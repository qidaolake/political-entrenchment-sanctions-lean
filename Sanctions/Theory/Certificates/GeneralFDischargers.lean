/-
Sanctions/Theory/Certificates/GeneralFDischargers.lean

**Certificate dischargers that do not require an affine transition.**

The legacy affine combined-chord discharger (`StandardComplianceLocal.lean`,
retired 2026-08-21) took
`hF : p.F = affineF p.δ` and opens with `simp only [hF, affineF]`. Affineness
enters it at exactly one place — the displacement identity
`F(x,s₂) − F(x,s₁) = δ·(s₂ − s₁)`, which converts the loss-offset margin into a
continuation gain. Everything else in that proof already runs on `F_mem`,
`F_diag` and `F_mono_s`.

This file replaces that identity by the sanction-side **lower chord**, which
supplies the same step as an inequality in the one direction the chain
consumes. The affine law satisfies it at equality with `dlo = δ`, so the
affine discharger is the `glo = ghi` instance rather than a separate route.

The direction is the whole risk here — a flipped sign compiles and is silently
wrong — so the chain is documented in the declaration's own docstring below.

**Round BH (2026-10-06).** The certificate theorems below now run through the
Sender persistence basin (`exists_equilibrium_senderPersistenceBasinTop_generalF`
and its Schur sibling) rather than the joint basin. Their statements are
unchanged; their proofs no longer read the Target loss-offset fields (`dlo`,
`hchord_lo`, `cT`, `gT`, `hgT_nn`, `hT_loss_margin`, `h_stage_target_loss_on`,
`hV_T_gain_on_carrier`), which only fed the Target-preference conjunct that every
caller discarded (BH1.5). Two siblings are new: the slim pathwise comparison
`pathwise_dominance_generalF` (BH1.4) and the fixed-start general regime
comparison `StandardComplianceLocalCertificate.three_goals_local_regime_comparison_generalF`
(BH1.7).

**Round BJ1.4 (2026-10-07, author-approved).** Those fields, and the floor
sign `hsbar_pos`, are now deleted from both certificates. The decomposition
discharger `Target_combined_chord_of_decomposition_lowerChord` below stays as a
standalone theorem, and the two joint-basin theorems
(`exists_equilibrium_basinTop_generalF` and its Schur sibling), the only ones
that still certify the Target-preference field, take the Target combined chord
as an explicit hypothesis.
-/

import Sanctions.Theory.Certificates.StandardComplianceLocal
import Sanctions.Theory.Basin.TransitionChords
import Sanctions.Theory.Certificates.StandardComplianceSchur
import Sanctions.Theory.Basin.SenderPersistence

namespace Sanctions

namespace AbstractGame

namespace Params

open Set Sanctions.TransitionChords

variable (p : Params)

/-- **General-`F` Target combined chord from the loss / gain decomposition.**

Affine-free replacement for the retired affine combined-chord discharger.  The affine
hypothesis `hF : p.F = affineF p.δ` is deleted; in its place the transition
enters only through the sanction **lower** chord at rate `dlo`, and the margin
is denominated in `dlo` rather than `δ`.

Reading the fields in English:

* `hchord` — raising the sanction by `Δ` raises next period's political state
  by at least `dlo·Δ`, uniformly on the feasible square (`SanctionLowerChord`);
* `cT` — the Target's worst stage loss rate per unit of extra sanction on the
  basin's high-sanction chord domain (`LowerLossSlopeOn`);
* `gT` — the Target value function's minimum upward state slope on the basin
  (`LowerSlopeOnValueOn`), assumed nonnegative;
* `hT_loss_margin` — `c_T ≤ β_T · g_T · dlo`: the stage loss rate is covered by
  the discounted continuation gain the extra sanction actually buys.

Conclusion `TargetCombinedChordOn D xT sbar`: for every carrier pair and every
basin state, the Target's *joint* dynamic payoff (stage plus discounted
continuation) is nondecreasing in the sanction on `[max(x, s̄), 1]`.

Setting `p.F = affineF p.δ` and `dlo = δ` recovers the affine statement, since
`affine_sanctionLowerChord` discharges `hchord` at equality. -/
theorem Target_combined_chord_of_decomposition_lowerChord
    {D : p.ValueClass2}
    {xT sbar : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    {dlo cT gT : ℝ}
    (hchord : SanctionLowerChord p.F dlo)
    (hgT_nn : 0 ≤ gT)
    (hT_loss_margin : cT ≤ p.β_T * gT * dlo)
    (h_stage_target_loss_on :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc xT (1 : ℝ),
          LowerLossSlopeOn (fun s => p.U_T x (D.α_on V_T V_S x) s)
            (Set.Icc (max x sbar) 1) cT)
    (hV_T_gain_on_carrier :
      ∀ V_T ∈ D.carrier_T, LowerSlopeOnValueOn V_T (Set.Icc xT 1) gT) :
    p.TargetCombinedChordOn D xT sbar := by
  intro V_T V_S x hx s₁ hs₁ s₂ hs₂ hs_le
  -- Geometry, all of it general: `F_mem`, `F_diag`, `F_mono_s` only.
  have hβT_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have hxT_nn : 0 ≤ xT := hxT_mem.1
  have hx_lo : 0 ≤ x := le_trans hxT_nn hx.1
  have hx_hi : x ≤ 1 := hx.2
  have hs₁_ge_x : x ≤ s₁ := le_trans (le_max_left _ _) hs₁.1
  have hs₂_ge_x : x ≤ s₂ := le_trans (le_max_left _ _) hs₂.1
  have hx_I : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx_lo, hx_hi⟩
  have hs₁_I : s₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hx_lo hs₁_ge_x, hs₁.2⟩
  have hs₂_I : s₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hx_lo hs₂_ge_x, hs₂.2⟩
  have hF1_mem : p.F x s₁ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem x s₁ hx_I hs₁_I
  have hF2_mem : p.F x s₂ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem x s₂ hx_I hs₂_I
  -- `F(x, s) ≥ F(x, x) = x ≥ xT` for `s ≥ x`: the basin cannot be left.
  have hF1_ge_x : x ≤ p.F x s₁ := by
    have h : p.F x x ≤ p.F x s₁ := p.F_mono_s x hs₁_ge_x
    rwa [p.F_diag x] at h
  have hF2_ge_x : x ≤ p.F x s₂ := by
    have h : p.F x x ≤ p.F x s₂ := p.F_mono_s x hs₂_ge_x
    rwa [p.F_diag x] at h
  have hF12 : p.F x s₁ ≤ p.F x s₂ := p.F_mono_s x hs_le
  -- `clipS'` is the identity on `[0,1]`.
  have hclip1_val : (Sanctions.clipS' (p.F x s₁)).val = p.F x s₁ := by
    show Sanctions.clipS (p.F x s₁) = p.F x s₁
    unfold Sanctions.clipS
    rw [min_eq_right hF1_mem.2, max_eq_right hF1_mem.1]
  have hclip2_val : (Sanctions.clipS' (p.F x s₂)).val = p.F x s₂ := by
    show Sanctions.clipS (p.F x s₂) = p.F x s₂
    unfold Sanctions.clipS
    rw [min_eq_right hF2_mem.2, max_eq_right hF2_mem.1]
  have hclip1_mem : (Sanctions.clipS' (p.F x s₁)).val ∈ Set.Icc xT 1 := by
    rw [hclip1_val]; exact ⟨le_trans hx.1 hF1_ge_x, hF1_mem.2⟩
  have hclip2_mem : (Sanctions.clipS' (p.F x s₂)).val ∈ Set.Icc xT 1 := by
    rw [hclip2_val]; exact ⟨le_trans hx.1 hF2_ge_x, hF2_mem.2⟩
  have hclip12 : Sanctions.clipS' (p.F x s₁) ≤ Sanctions.clipS' (p.F x s₂) :=
    Sanctions.clipS'_mono hF12
  -- Stage chord: `stage(s₂) − stage(s₁) ≥ −c_T·(s₂ − s₁)`.
  have h_stage_chord :=
    h_stage_target_loss_on V_T V_S x hx s₁ hs₁ s₂ hs₂ hs_le
  -- Value chord: `g_T · dist ≤ V_T(y₂) − V_T(y₁)`.
  have h_val_chord :=
    hV_T_gain_on_carrier V_T.val V_T.property
      (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
      hclip1_mem hclip2_mem hclip12
  have h_dist :
      dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
        = p.F x s₂ - p.F x s₁ := by
    rw [Subtype.dist_eq, Real.dist_eq, hclip1_val, hclip2_val, abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  rw [h_dist] at h_val_chord
  -- **The one replaced step**: the affine displacement identity becomes the
  -- lower-chord inequality.
  have hchord' : dlo * (s₂ - s₁) ≤ p.F x s₂ - p.F x s₁ :=
    hchord hx_I hs₁_I hs₂_I hs_le
  have h_diff_nn : 0 ≤ s₂ - s₁ := by linarith
  have h_margin_chord : cT * (s₂ - s₁) ≤ p.β_T * gT * dlo * (s₂ - s₁) :=
    mul_le_mul_of_nonneg_right hT_loss_margin h_diff_nn
  have h_gain_lb : gT * (dlo * (s₂ - s₁)) ≤ gT * (p.F x s₂ - p.F x s₁) :=
    mul_le_mul_of_nonneg_left hchord' hgT_nn
  have h_gain_scaled :
      p.β_T * (gT * (dlo * (s₂ - s₁)))
        ≤ p.β_T * (gT * (p.F x s₂ - p.F x s₁)) :=
    mul_le_mul_of_nonneg_left h_gain_lb hβT_nn
  have h_translate :
      p.β_T * gT * dlo * (s₂ - s₁) = p.β_T * (gT * (dlo * (s₂ - s₁))) := by
    ring
  have h_val_scaled :
      p.β_T * (gT * (p.F x s₂ - p.F x s₁))
        ≤ p.β_T * (V_T.val (Sanctions.clipS' (p.F x s₂))
                    - V_T.val (Sanctions.clipS' (p.F x s₁))) :=
    mul_le_mul_of_nonneg_left h_val_chord hβT_nn
  linarith

/-! ## G3 — the general-`F` Goal-2 route

`three_goals_local_uniform_starts` consumes `hF : p.F = affineF p.delta`, but its
**Goal 2** — statewise dominance of the forward-looking realised sanction over
the myopic one — mentions no transition at all: `dynamicTopRealizedRule` is
`sigma_dyn_top V_S x (alpha x)`, and `sigma x (M.alpha x)` is a stage object. The
affine hypothesis enters only through the *route*, at the one-sided threshold
constructor.

This theorem takes the other route. Every link already existed; the only thing
missing was the composition:

* `Target_combined_chord_of_decomposition_lowerChord` (above) — Target leg on a
  sanction **lower** chord at rate `dlo` instead of the affine displacement;
* `TargetCombinedChordOn.at_equilibrium` — carrier-quantified chord read at the
  constructed equilibrium pair;
* the G1 threshold constructor
  `..._of_stage_lowerSlope_sender_and_target_combined_chord_generalF` — Sender
  leg on a range-restricted **upper** chord at rate `d`;
* `JointPreferenceBasinTop.of_oneSidedThresholds` then `level_dyn_top` — the
  basin floor `max x sbar <= dynamicTopRealizedRule`;
* `ruleDom_of_dynamic_floor_and_myopic_ceiling` — floor meets the certificate's
  myopic ceiling.

**Why two rates and not one.** A single two-sided chord at one rate is *not* a
generalisation: `SanctionLowerChord F d` together with `SanctionUpperChord F d`
forces `F x s2 - F x s1 = d * (s2 - s1)` exactly, and with `F_diag` that pins
`F = affineF d`. The generality is real only because the Target leg consumes a
lower rate `dlo` and the Sender leg an upper rate `d`, with `dlo < d` for any
non-affine member and the two margins denominated separately.

**Why `0 <= gT` appears here and not in the affine sibling.** The transition
enters the Target leg as the *inequality* `dlo * (s2 - s1) <= F x s2 - F x s1`,
and scaling an inequality by `gT` reverses it when `gT < 0`. Under the affine law
that step is an equality, so the sign cannot matter. Generality in `F` is exactly
what makes the sign of the continuation-gain rate load-bearing.

**Affine recovery (Rule 5).** At `dlo = d = p.delta` the two chords are
discharged by `affine_sanctionLowerChord` and `affine_sender_chord_on`, and the
two margin hypotheses are the loss-offset margin and the certificate's own
`hS_margin` field — so every existing affine witness re-routes with no change
to its own statement.

**Round BJ1.4 (2026-10-07).** The certificates no longer carry the Target leg
(`dlo`, the lower chord, the loss and gain rates and their margin): since round
BH1.5 the goals run through the Sender persistence basin, which reads only the
Sender leg. The Target leg survives as the explicit combined-chord hypothesis
of the joint-basin theorems below. -/

namespace StandardComplianceLocalCoreCertificate

/-- **The general-`F` route's one shared step: certificate ⇒ equilibrium in the
joint preference basin.**

All three goals need exactly the same object — an equilibrium whose two value
functions lie in the certificate's carriers, sitting in a
`JointPreferenceBasinTop` over the basin `[max xT xS, 1]` at the certificate's
own sanction floor `sbar`. Each goal then reads a different consequence off it:
Goal 1 the state-path invariance, Goal 2 the dominance of the dynamic realised
sanction over the myopic one, Goal 3 the post-shock long run.

Factoring it here is what keeps the transition's entry point in **one** place.
`F` enters any of the three only through the Sender's range-restricted sanction
upper chord at rate `d` and through the Target combined chord `h_combined_on`
(until round BJ1.4 the latter was built here from a sanction lower chord at rate
`dlo` carried by the certificate). Nothing downstream sees `F` again.

Note the basin is built at `C.sbar`, not at `max xT xS`. That matters: routing
Goal 3 through `GeneralFPersistencePackage` instead would pin the floor to
`max xT xS` and silently discard the certificate's free `sbar`, which is the
quantified regression recorded against the MS route.

Since round BH1.5 (2026-10-06) the goal theorems below read the Sender
persistence basin (`exists_equilibrium_senderPersistenceBasinTop_generalF`)
instead, which needs none of the Target loss-offset fields. This joint-basin
form is kept: it additionally certifies the Target-preference field.

Round BJ1.4 (2026-10-07): the certificate no longer carries the Target
loss-offset stack, so the Target combined chord on the carriers (P4) is taken
as the explicit hypothesis `h_combined_on`, the weakest form the proof reads.
The former fields give it through
`Target_combined_chord_of_decomposition_lowerChord` (a sanction lower chord at
rate `dlo`, the loss and gain rates and the margin `cT ≤ β_T · gT · dlo`), so
every former instance is still covered. General in `F`: the transition enters
only through the Sender chord at rate `d` and through `h_combined_on`. -/
theorem exists_equilibrium_basinTop_generalF
    (C : p.StandardComplianceLocalCoreCertificate)
    (h_combined_on : p.TargetCombinedChordOn C.D C.xT C.sbar) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ p.JointPreferenceBasinTop E.V_T E.V_S E.α (max C.xT C.xS) C.sbar := by
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    C.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership
      C.h_inv C.hβ_T_nn C.hβ_S_nn C.hL_TS_nn C.hL_ST_nn
      C.hT_T_op C.hT_S_op C.hsuff_T C.hsuff_S
  let V_T_sub : C.D.CarrierT := ⟨E.V_T, hVT⟩
  let V_S_sub : C.D.CarrierS := ⟨E.V_S, hVS⟩
  change E.α = C.D.α_on V_T_sub V_S_sub at hα_eq
  -- Target leg: the carrier combined chord, read at the equilibrium.
  have h_target_combined :=
    TargetCombinedChordOn.at_equilibrium p h_combined_on E hVT hVS hα_eq
  -- Sender leg: carrier Lipschitz + stage slope at the equilibrium.
  have hV_S_lip : ValueLipschitzWith E.V_S C.KS :=
    C.hV_S_lip_carrier E.V_S hVS
  have h_stage_sender :
      ∀ x ∈ Set.Icc C.xS (1 : ℝ),
        LowerSlopeOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x C.sbar)) C.mS := by
    intro x hx
    rw [hα_eq]
    exact C.h_stage_sender_on V_T_sub V_S_sub x hx
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α C.xT C.xS C.sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_lowerSlope_sender_and_target_combined_chord_generalF
      p C.hxT_mem C.hxS_mem C.hsbar_mem C.hKS_nonneg C.hS_margin hV_S_lip
      C.hF_chord h_target_combined h_stage_sender
  have hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max C.xT C.xS) 1)
        (fun s x => p.senderDynObjective E.V_S x (E.α x) s) := by
    have h := C.hIDO_on V_T_sub V_S_sub
    convert h using 2
    rw [hα_eq]
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max C.xT C.xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO
  have hα_feas : ∀ x ∈ Set.Icc (max C.xT C.xS) 1, E.α x ∈ Sanctions.I := by
    intro x hx
    exact E.α_mem x ⟨le_trans (le_max_of_le_left C.hxT_mem.1) hx.1, hx.2⟩
  have hα_opt : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
      IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S x a)
        Sanctions.I (E.α x) := by
    intro x hx
    exact E.α_opt_top x ⟨le_trans (le_max_of_le_left C.hxT_mem.1) hx.1, hx.2⟩
  exact ⟨E, hVT, hVS,
    JointPreferenceBasinTop.of_oneSidedThresholds p hOne hα_feas hTopMono hα_opt⟩

/-- **Certificate ⇒ equilibrium in the Sender persistence basin (round BH1.5,
2026-10-06).**

The same equilibrium as `exists_equilibrium_basinTop_generalF` (row-sum
existence, values in the certificate's carriers), placed in the P4-free
`SenderPersistenceBasinTop` over `[max xT xS, 1]` at the certificate's own floor
`sbar` instead of the joint basin. The Target loss-offset stack (`dlo`,
`hchord_lo`, `cT`, `gT`, `hgT_nn`, `hT_loss_margin`, `h_stage_target_loss_on`,
`hV_T_gain_on_carrier`) was not read: in the joint basin it fed only the
Target-preference field, whose conclusion every certificate theorem discarded.
Round BJ1.4 (2026-10-07) then deleted the stack from the certificate.
The level input is the Sender leg alone (stage slope `mS`, carrier Lipschitz
bound `KS`, the range-restricted upper chord at rate `d` and the margin
`β_S·KS·d < mS`); the direction input is the interval-dominance field.

Plain language: given the Target's equilibrium policy, the Sender's own
incentives keep the sanction at or above the floor and make it rise with the
state; how the Target ranks sanction levels plays no part. Every theorem below
that reads basin persistence, the floor or dominance reads it from this object.
General in `F`: the transition enters only through the chord at rate `d`. -/
theorem exists_equilibrium_senderPersistenceBasinTop_generalF
    (C : p.StandardComplianceLocalCoreCertificate) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ p.SenderPersistenceBasinTop E.V_S E.α (max C.xT C.xS) C.sbar := by
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    C.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership
      C.h_inv C.hβ_T_nn C.hβ_S_nn C.hL_TS_nn C.hL_ST_nn
      C.hT_T_op C.hT_S_op C.hsuff_T C.hsuff_S
  let V_T_sub : C.D.CarrierT := ⟨E.V_T, hVT⟩
  let V_S_sub : C.D.CarrierS := ⟨E.V_S, hVS⟩
  change E.α = C.D.α_on V_T_sub V_S_sub at hα_eq
  have hV_S_lip : ValueLipschitzWith E.V_S C.KS := C.hV_S_lip_carrier E.V_S hVS
  have hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max C.xT C.xS) 1)
        (fun s x => p.senderDynObjective E.V_S x (E.α x) s) := by
    have h := C.hIDO_on V_T_sub V_S_sub
    convert h using 2
    rw [hα_eq]
  refine ⟨E, hVT, hVS, SenderPersistenceBasinTop.of_sender_dynamic_margin p
    (le_trans C.hxT_mem.1 (le_max_left _ _)) C.hsbar_mem ?_ hIDO⟩
  -- Level: the Sender leg on the basin, which sits inside `[xS, 1]`.
  intro x hx
  have hxS : x ∈ Set.Icc C.xS (1 : ℝ) := ⟨le_trans (le_max_right _ _) hx.1, hx.2⟩
  have h_stage :
      LowerSlopeOn (fun s => p.U_S x (E.α x) s)
        (Set.Icc (0 : ℝ) (max x C.sbar)) C.mS := by
    rw [hα_eq]
    exact C.h_stage_sender_on V_T_sub V_S_sub x hxS
  exact p.senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz
    (p.sender_transition_adjusted_chord_of_upperChordOn_lowerSlope
      C.hKS_nonneg (C.hF_chord x hxS) C.hS_margin h_stage)
    hV_S_lip

/-- **Goal 2 (statewise dynamic-over-myopic dominance) without an affine
transition.** Same certificate, same conclusion, no `hF`: the transition enters
only through the range-restricted sanction upper chord at rate `d` (Sender
leg), with the margin denominated in that rate.

Since round BH1.5 (2026-10-06) the proof runs through the Sender persistence
basin (`exists_equilibrium_senderPersistenceBasinTop_generalF`), so the Target
lower chord at rate `dlo` and the rest of the Target loss-offset stack were no
longer read; round BJ1.4 (2026-10-07) deleted them from the certificate. The
statement is unchanged. -/
theorem goal2_dominance_generalF
    (C : p.StandardComplianceLocalCoreCertificate) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x) := by
  obtain ⟨E, hVT, hVS, hB⟩ :=
    C.exists_equilibrium_senderPersistenceBasinTop_generalF p
  have hFloor := SenderPersistenceBasinTop.level_dyn_top p hB
  exact ⟨E, hVT, hVS,
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling⟩

/-- **Goal 3 (temporary shock ⇒ permanent high sanctions) without an affine
transition.** Same certificate, same Sender chord rate `d`, and `hF` replaced by
`hAdj : p.StrictAdjustment` — the paper's *ordinal* transition condition, that
a sanction below the inherited state erodes entrenchment and one above it
builds entrenchment.

**That swap is a weakening, not a widening.** `strictAdjustment_of_F_eq_affineF`
derives `hAdj` from `hF` together with `Params`' own `δ ∈ (0,1)`, so `hF`
implies `hAdj` and the converse fails. The general route therefore rests on
strictly less than the affine one.

The shock horizon is the paper's conservative general-`F` ceiling
`fullShockEntryHorizon (max xT xS) = ⌈x̄ / η_F(x̄)⌉`, with `η_F` the minimum
full-sanction drift below the pivot. It is weaker than the affine closed form
`⌈log(1−x̄)/log(1−δ)⌉` — but the conclusion is existentially quantified over the
horizon, so the loss is invisible here. It is visible only in
`shockEntryHorizon_bound`, which states the sharp constant and is affine **by
nature**; that theorem stays affine and should.

Since round BH1.5 (2026-10-06) the proof runs through the Sender persistence
basin, so the Target loss-offset fields were no longer read (round BJ1.4 deleted
them from the certificate). The statement is unchanged. -/
theorem goal3_shock_generalF
    (C : p.StandardComplianceLocalCoreCertificate)
    (hAdj : p.StrictAdjustment) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ ∃ N : ℕ, ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀shock N) n ∈ Set.Icc (max C.xT C.xS) 1)
          ∧ (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N) n)
          ∧ (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N) n)
          ∧ Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N)) := by
  obtain ⟨E, hVT, hVS, hB⟩ :=
    C.exists_equilibrium_senderPersistenceBasinTop_generalF p
  have hxbar : max C.xT C.xS ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨le_trans C.hxT_mem.1 (le_max_left _ _), C.hjoint_lt⟩
  refine ⟨E, hVT, hVS, p.fullShockEntryHorizon (max C.xT C.xS), ?_⟩
  intro x₀shock hx₀shock
  have hentry :
      p.shockPathF x₀shock (p.fullShockEntryHorizon (max C.xT C.xS))
        ∈ Set.Icc (max C.xT C.xS) 1 :=
    p.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment
      hAdj hxbar x₀shock hx₀shock _ (le_refl _)
  obtain ⟨hpath, hfloor, hxbar_le, hmono, -, -, -⟩ :=
    p.equilibriumTop_senderPersistenceF_long_run_with_evidence E hB hentry
  exact ⟨hpath, hfloor, hxbar_le, hmono⟩

/-- **The three goals, from one certificate, with no affine transition.**

This is the general-`F` counterpart of the certificate route's headline. One
equilibrium, its two value functions in the certificate's carriers, and:

1. **persistence** — from every start in the high political basin
   `[max xT xS, 1]` the equilibrium state path never leaves it;
2. **dominance** — in every basin state the myopic realised sanction lies at or
   below the forward-looking one;
3. **hysteresis** — there is a finite shock duration `N` such that after a
   temporary maximum-sanction phase of that length, from *any* feasible start,
   the economy is in the basin and stays there with sanctions above the floor
   `sbar` and non-decreasing forever after.

Every path object is the general-`F` one (`dynamicTopLockInPathF`,
`dynamicTopLockInSanctionsF`, `shockPathF`). The transition enters in exactly
two places, both of them ordinal or chord conditions on `p.F`: the Sender chord
rate `d` and `hAdj`. (Until round BJ1.4 the certificate also carried a Target
lower chord at rate `dlo`, which no goal read.) **No `hF` anywhere.**

Because all three read off the single
`exists_equilibrium_senderPersistenceBasinTop_generalF` object, they are
conclusions about *the same* equilibrium — not three separately constructed
ones. Since round BH1.5 (2026-10-06) that object is the Sender persistence
basin, so the Target loss-offset fields were not read (round BJ1.4 deleted them
from the certificate); the statement is unchanged. -/
theorem three_goals_generalF
    (C : p.StandardComplianceLocalCoreCertificate)
    (hAdj : p.StrictAdjustment) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      -- Goal 1: basin persistence.
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
           ∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1)
      -- Goal 2: dynamic dominates myopic.
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      -- Goal 3: temporary shock ⇒ permanent high sanctions.
      ∧ ∃ N : ℕ, ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀shock N) n ∈ Set.Icc (max C.xT C.xS) 1)
          ∧ (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N) n)
          ∧ (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N) n)
          ∧ Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock N)) := by
  obtain ⟨E, hVT, hVS, hB⟩ :=
    C.exists_equilibrium_senderPersistenceBasinTop_generalF p
  have hFloor := SenderPersistenceBasinTop.level_dyn_top p hB
  have hxbar : max C.xT C.xS ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨le_trans C.hxT_mem.1 (le_max_left _ _), C.hjoint_lt⟩
  refine ⟨E, hVT, hVS,
    fun x₀ hx₀ => p.dynamicTopLockInPathF_mem_basin E.V_S E.α hFloor hx₀,
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling,
    p.fullShockEntryHorizon (max C.xT C.xS), ?_⟩
  intro x₀shock hx₀shock
  have hentry :
      p.shockPathF x₀shock (p.fullShockEntryHorizon (max C.xT C.xS))
        ∈ Set.Icc (max C.xT C.xS) 1 :=
    p.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment
      hAdj hxbar x₀shock hx₀shock _ (le_refl _)
  obtain ⟨hpath, hfloor, hxbar_le, hmono, -, -, -⟩ :=
    p.equilibriumTop_senderPersistenceF_long_run_with_evidence E hB hentry
  exact ⟨hpath, hfloor, hxbar_le, hmono⟩

/-! ### The full-strength conclusion set, without an affine transition

`three_goals_generalF` above reads only *one* of the eight conjuncts that
`jointPreferenceBasinTopF_long_run_with_equilibrium_evidence` delivers on the
Goal-1 leg, so its persistence conclusion is weaker than the legacy affine
route's — it asserts that the state path stays in the basin, but drops the free
sanction floor `s̄`, the `max xT xS` floor, sanction monotonicity, and the
per-period Target-argmax certificate.

That gap was recorded as a *quantified regression* of the general-`F` route
(`AFFINE-REMOVAL-IMPACT.md` §4c): at `eeCertParams` the legacy route certifies a
sanction floor of `1/2` on the basin `[1/10, 1]` where the general route
certifies only `1/10` — five times weaker on the identical basin.

It was never a limitation of general `F`. All four missing conjuncts are already
proved at full generality over `dynamicTopLockInPathF` / `...SanctionsF`; the
composition was simply absent, the same finding commit `5251447` recorded for
Goal 2 and the previous round recorded for Goal 1. The theorem below closes it:
it is `three_goals_local_uniform_starts` conjunct for conjunct, with every
trajectory object replaced by its general-`F` sibling and `hF` replaced by the
paper's ordinal transition condition. -/

/-- **All three goals at full conclusion strength, general in `F`.**

Matches `StandardComplianceLocalCoreCertificate.three_goals_local_uniform_starts`
conjunct for conjunct — the strongest statement the certificate supports — with
two differences and no third:

* every trajectory object is the general-`F` one (`dynamicTopLockInPathF`,
  `dynamicTopLockInSanctionsF`, `shockPathF`) rather than the hand-written
  affine one, so at a non-affine economy the conclusion describes the state law
  the model actually has;
* `hF : p.F = affineF p.δ` is replaced by `hAdj : p.StrictAdjustment` — the
  paper's *ordinal* transition condition, that a sanction below the inherited
  state erodes entrenchment and one above it builds entrenchment.

**The swap is a weakening, not a widening.** `strictAdjustment_of_F_eq_affineF`
derives `hAdj` from `hF` together with `Params`' own `δ ∈ (0,1)`, and the
converse fails — the non-affine witnesses satisfy `hAdj` and not `hF`. The
transition otherwise enters only through the certificate's Sender chord rate
`d` (an extra unit of sanction raises next period's state by at most `d`); the
Target-leg rate `dlo` was deleted from the certificate in round BJ1.4.

Reading the conclusions in English, for every start `x₀` in the joint basin:

* **Goal 1 (persistence, five conjuncts)** — the equilibrium state path never
  leaves the basin; realised sanctions never fall below the certificate's own
  floor `s̄`; they never fall below the basin pivot `max xT xS`; they are
  monotone in time; and at every date the Target's action is a maximiser of its
  own joint dynamic objective, so the path is equilibrium-generated at every
  period rather than only at date 0 (Rule 1).
* **Goal 2 (dominance)** — statewise on the basin, the dynamic Sender's realised
  sanction weakly exceeds the myopic Sender's.
* **Goal 3 (hysteresis)** — after any temporary full-sanction shock from any
  admissible start, there is a finite entry horizon after which Goal 1's basin
  membership and both sanction floors hold forever.

The price of generality is confined to the shock horizon: `N` here is the
conservative general-`F` ceiling `⌈x̄ / η_F(x̄)⌉` rather than the affine closed
form `⌈log(1−x̄)/log(1−δ)⌉`. The conclusion existentially quantifies `N`, so the
loss is invisible in this statement; it is visible only in
`shockEntryHorizon_bound`, which states the sharp constant and is affine **by
nature**. That theorem stays affine and should.

Since round BH1.5 (2026-10-06) the proof runs through the Sender persistence
basin and reads all five Goal-1 conjuncts off
`equilibriumTop_senderPersistenceF_long_run_with_evidence`; the Target
loss-offset fields were no longer read (round BJ1.4 deleted them from the
certificate). The statement is unchanged. -/
theorem three_goals_local_uniform_starts_generalF
    (C : p.StandardComplianceLocalCoreCertificate)
    (hAdj : p.StrictAdjustment) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                            (p.shockPathF x₀shock N) n) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀shock N) n)) := by
  obtain ⟨E, hVT, hVS, hB⟩ :=
    C.exists_equilibrium_senderPersistenceBasinTop_generalF p
  have hFloor := SenderPersistenceBasinTop.level_dyn_top p hB
  have hxbar : max C.xT C.xS ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨le_trans C.hxT_mem.1 (le_max_left _ _), C.hjoint_lt⟩
  refine ⟨E, hVT, hVS, ?_,
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling, ?_⟩
  · -- Goal 1: all five conjuncts off the same long-run evidence bundle.
    intro x₀ hx₀
    obtain ⟨hpath, hfloor, hxbar_le, hmono, -, hargmax, -⟩ :=
      p.equilibriumTop_senderPersistenceF_long_run_with_evidence E hB hx₀
    exact ⟨hpath, hfloor, hxbar_le, hmono, hargmax⟩
  · -- Goal 3: enter the basin in finite time, then re-read Goal 1 there.
    intro x₀shock h0 h1
    refine ⟨p.fullShockEntryHorizon (max C.xT C.xS), ?_⟩
    have hentry :
        p.shockPathF x₀shock (p.fullShockEntryHorizon (max C.xT C.xS))
          ∈ Set.Icc (max C.xT C.xS) 1 :=
      p.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment
        hAdj hxbar x₀shock ⟨h0, h1⟩ _ (le_refl _)
    obtain ⟨hpath, hfloor, hxbar_le, -, -, -, -⟩ :=
      p.equilibriumTop_senderPersistenceF_long_run_with_evidence E hB hentry
    exact ⟨hpath, hfloor, hxbar_le⟩

/-! ### The remaining certificate routes, general in `F` (2026-08-21)

`three_goals_local_uniform_starts_generalF` above covers the start-free core
certificate. Four affine routes remained, at six call sites of the affine
threshold constructor, and all four are *replaceable now* — their certificates
already carry `d` and `hF_chord` (and, until round BJ1.4, `dlo`, `hchord_lo` and
`hgT_nn`), so no hypothesis is added anywhere below.

They could not be de-affined **in place**: each also consumes
`persistence_at_equilibriumTop_from_lossOffset_on` and
`shock_at_equilibriumTop_from_lossOffset_on`, which carry `hF` and run over the
hard-coded affine trajectory objects, and `StandardComplianceLocal.lean` is
imported *by* this file. So the general form is a sibling here rather than an
edit there — the affine statements keep their `hF`, which under Rule 22 is
exactly how an affine-restricted result should be marked.

Since round BH1.7 (2026-10-06) the direction is reversed: the affine
statements in `Examples/AffineInstance/ComplianceTower.lean` are proved as
instances of the general ones here (`hF` gives `hAdj`, and the affine trajectory
objects equal the general-`F` ones under `hF`), with their statements and `hF`
binders unchanged. -/

/-- **Goal-1/2/3 at the certificate's own stored start, general in `F`.**
The fixed-start sibling of `three_goals_local_generalF`'s uniform version: same
conclusions read at `C.x₀` and `C.x₀shock` rather than quantified. -/
theorem three_goals_local_generalF
    (C : p.StandardComplianceLocalCertificate)
    (hAdj : p.StrictAdjustment) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ ((∀ n, p.dynamicTopLockInPathF E.V_S E.α C.x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
         (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α C.x₀ n) ∧
         (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α C.x₀ n) ∧
         Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α C.x₀) ∧
         (∀ n, IsMaxOn
           (fun a => p.joint_T_top_integrand E.V_T E.V_S
                       (p.dynamicTopLockInPathF E.V_S E.α C.x₀ n) a)
           Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF C.x₀shock N) n ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                          (p.shockPathF C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                  (p.shockPathF C.x₀shock N) n) := by
  obtain ⟨E, hVT, hVS, hG1, hG2, hG3⟩ :=
    C.toStandardComplianceLocalCoreCertificate.three_goals_local_uniform_starts_generalF
      p hAdj
  exact ⟨E, hVT, hVS, hG1 C.x₀ C.hx₀, hG2,
    hG3 C.x₀shock C.hx₀shock_nn C.hx₀shock_le⟩

/-- **Regime comparison, general in `F`.** Adds to the three goals a *pathwise*
Sender-regime comparison: from every basin start, the myopic equilibrium's
realised sanction is weakly below the dynamic equilibrium's at **every** date,
not merely statewise. `hMyoBasin` — that the myopic realised rule keeps the
state in the basin — is the same hypothesis the affine route takes, and is what
makes the path comparison well-posed.

Both trajectory families are the general-`F` ones (`ruleSanctionsF`). Since
round BH1.5 (2026-10-06) the proof runs through the Sender persistence basin, so
the transition enters only through the Sender chord at rate `d` and `hAdj`, and
the Target loss-offset fields were no longer read (round BJ1.4 deleted them from
the certificate). The statement is unchanged.
`pathwise_dominance_generalF` below states the two comparisons alone, without
`hAdj`. -/
theorem three_goals_local_regime_comparison_uniform_starts_generalF
    (C : p.StandardComplianceLocalCoreCertificate)
    (hAdj : p.StrictAdjustment)
    (hMyoBasin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.myopicEquilibriumRule C.M x ∈ Set.Icc (max C.xT C.xS) 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.myopicEquilibriumRule C.M x ≤ p.dynamicEquilibriumRule E x)
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
           ∀ n, p.ruleSanctionsF (p.myopicEquilibriumRule C.M) x₀ n
                  ≤ p.ruleSanctionsF (p.dynamicEquilibriumRule E) x₀ n)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                            (p.shockPathF x₀shock N) n) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀shock N) n)) := by
  obtain ⟨E, hVT, hVS, hB⟩ := C.exists_equilibrium_senderPersistenceBasinTop_generalF p
  have hFloor := SenderPersistenceBasinTop.level_dyn_top p hB
  have hDynMono := hB.top_rule_mono
  have hG2 := p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling
  have hDyn_basin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.dynamicTopRealizedRule E.V_S E.α x ∈ Set.Icc (max C.xT C.xS) 1 := by
    intro x hx
    exact ⟨le_trans hx.1 (le_trans (le_max_left _ _) (hFloor x hx)),
      (p.σ_dyn_top_mem_I E.V_S x (E.α x)).2⟩
  refine ⟨E, hVT, hVS, ?_, hG2, ?_, ?_⟩
  · intro x₀ hx₀
    obtain ⟨hpath, hfloor, hxbar_le, hmono, -, hargmax, -⟩ :=
      p.equilibriumTop_senderPersistenceF_long_run_with_evidence E hB hx₀
    exact ⟨hpath, hfloor, hxbar_le, hmono, hargmax⟩
  · intro x₀ hx₀
    exact p.ruleSanctionsF_le_of_rule_le_and_upper_monoOn_basin
      hMyoBasin hDyn_basin hDynMono hG2 hx₀
  · intro x₀shock h0 h1
    have hxbar : max C.xT C.xS ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨le_trans C.hxT_mem.1 (le_max_left _ _), C.hjoint_lt⟩
    refine ⟨p.fullShockEntryHorizon (max C.xT C.xS), ?_⟩
    have hentry :
        p.shockPathF x₀shock (p.fullShockEntryHorizon (max C.xT C.xS))
          ∈ Set.Icc (max C.xT C.xS) 1 :=
      p.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment
        hAdj hxbar x₀shock ⟨h0, h1⟩ _ (le_refl _)
    obtain ⟨hpath, hfloor, hxbar_le, -, -, -, -⟩ :=
      p.equilibriumTop_senderPersistenceF_long_run_with_evidence E hB hentry
    exact ⟨hpath, hfloor, hxbar_le⟩

/-- **Pathwise dominance, general in `F` (round BH1.4, 2026-10-06).** From the
core certificate and myopic basin preservation alone: there is an equilibrium
with values in the certificate's carriers such that

* **statewise**, at every basin state the myopic equilibrium's realised
  sanction is weakly below the forward-looking equilibrium's;
* **pathwise**, from *every* common basin start `x₀`, the myopic regime's
  sanction path lies weakly below the forward-looking regime's at every date,
  both paths evolved by the general transition (`ruleSanctionsF`).

Compared with the affine fixed-start root
`standardCompliance_three_goals_local_regime_comparison`, three things are
dropped: `hF : p.F = affineF p.δ`, the fixed start `C.x₀` (the comparison now
holds uniformly over the basin), and the persistence and shock goals together
with their `hAdj`. The proof is the comparison half of
`three_goals_local_regime_comparison_uniform_starts_generalF`, run on the
Sender persistence basin, so it never needed the Target loss-offset fields
(deleted from the certificate in round BJ1.4).
`hMyoBasin` stays: the certificate's myopic ceiling holds only on the basin, and
the comparator needs the myopic path to remain there.

Plain language: wherever the two regimes start inside the high basin, the
forward-looking Sender sanctions at least as hard as the myopic one in every
period. General in `F`: the transition enters only through the certificate's
Sender chord at rate `d`. -/
theorem pathwise_dominance_generalF
    (C : p.StandardComplianceLocalCoreCertificate)
    (hMyoBasin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.myopicEquilibriumRule C.M x ∈ Set.Icc (max C.xT C.xS) 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.myopicEquilibriumRule C.M x ≤ p.dynamicEquilibriumRule E x)
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
           ∀ n, p.ruleSanctionsF (p.myopicEquilibriumRule C.M) x₀ n
                  ≤ p.ruleSanctionsF (p.dynamicEquilibriumRule E) x₀ n) := by
  obtain ⟨E, hVT, hVS, hB⟩ := C.exists_equilibrium_senderPersistenceBasinTop_generalF p
  have hFloor := SenderPersistenceBasinTop.level_dyn_top p hB
  have hDynMono := hB.top_rule_mono
  have hG2 := p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling
  have hDyn_basin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.dynamicTopRealizedRule E.V_S E.α x ∈ Set.Icc (max C.xT C.xS) 1 := by
    intro x hx
    exact ⟨le_trans hx.1 (le_trans (le_max_left _ _) (hFloor x hx)),
      (p.σ_dyn_top_mem_I E.V_S x (E.α x)).2⟩
  refine ⟨E, hVT, hVS, hG2, ?_⟩
  intro x₀ hx₀
  exact p.ruleSanctionsF_le_of_rule_le_and_upper_monoOn_basin
    hMyoBasin hDyn_basin hDynMono hG2 hx₀

end StandardComplianceLocalCoreCertificate

namespace StandardComplianceLocalCertificate

open StandardComplianceLocalCoreCertificate in
/-- **Regime comparison at the certificate's stored start, general in `F`
(round BH1.7, 2026-10-06).** The fixed-start sibling of
`three_goals_local_regime_comparison_uniform_starts_generalF`: the same five
persistence conjuncts, statewise and pathwise regime comparisons, and shock
conclusions, read at `C.x₀` and `C.x₀shock` instead of quantified. It is the
general-`F` form of the affine `three_goals_local_regime_comparison`
(`Examples/AffineInstance/ComplianceTower.lean`), with every trajectory object
the general-`F` one and `hF` replaced by `hAdj : p.StrictAdjustment`, which
`hF` implies (`strictAdjustment_of_F_eq_affineF`). No hypothesis is added; the
affine theorem is now its instance. General in `F`. -/
theorem three_goals_local_regime_comparison_generalF
    (C : p.StandardComplianceLocalCertificate)
    (hAdj : p.StrictAdjustment)
    (hMyoBasin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.myopicEquilibriumRule C.M x ∈ Set.Icc (max C.xT C.xS) 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ ((∀ n, p.dynamicTopLockInPathF E.V_S E.α C.x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
         (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α C.x₀ n) ∧
         (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α C.x₀ n) ∧
         Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α C.x₀) ∧
         (∀ n, IsMaxOn
           (fun a => p.joint_T_top_integrand E.V_T E.V_S
                       (p.dynamicTopLockInPathF E.V_S E.α C.x₀ n) a)
           Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.myopicEquilibriumRule C.M x ≤ p.dynamicEquilibriumRule E x)
      ∧ (∀ n, p.ruleSanctionsF (p.myopicEquilibriumRule C.M) C.x₀ n
                ≤ p.ruleSanctionsF (p.dynamicEquilibriumRule E) C.x₀ n)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF C.x₀shock N) n ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                          (p.shockPathF C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                  (p.shockPathF C.x₀shock N) n) := by
  obtain ⟨E, hVT, hVS, hG1, hG2, hPath, hG3⟩ :=
    three_goals_local_regime_comparison_uniform_starts_generalF p
      C.toStandardComplianceLocalCoreCertificate hAdj hMyoBasin
  exact ⟨E, hVT, hVS, hG1 C.x₀ C.hx₀, hG2, hPath C.x₀ C.hx₀,
    hG3 C.x₀shock C.hx₀shock_nn C.hx₀shock_le⟩

end StandardComplianceLocalCertificate


namespace StandardComplianceLocalCoreCertificateSchur

/-! ### The Schur route, general in `F`

The Schur certificate reaches its equilibrium through the Perov existence
theorem (diagonal bounds plus the Schur determinant margin) rather than the
row-sum one, so it needs its own copy of the shared scaffold. Everything after
the existence step is identical: the transition enters only through the two
chord rates, and the basin is built at the certificate's own floor `s̄`. -/

/-- **Schur sibling of `exists_equilibrium_basinTop_generalF`.** Certificate ⇒
an equilibrium whose two value functions lie in the certificate's carriers,
sitting in a `JointPreferenceBasinTop` over `[max xT xS, 1]` at the floor `s̄`.
No `hF`: the Sender leg runs on the range-restricted upper chord at rate `d`.
Since round BH1.5 the Schur goal theorem reads the Sender persistence basin
instead (`exists_equilibrium_senderPersistenceBasinTop_generalF_schur`); this
joint-basin form is kept for the Target-preference field.

Round BJ1.4 (2026-10-07): as in the row-sum form, the Target combined chord on
the carriers (P4) is now the explicit hypothesis `h_combined_on`, since the
certificate no longer carries the loss-offset stack that produced it. General
in `F`. -/
theorem exists_equilibrium_basinTop_generalF_schur
    (C : p.StandardComplianceLocalCoreCertificateSchur)
    (h_combined_on : p.TargetCombinedChordOn C.D C.xT C.sbar) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ p.JointPreferenceBasinTop E.V_T E.V_S E.α (max C.xT C.xS) C.sbar := by
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    C.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur
      C.h_inv C.hT_T_op C.hT_S_op C.hβ_T_lt C.hβ_S_lt C.hSchur
  let V_T_sub : C.D.CarrierT := ⟨E.V_T, hVT⟩
  let V_S_sub : C.D.CarrierS := ⟨E.V_S, hVS⟩
  change E.α = C.D.α_on V_T_sub V_S_sub at hα_eq
  have h_target_combined :=
    TargetCombinedChordOn.at_equilibrium p h_combined_on E hVT hVS hα_eq
  have hV_S_lip : ValueLipschitzWith E.V_S C.KS := C.hV_S_lip_carrier E.V_S hVS
  have h_stage_sender :
      ∀ x ∈ Set.Icc C.xS (1 : ℝ),
        LowerSlopeOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x C.sbar)) C.mS := by
    intro x hx
    rw [hα_eq]
    exact C.h_stage_sender_on V_T_sub V_S_sub x hx
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α C.xT C.xS C.sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_lowerSlope_sender_and_target_combined_chord_generalF
      p C.hxT_mem C.hxS_mem C.hsbar_mem C.hKS_nonneg C.hS_margin hV_S_lip
      C.hF_chord h_target_combined h_stage_sender
  have hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max C.xT C.xS) 1)
        (fun s x => p.senderDynObjective E.V_S x (E.α x) s) := by
    have h := C.hIDO_on V_T_sub V_S_sub
    convert h using 2
    rw [hα_eq]
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max C.xT C.xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO
  have hα_feas : ∀ x ∈ Set.Icc (max C.xT C.xS) 1, E.α x ∈ Sanctions.I := fun x hx =>
    E.α_mem x ⟨le_trans (le_max_of_le_left C.hxT_mem.1) hx.1, hx.2⟩
  have hα_opt : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
      IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S x a)
        Sanctions.I (E.α x) := fun x hx =>
    E.α_opt_top x ⟨le_trans (le_max_of_le_left C.hxT_mem.1) hx.1, hx.2⟩
  exact ⟨E, hVT, hVS,
    JointPreferenceBasinTop.of_oneSidedThresholds p hOne hα_feas hTopMono hα_opt⟩

/-- **Schur sibling of `exists_equilibrium_senderPersistenceBasinTop_generalF`
(round BH1.5, 2026-10-06).** Certificate ⇒ an equilibrium whose two value
functions lie in the certificate's carriers, sitting in the P4-free
`SenderPersistenceBasinTop` over `[max xT xS, 1]` at the floor `s̄`, reached
through the Perov / Schur existence theorem. The Target loss-offset fields were
not read (round BJ1.4 deleted them); the level input is the Sender leg (chord at
rate `d`, `KS`, `mS`, `β_S·KS·d < mS`) and the direction input is interval
dominance. General in `F`. -/
theorem exists_equilibrium_senderPersistenceBasinTop_generalF_schur
    (C : p.StandardComplianceLocalCoreCertificateSchur) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ p.SenderPersistenceBasinTop E.V_S E.α (max C.xT C.xS) C.sbar := by
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    C.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur
      C.h_inv C.hT_T_op C.hT_S_op C.hβ_T_lt C.hβ_S_lt C.hSchur
  let V_T_sub : C.D.CarrierT := ⟨E.V_T, hVT⟩
  let V_S_sub : C.D.CarrierS := ⟨E.V_S, hVS⟩
  change E.α = C.D.α_on V_T_sub V_S_sub at hα_eq
  have hV_S_lip : ValueLipschitzWith E.V_S C.KS := C.hV_S_lip_carrier E.V_S hVS
  have hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max C.xT C.xS) 1)
        (fun s x => p.senderDynObjective E.V_S x (E.α x) s) := by
    have h := C.hIDO_on V_T_sub V_S_sub
    convert h using 2
    rw [hα_eq]
  refine ⟨E, hVT, hVS, SenderPersistenceBasinTop.of_sender_dynamic_margin p
    (le_trans C.hxT_mem.1 (le_max_left _ _)) C.hsbar_mem ?_ hIDO⟩
  intro x hx
  have hxS : x ∈ Set.Icc C.xS (1 : ℝ) := ⟨le_trans (le_max_right _ _) hx.1, hx.2⟩
  have h_stage :
      LowerSlopeOn (fun s => p.U_S x (E.α x) s)
        (Set.Icc (0 : ℝ) (max x C.sbar)) C.mS := by
    rw [hα_eq]
    exact C.h_stage_sender_on V_T_sub V_S_sub x hxS
  exact p.senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz
    (p.sender_transition_adjusted_chord_of_upperChordOn_lowerSlope
      C.hKS_nonneg (C.hF_chord x hxS) C.hS_margin h_stage)
    hV_S_lip

/-- **All three goals at full conclusion strength on the Schur route, general
in `F`.** Same conclusions as the row-sum
`three_goals_local_uniform_starts_generalF`, reached through the Perov /
Schur-determinant existence theorem instead of the row sums. Since round BH1.5
(2026-10-06) the proof runs through the Sender persistence basin
(`exists_equilibrium_senderPersistenceBasinTop_generalF_schur`), so the Target
loss-offset fields were no longer read (round BJ1.4 deleted them from the
certificate). The statement is unchanged. -/
theorem three_goals_local_uniform_starts_generalF
    (C : p.StandardComplianceLocalCoreCertificateSchur)
    (hAdj : p.StrictAdjustment) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, C.sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                            (p.shockPathF x₀shock N) n) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀shock N) n)) := by
  obtain ⟨E, hVT, hVS, hB⟩ := C.exists_equilibrium_senderPersistenceBasinTop_generalF_schur p
  have hFloor := SenderPersistenceBasinTop.level_dyn_top p hB
  have hxbar : max C.xT C.xS ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨le_trans C.hxT_mem.1 (le_max_left _ _), C.hjoint_lt⟩
  refine ⟨E, hVT, hVS, ?_,
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling, ?_⟩
  · intro x₀ hx₀
    obtain ⟨hpath, hfloor, hxbar_le, hmono, -, hargmax, -⟩ :=
      p.equilibriumTop_senderPersistenceF_long_run_with_evidence E hB hx₀
    exact ⟨hpath, hfloor, hxbar_le, hmono, hargmax⟩
  · intro x₀shock h0 h1
    refine ⟨p.fullShockEntryHorizon (max C.xT C.xS), ?_⟩
    have hentry :
        p.shockPathF x₀shock (p.fullShockEntryHorizon (max C.xT C.xS))
          ∈ Set.Icc (max C.xT C.xS) 1 :=
      p.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment
        hAdj hxbar x₀shock ⟨h0, h1⟩ _ (le_refl _)
    obtain ⟨hpath, hfloor, hxbar_le, -, -, -, -⟩ :=
      p.equilibriumTop_senderPersistenceF_long_run_with_evidence E hB hentry
    exact ⟨hpath, hfloor, hxbar_le⟩

end StandardComplianceLocalCoreCertificateSchur

-- Round BH (2026-10-06) additions; relative names keep the lines under 100 characters.
#print axioms
  StandardComplianceLocalCoreCertificate.exists_equilibrium_senderPersistenceBasinTop_generalF
open StandardComplianceLocalCoreCertificateSchur in
#print axioms exists_equilibrium_senderPersistenceBasinTop_generalF_schur
#print axioms StandardComplianceLocalCoreCertificate.pathwise_dominance_generalF
#print axioms StandardComplianceLocalCertificate.three_goals_local_regime_comparison_generalF

end Params

end AbstractGame

end Sanctions

#print axioms
  Sanctions.AbstractGame.Params.Target_combined_chord_of_decomposition_lowerChord
#print axioms
  Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate.goal2_dominance_generalF
#print axioms
  Sanctions.AbstractGame.Params.targetSanctionObjective_mono_of_lowerChord_loss_offset_on
#print axioms
  Sanctions.AbstractGame.Params.OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target_on_generalF
#print axioms
  Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate.three_goals_local_uniform_starts_generalF
#print axioms
  Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate.three_goals_local_generalF
#print axioms
  Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate.three_goals_local_regime_comparison_uniform_starts_generalF
#print axioms
  Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur.exists_equilibrium_basinTop_generalF_schur
#print axioms
  Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur.three_goals_local_uniform_starts_generalF

