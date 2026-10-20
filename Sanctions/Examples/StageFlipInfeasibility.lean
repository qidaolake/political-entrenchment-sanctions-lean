/-
Sanctions/Examples/StageFlipInfeasibility.lean

**Rule-11 audit artifact (2026-07-07): the high-basin stage-flip
constructor family is hypothesis-infeasible at every
complete-certificate economy in `Examples/`.**

The paper-canonical flip route — the four high-basin members of the
`of_stage_flip` constructor family
(`OneSidedSanctionPreferenceThresholds.of_stage_flip`,
`StandardComplianceLocalCoreCertificate.of_stage_flip`,
`StandardComplianceLocalCoreCertificate_MS.of_stage_flip`) and both
headline wrappers (`standardCompliance_three_goals_from_stage_flip`,
`standardCompliance_three_goals_from_stage_flip_generalF`) — has
**jointly unsatisfiable hypothesis bundles at all five complete
certificate economies** (`eeCertParams` [= the `eeCertCertificateMS`
economy], `qbParams`, `fgcParams`, `lbParams`, `b2Params`), for EVERY
choice of the free data `(s̄, m_S, K_S, carriers)`. Case split over
the sanction floor `s̄ ∈ [0, 1]` (forced by `hsbar_mem`):

* **`s̄ < 1`** — the Target boundary sign
  `h1_T : 1 ∈ targetFlipSet s̄` ("at the top state, every sanction
  chord in `[s̄, 1]` weakly raises the Target stage payoff") is
  FALSE: all five witnesses are *loss-offset* designs whose Target
  stage sanction slope is strictly negative everywhere — the
  sanction-pain constants (3, 14/5, 7/4, ≥ 1) dominate the rally
  cross-partials (1/10 or 1), so the flip set is empty below the
  degenerate floor. Refutations `*_one_not_mem_targetFlipSet` below.
* **`s̄ = 1`** — `h1_T` becomes vacuously true (the chord range
  degenerates to `{1}`), but then the flip set is ALL of `[0, 1]`,
  so the interiority sign `h0_T : 0 ∉ targetFlipSet s̄` of the
  MS-form constructor fails (`targetFlipSet_zero_mem_at_sbar_one`);
  independently the MS ordering inputs `hsbar_le` + `hjoint_lt`
  already force `s̄ < 1` (`stageFlip_ordering_forces_sbar_lt_one`);
  and for the affine (legacy) constructor — which takes neither
  `h0_T` nor `hsbar_le` — the Sender boundary sign
  `h1_S : 1 ∈ senderFloorFlipSet 1 m_S` forces a NEGATIVE wedge
  level `m_S` (`*_sbarOne_senderWedge_neg`), contradicting
  `hS_margin` + `hKS_nonneg` (which force `m_S > β_S·K_S·δ ≥ 0`).

The failure is specifically the *boundary sign*, not the
complementarity structure: the two Round-A stage
increasing-differences primitives (`TargetStageID`,
`SenderStageID` — chord forms of `∂²U/∂s∂x ≥ 0`) DO hold at
`eeCertParams` and `fgcParams` (`*_targetStageID`,
`*_senderStageID` below).

**Consequences.** Non-vacuity of the flip route requires a NEW tuned
economy whose Target stage payoff genuinely level-flips in the
sanction at high states (e.g. an `s`-coefficient of the form
`k·(x − x̄_T)` with the pain constant below the rally term at the
top state), plus a full new certificate stack (carriers, invariance,
Schur rows, argmax uniqueness, myopic comparator).
**CLOSED (2026-07-08, Round R-FLIP)**: exactly such an economy was
designed and built — see `Examples/StageFlipCertWitness.lean`
(`sfParams`, sanction slope `5x − a − 1` flipping at pivot `2/5`;
`sfCertificate` produced by the `of_stage_flip` constructor;
`sfCert_three_goals_generalF`). The refutations below remain the
proof that the five LOSS-OFFSET witnesses cannot inhabit the route —
the two sufficient routes are mutually exclusive at any given
economy. One live lead outside this family's scope: the low-basin dual
`OneSidedSanctionLowBasinPreferenceThresholds.of_stage_flip_low`
appears feasible at `lbParams` (dual boundary signs hold
numerically; not kernel-checked here) — but it is a thresholds Prop
only and would not deliver the certificate/headline non-vacuity the
paper's flip-route proposition claims.

**Scope after round BH-1 (2026-10-06, item BH1.8).** The verdict covers
the constructors and wrappers named above, each of which takes the
Target boundary sign `h1_T` (and, in the MS form, `h0_T`). It does not
cover the persistence route of `Theory/Basin/StageFlipPersistence.lean`
(`StandardCompliancePersistenceCertificate.of_stage_flip` and its
pre-basin-ascent three-goals siblings), which takes no Target boundary
sign and no other Target-side stage input; the refutations below say
nothing about it. Whether the five loss-offset economies inhabit the
persistence route is not decided here: its Sender-side inputs are not
checked at these economies. The old wrapper
`standardCompliance_three_goals_from_stage_flip_generalF` still lists
`h1_T` and `h0_T` in its statement (no longer read by its proof), so its
hypothesis bundle stays infeasible at these economies.

Rule 5: these are refutation certificates at named witnesses (the
allowed witness-specific existence/non-existence case); the two
generic `s̄ = 1` lemmas are parametric. Rule 3: no new assumptions —
every statement is proved (or refuted) from the existing surface.
-/

import Sanctions.Examples.EECertWitness
import Sanctions.Examples.QuadBumpCertWitnessMS
import Sanctions.Examples.FourGroupCertWitness
import Sanctions.Examples.LowBasinCertWitness
import Sanctions.Examples.B2NonMonotoneCertWitness
import Sanctions.Theory.Basin.StageFlipCertificate

namespace Sanctions

namespace Examples

open Set AbstractGame Sanctions.AbstractGame.Params

/-! ## 1. Positive corroboration: the stage-ID primitives hold

The two user-approved Round-A stage-complementarity primitives are
satisfied at the certificate witnesses — the flip-route failure below
is NOT a failure of increasing differences. -/

/-- **Target stage complementarity holds at `eeCertParams`**: the
rally cross-partial is `∂²U_T/∂s∂x = 1/10 > 0`, so Target sanction
chords weakly rise with the state (exact chord identity
`ΔΔ = (s₂−s₁)(x₂−x₁)/10`). -/
theorem eeCertParams_targetStageID : eeCertParams.TargetStageID := by
  intro a _ s s' x x' _ _ hss _ _ hxx
  simp only [eeCertParams_U_T, eecU_T]
  nlinarith [mul_nonneg (sub_nonneg.mpr hss) (sub_nonneg.mpr hxx)]

/-- **Sender stage complementarity holds at `eeCertParams`**: the
rally cross-partial is `∂²U_S/∂s∂x = 1 > 0`
(`ΔΔ = (s₂−s₁)(x₂−x₁)`). -/
theorem eeCertParams_senderStageID : eeCertParams.SenderStageID := by
  intro a _ s s' x x' _ _ hss _ _ hxx
  simp only [eeCertParams_U_S, eecU_S]
  nlinarith [mul_nonneg (sub_nonneg.mpr hss) (sub_nonneg.mpr hxx)]

/-- **Target stage complementarity holds at the microfounded
`fgcParams`**: `∂²U_T/∂s∂x = 1 > 0` from the four-group rally
dominance. -/
theorem fgcParams_targetStageID : fgcParams.TargetStageID := by
  intro a _ s s' x x' _ _ hss _ _ hxx
  simp only [fgcParams_U_T]
  nlinarith [mul_nonneg (sub_nonneg.mpr hss) (sub_nonneg.mpr hxx)]

/-- **Sender stage complementarity holds at `fgcParams`**:
`∂²U_S/∂s∂x = 1 > 0` from the hawk-group effectiveness slope. -/
theorem fgcParams_senderStageID : fgcParams.SenderStageID := by
  intro a _ s s' x x' _ _ hss _ _ hxx
  simp only [fgcParams_U_S]
  nlinarith [mul_nonneg (sub_nonneg.mpr hss) (sub_nonneg.mpr hxx)]

/-! ## 2. The decisive refutation: `h1_T` fails at every floor `s̄ < 1`

At each economy, the counterexample chord is at the maximal-rally top
state `x = 1` and full defiance `a = 0`, on `[s̄, 1]`: the Target
stage payoff strictly FALLS. -/

/-- **`h1_T` counterexample at `eeCertParams`** (the economy of BOTH
`eeCertCertificate` and `eeCertCertificateMS`): the Target stage
sanction slope is `a/10 + x/10 − 3 ≤ −2.8` everywhere, e.g.
`U_T(1,0,1/2) = 2.55 > 1.10 = U_T(1,0,1)`. The top state is not in
the flip set for any floor `s̄ < 1`, so the boundary-sign input of
every high-basin `of_stage_flip` constructor fails. -/
theorem eeCert_one_not_mem_targetFlipSet :
    ∀ sbar ∈ Set.Ico (0 : ℝ) 1,
      (1 : ℝ) ∉ eeCertParams.targetFlipSet sbar := by
  rintro sbar hs ⟨-, hmem⟩
  have h := hmem 0 ⟨le_refl _, by norm_num⟩ sbar ⟨le_refl _, hs.2.le⟩
    1 ⟨hs.2.le, le_refl _⟩ hs.2.le
  simp only [eeCertParams_U_T, eecU_T] at h
  nlinarith [hs.2]

/-- **`h1_T` counterexample at `qbParams`** (same stage payoffs as
`eeCertParams`, quadratic-bump transition — the transition is
irrelevant to the stage flip sets). -/
theorem qbCert_one_not_mem_targetFlipSet :
    ∀ sbar ∈ Set.Ico (0 : ℝ) 1,
      (1 : ℝ) ∉ qbParams.targetFlipSet sbar := by
  rintro sbar hs ⟨-, hmem⟩
  have h := hmem 0 ⟨le_refl _, by norm_num⟩ sbar ⟨le_refl _, hs.2.le⟩
    1 ⟨hs.2.le, le_refl _⟩ hs.2.le
  simp only [qbParams_U_T, eecU_T] at h
  nlinarith [hs.2]

/-- **`h1_T` counterexample at the microfounded `fgcParams`**: the
Target stage sanction slope is `x − 14/5 ≤ −1.8` everywhere
(`U_T(1,0,1/2) = 2.1 > 1.2 = U_T(1,0,1)`). -/
theorem fgcCert_one_not_mem_targetFlipSet :
    ∀ sbar ∈ Set.Ico (0 : ℝ) 1,
      (1 : ℝ) ∉ fgcParams.targetFlipSet sbar := by
  rintro sbar hs ⟨-, hmem⟩
  have h := hmem 0 ⟨le_refl _, by norm_num⟩ sbar ⟨le_refl _, hs.2.le⟩
    1 ⟨hs.2.le, le_refl _⟩ hs.2.le
  simp only [fgcParams_U_T] at h
  nlinarith [hs.2]

/-- **`h1_T` counterexample at `lbParams`** (the low-basin witness;
Target stage sanction slope `−(1 + x/10 + a/10) ≤ −1`). -/
theorem lbCert_one_not_mem_targetFlipSet :
    ∀ sbar ∈ Set.Ico (0 : ℝ) 1,
      (1 : ℝ) ∉ lbParams.targetFlipSet sbar := by
  rintro sbar hs ⟨-, hmem⟩
  have h := hmem 0 ⟨le_refl _, by norm_num⟩ sbar ⟨le_refl _, hs.2.le⟩
    1 ⟨hs.2.le, le_refl _⟩ hs.2.le
  simp only [lbParams_U_T, lbU_T] at h
  nlinarith [hs.2]

/-- **`h1_T` counterexample at `b2Params`** (the non-monotone-carrier
witness; Target stage sanction slope `−9/4 + 1/2 = −7/4`). -/
theorem b2Cert_one_not_mem_targetFlipSet :
    ∀ sbar ∈ Set.Ico (0 : ℝ) 1,
      (1 : ℝ) ∉ b2Params.targetFlipSet sbar := by
  rintro sbar hs ⟨-, hmem⟩
  have h := hmem 0 ⟨le_refl _, by norm_num⟩ sbar ⟨le_refl _, hs.2.le⟩
    1 ⟨hs.2.le, le_refl _⟩ hs.2.le
  simp only [b2Params_U_T, b2U_T] at h
  nlinarith [hs.2]

/-! ## 3. The `s̄ = 1` escape branch is closed -/

/-- **At the degenerate floor `s̄ = 1` the Target flip set is all of
`[0, 1]`, at EVERY economy**: the chord range `[1, 1]` carries only
the trivial chord, so `0` is a member and the MS-form interiority
sign `h0_T : 0 ∉ targetFlipSet s̄` fails. (Generic in `p`.) -/
theorem targetFlipSet_zero_mem_at_sbar_one
    (p : Sanctions.AbstractGame.Params) :
    (0 : ℝ) ∈ p.targetFlipSet 1 := by
  refine ⟨⟨le_refl _, by norm_num⟩, fun a _ s₁ hs₁ s₂ hs₂ _ => ?_⟩
  obtain rfl : s₁ = 1 := le_antisymm hs₁.2 hs₁.1
  obtain rfl : s₂ = 1 := le_antisymm hs₂.2 hs₂.1
  exact le_refl _

/-- **The MS constructor's ordering inputs force `s̄ < 1`** (generic
in `p`): the floor-below-pivot ordering `hsbar_le` and the pivot
nondegeneracy `hjoint_lt` compose to `s̄ < 1`, so the MS-form bundle
can never retreat to the degenerate floor. -/
theorem stageFlip_ordering_forces_sbar_lt_one
    (p : Sanctions.AbstractGame.Params) {sbar mS : ℝ}
    (hsbar_le :
      sbar ≤ max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS))
    (hjoint_lt :
      max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS) < 1) :
    sbar < 1 :=
  lt_of_le_of_lt hsbar_le hjoint_lt

/-- **Sender-wedge refutation at `s̄ = 1`, `eeCertParams`**: Sender
floor flip membership of the top state forces `m_S ≤ −3/20 < 0`
(counterexample chord `[9/10, 1]` at `(x, a) = (1, 1)`:
`ΔU_S = −3/200`), contradicting both `hS_margin` + `hKS_nonneg`
(legacy constructor: `m_S > β_S·K_S·δ ≥ 0`) and `hmS_pos` (MS
constructor). -/
theorem eeCert_sbarOne_senderWedge_neg (mS : ℝ)
    (h : (1 : ℝ) ∈ eeCertParams.senderFloorFlipSet 1 mS) :
    mS ≤ -(3 / 20) := by
  obtain ⟨-, hmem⟩ := h
  have hch := hmem 1 ⟨by norm_num, le_refl _⟩
    (9 / 10) ⟨by norm_num, by norm_num⟩
    1 ⟨by norm_num, le_refl _⟩ (by norm_num)
  simp only [eeCertParams_U_S, eecU_S] at hch
  nlinarith [hch]

/-- **Sender-wedge refutation at `s̄ = 1`, `qbParams`** (same Sender
stage payoff as `eeCertParams`): `m_S ≤ −3/20`. -/
theorem qbCert_sbarOne_senderWedge_neg (mS : ℝ)
    (h : (1 : ℝ) ∈ qbParams.senderFloorFlipSet 1 mS) :
    mS ≤ -(3 / 20) := by
  obtain ⟨-, hmem⟩ := h
  have hch := hmem 1 ⟨by norm_num, le_refl _⟩
    (9 / 10) ⟨by norm_num, by norm_num⟩
    1 ⟨by norm_num, le_refl _⟩ (by norm_num)
  simp only [qbParams_U_S, eecU_S] at hch
  nlinarith [hch]

/-- **Sender-wedge refutation at `s̄ = 1`, `fgcParams`**: same chord
`[9/10, 1]` at `(1, 1)` gives `m_S ≤ −3/20`. -/
theorem fgcCert_sbarOne_senderWedge_neg (mS : ℝ)
    (h : (1 : ℝ) ∈ fgcParams.senderFloorFlipSet 1 mS) :
    mS ≤ -(3 / 20) := by
  obtain ⟨-, hmem⟩ := h
  have hch := hmem 1 ⟨by norm_num, le_refl _⟩
    (9 / 10) ⟨by norm_num, by norm_num⟩
    1 ⟨by norm_num, le_refl _⟩ (by norm_num)
  simp only [fgcParams_U_S] at hch
  nlinarith [hch]

/-- **Sender-wedge refutation at `s̄ = 1`, `lbParams`** (dovish
mirror: sanctions are a stage loss to the Sender everywhere; chord
`[0, 1]` at `(1, 1)` gives `m_S ≤ −5/2`). -/
theorem lbCert_sbarOne_senderWedge_neg (mS : ℝ)
    (h : (1 : ℝ) ∈ lbParams.senderFloorFlipSet 1 mS) :
    mS ≤ -(5 / 2) := by
  obtain ⟨-, hmem⟩ := h
  have hch := hmem 1 ⟨by norm_num, le_refl _⟩
    0 ⟨le_refl _, by norm_num⟩
    1 ⟨by norm_num, le_refl _⟩ (by norm_num)
  simp only [lbParams_U_S, lbU_S] at hch
  nlinarith [hch]

/-- **Sender-wedge refutation at `s̄ = 1`, `b2Params`** (interior
slice-peak design: chord `[15/16, 1]` at `(1, 1)` gives
`m_S/16 ≤ −3/512`, i.e. `m_S ≤ −3/32`). -/
theorem b2Cert_sbarOne_senderWedge_neg (mS : ℝ)
    (h : (1 : ℝ) ∈ b2Params.senderFloorFlipSet 1 mS) :
    mS ≤ -(3 / 32) := by
  obtain ⟨-, hmem⟩ := h
  have hch := hmem 1 ⟨by norm_num, le_refl _⟩
    (15 / 16) ⟨by norm_num, by norm_num⟩
    1 ⟨by norm_num, le_refl _⟩ (by norm_num)
  simp only [b2Params_U_S, b2U_S, b2f, b2hump, b2base, b2comp, b2lam,
    b2rho, b2pt, b2clip] at hch
  norm_num at hch
  linarith

/-! ## 4. Bundled infeasibility (headline form of the audit verdict)

The synthesis theorems: at the two primary candidate economies, the
boundary-sign inputs alone are jointly contradictory for the MS-form
constructor, and the boundary signs plus the Sender wedge are jointly
contradictory for the affine (legacy) constructor — for every
`(s̄, m_S, K_S)`. -/

/-- **MS-form bundle infeasible at `eeCertParams`**: the two Target
boundary signs `h1_T` (top state flipped) and `h0_T` (bottom state
unflipped) of `StandardComplianceLocalCoreCertificate_MS.of_stage_flip`
are jointly contradictory for every feasible floor `s̄ ∈ [0, 1]`. -/
theorem eeCert_stageFlip_MS_boundary_infeasible {sbar : ℝ}
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h1_T : (1 : ℝ) ∈ eeCertParams.targetFlipSet sbar)
    (h0_T : (0 : ℝ) ∉ eeCertParams.targetFlipSet sbar) : False := by
  rcases lt_or_eq_of_le hsbar_mem.2 with hlt | heq
  · exact eeCert_one_not_mem_targetFlipSet sbar ⟨hsbar_mem.1, hlt⟩ h1_T
  · subst heq
    exact h0_T (targetFlipSet_zero_mem_at_sbar_one eeCertParams)

/-- **Legacy (affine) bundle infeasible at `eeCertParams`**: the
Target boundary sign `h1_T`, the Sender boundary sign `h1_S`, and the
dynamic wedge margin `hS_margin` (with `hKS_nonneg`) of
`StandardComplianceLocalCoreCertificate.of_stage_flip` are jointly
contradictory for every `(s̄, m_S, K_S)`. -/
theorem eeCert_stageFlip_legacy_infeasible {sbar mS KS : ℝ}
    (hsbar_mem : sbar ∈ Sanctions.I) (hKS_nonneg : 0 ≤ KS)
    (hS_margin : eeCertParams.β_S * KS * eeCertParams.δ < mS)
    (h1_T : (1 : ℝ) ∈ eeCertParams.targetFlipSet sbar)
    (h1_S : (1 : ℝ) ∈ eeCertParams.senderFloorFlipSet sbar mS) :
    False := by
  rcases lt_or_eq_of_le hsbar_mem.2 with hlt | heq
  · exact eeCert_one_not_mem_targetFlipSet sbar ⟨hsbar_mem.1, hlt⟩ h1_T
  · subst heq
    have hneg := eeCert_sbarOne_senderWedge_neg mS h1_S
    simp only [eeCertParams_β_S, eeCertParams_δ] at hS_margin
    nlinarith [hS_margin, hneg, hKS_nonneg]

/-- **MS-form bundle infeasible at the microfounded `fgcParams`**:
same two-sign contradiction as at `eeCertParams`. -/
theorem fgcCert_stageFlip_MS_boundary_infeasible {sbar : ℝ}
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h1_T : (1 : ℝ) ∈ fgcParams.targetFlipSet sbar)
    (h0_T : (0 : ℝ) ∉ fgcParams.targetFlipSet sbar) : False := by
  rcases lt_or_eq_of_le hsbar_mem.2 with hlt | heq
  · exact fgcCert_one_not_mem_targetFlipSet sbar ⟨hsbar_mem.1, hlt⟩ h1_T
  · subst heq
    exact h0_T (targetFlipSet_zero_mem_at_sbar_one fgcParams)

/-- **Legacy (affine) bundle infeasible at `fgcParams`**: same
boundary-plus-wedge contradiction as at `eeCertParams`. -/
theorem fgcCert_stageFlip_legacy_infeasible {sbar mS KS : ℝ}
    (hsbar_mem : sbar ∈ Sanctions.I) (hKS_nonneg : 0 ≤ KS)
    (hS_margin : fgcParams.β_S * KS * fgcParams.δ < mS)
    (h1_T : (1 : ℝ) ∈ fgcParams.targetFlipSet sbar)
    (h1_S : (1 : ℝ) ∈ fgcParams.senderFloorFlipSet sbar mS) :
    False := by
  rcases lt_or_eq_of_le hsbar_mem.2 with hlt | heq
  · exact fgcCert_one_not_mem_targetFlipSet sbar ⟨hsbar_mem.1, hlt⟩ h1_T
  · subst heq
    have hneg := fgcCert_sbarOne_senderWedge_neg mS h1_S
    simp only [fgcParams_β_S, fgcParams_δ] at hS_margin
    nlinarith [hS_margin, hneg, hKS_nonneg]

#print axioms eeCert_one_not_mem_targetFlipSet
#print axioms targetFlipSet_zero_mem_at_sbar_one
#print axioms eeCert_stageFlip_MS_boundary_infeasible
#print axioms eeCert_stageFlip_legacy_infeasible
#print axioms fgcCert_stageFlip_MS_boundary_infeasible
#print axioms fgcCert_stageFlip_legacy_infeasible

end Examples

end Sanctions
