/-
Sanctions/Examples/SymbolicCertifiedFamilyGeneralFEmbedding.lean

**The affine family is an instance of the general one.**

Rule 5's parametric-first pattern, applied to the transition: the general
family is proved first and the affine family is recovered as its degenerate
member, at `(glo, ghi, dlo) = (1−δ, 1−δ, δ)`.

Until plan item BJ4.3 (2026-10-08) the general family also carried a curvature
block (`dhi`, `M_F`, `M_state` and the curvature margin `hCurv`), and this file
showed that it cost the affine family nothing (at `M_state = 0` the Riccati
modulus vanished and `hCurv` collapsed to `0 < q`). The block is deleted, so the
embedding now needs nothing beyond the affine family's own fields. The
generalisation is strict in one direction only — every affine member survives,
and non-affine members are added.

## READ THIS BEFORE CLASSIFYING ANYTHING IN THIS FILE (audit note)

**The results here are universals over a family, not witness instances.** They
are quantified over the symbolic economy variable declared below -- every
admissible member -- so they license universal statements about the family, and
Rule 9's "a witness proves only existence" restriction does **not** apply to
them.

The file sits under `Examples/` because the family fixes a *functional form* for
the stage payoffs, not because its theorems are point checks. Rule 19 keeps
`Theory/` for statements over an arbitrary `Params`; a coefficient-parameterised
algebraic family is narrower than that, so `Examples/` is the correct home and
the file is deliberately not moved.

This banner exists because the filing has already misled an audit. A 2026-08-16
review classified `prop:equilibrium-patience-feedback` as a paper universal
backed only by a witness, having found the numeric `eeCertB_*` names cited in
the formalization map and not the `symbolic_*` siblings in this cluster. The
paper was right and the audit was wrong. If you are deciding what a paper claim
rests on, grep this cluster before concluding that a family-level claim has only
witness backing.
-/

import Sanctions.Examples.SymbolicCertifiedFamilyGeneralF
-- `affine_transitionChordPack`.
import Sanctions.Examples.AffineInstance.Certificates
import Sanctions.Examples.AffineInstance.TransitionChords
import Sanctions.Examples.AffineInstance.SemiconcaveRiccati

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params Sanctions.TransitionChords Sanctions.Semiconcave

noncomputable section

/-! ## 0. (Retired.) The Riccati modulus at zero state curvature

This section proved that the general family's Riccati modulus `symSigV`
vanished at `M_state = 0` (`symSigV_zero_of_Mstate_zero`,
`symSigV_eq_of_Mstate_zero`). `symSigV` was deleted with the curvature block
(plan item BJ4.3, 2026-10-08), and the two lemmas with it. -/

/-! ## 1. The embedding -/

namespace SymbolicEconomy

variable (A : SymbolicEconomy)

/-- **The affine family embeds into the general-transition family.**

Every chord field is discharged at the affine law through the routes the
brief names:

* `hSlo` — the sanction lower chord comes straight out of the `Params`-level
  bundle `AbstractGame.Params.affine_transitionChordPack`, at `d_lo = δ`;
* `hband` — the two-sided corner band comes from the ABANDONED equality
  route, `cornerStateChord_of_cornerSectionTop` applied to the pack's own
  `CornerSectionTopWith (1 − δ)` component.  The affine member is exactly the
  degenerate `glo = ghi` point of the band, which is what makes the equality
  route available here and unavailable at `wobbleEconF` (§5).

The two margins `SymbolicEconomyF` carries transfer verbatim: it states them
with `glo` and `dlo` where `SymbolicEconomy` writes `1 − δ` and `δ`, and at
this member those are the same numbers, so `A.hCorner` and `A.hTMargin`
typecheck unchanged.  The curvature block the general family used to carry
(`hShi`, `hFsc`, `hGsc` at `(d_hi, M_F, M_state) = (δ, 0, 0)` and `hCurv`) was
deleted by plan item BJ4.3 (2026-10-08), so the map no longer supplies it; the
pack still gives those predicates (`toF_hShi_from_pack`, `toF_hFsc_from_pack`).
The affine family's third margin, the Sender stage margin
`A.hSMargin`, and its sanction floor `A.sbar` are simply forgotten: the general
family no longer carries them (plan item BJ4.1, 2026-10-07), and the affine
`x̄ ≤ s̄ < 1` supplies the general `x̄ < 1` (`A.xb_lt_one`).  Nor does the map
supply `F_mem` or `glo ≤ ghi`, which are theorems of the general family (plan
item BJ4.2); `0 < δ` supplies the weakened `0 ≤ dlo`.

This is the only embedding of the affine family into the general one: the
duplicate `SymbolicEconomyF.ofSymbolic` and the bridge `toF_eq_ofSymbolic`
were deleted on 2026-10-06 (plan item BG3.8). -/
def toF : SymbolicEconomyF where
  F := AbstractGame.affineF A.δ
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨A.hδ0, A.hδ1⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨A.hδ0, A.hδ1⟩
  F_diag := AbstractGame.affineF_diag _
  glo := 1 - A.δ
  ghi := 1 - A.δ
  dlo := A.δ
  -- the two-sided band, via the abandoned equality route
  hband := cornerStateChord_of_cornerSectionTop
    (A.toParams.affine_transitionChordPack (δ := A.δ) rfl).2.2.1
  -- the sanction lower chord, via the `Params`-level pack
  hSlo := (A.toParams.affine_transitionChordPack (δ := A.δ) rfl).1
  hglo0 := by linarith [A.hδ1]
  hghi1 := by linarith [A.hδ0]
  hdlo0 := A.hδ0.le
  δ := A.δ
  βS := A.βS
  βT := A.βT
  q := A.q
  u₀ := A.u₀
  k := A.k
  r := A.r
  w := A.w
  ℓ := A.ℓ
  c := A.c
  n := A.n
  v := A.v
  xb := A.xb
  hδ0 := A.hδ0
  hδ1 := A.hδ1
  hβS0 := A.hβS0
  hβS1 := A.hβS1
  hβT0 := A.hβT0
  hβT1 := A.hβT1
  hq := A.hq
  hqr := A.hqr
  hu₀ := A.hu₀
  hk := A.hk
  hn := A.hn
  hℓ := A.hℓ
  hcn := A.hcn
  hxb0 := A.hxb0
  hxb1 := A.xb_lt_one
  hCorner := A.hCorner
  hTMargin := A.hTMargin

/-- The rate assignment, on the record. (`toF_dhi`, `toF_MF` and `toF_Mstate`
named fields that plan item BJ4.3 deleted, and were deleted with them.) -/
@[simp] theorem toF_glo : A.toF.glo = 1 - A.δ := rfl
@[simp] theorem toF_ghi : A.toF.ghi = 1 - A.δ := rfl
@[simp] theorem toF_dlo : A.toF.dlo = A.δ := rfl
@[simp] theorem toF_F : A.toF.F = AbstractGame.affineF A.δ := rfl
@[simp] theorem toF_q : A.toF.q = A.q := rfl
@[simp] theorem toF_βS : A.toF.βS = A.βS := rfl
@[simp] theorem toF_βT : A.toF.βT = A.βT := rfl
@[simp] theorem toF_δ : A.toF.δ = A.δ := rfl

/-- **The band is degenerate at the affine member.**  Contrast
`wobbleEconF_band_strict`, where `glo < ghi` strictly. -/
theorem toF_band_degenerate : A.toF.glo = A.toF.ghi := rfl

/-- **The sanction chords coincide at the affine member**: the lower rate
`dlo = δ` is also an upper sanction chord rate, so the transition's sanction
responsiveness is exactly `δ`. Affine-restricted.

**Edited in place (plan item BJ4.3, 2026-10-08).** The statement was
`A.toF.dlo = A.toF.dhi`; the field `dhi` is deleted, so the statement now says
the same thing of `F` directly. -/
theorem toF_chords_degenerate : SanctionUpperChord A.toF.F A.toF.dlo :=
  (A.toParams.affine_transitionChordPack (δ := A.δ) rfl).2.1

/-! ## 2. The chord discharges, cross-checked against the `Params`-level pack -/

/-- The `Params`-level bundle at `A.toParams`, exhibited. -/
theorem toParams_chordPack :
    A.toParams.SanctionLowerChordWith A.δ ∧ A.toParams.SanctionUpperChordWith A.δ
      ∧ A.toParams.CornerSectionTopWith (1 - A.δ)
      ∧ A.toParams.SanctionSemiconcaveWith 0 :=
  A.toParams.affine_transitionChordPack (δ := A.δ) rfl

/-- Each structure field is the corresponding pack component, on the nose. -/
theorem toF_hSlo_from_pack : SanctionLowerChord A.toF.F A.toF.dlo :=
  A.toParams_chordPack.1

/-- The affine member's upper sanction chord at rate `δ`, from the pack.
Affine-restricted. **Edited in place (plan item BJ4.3):** the rate was the
deleted field `A.toF.dhi`, which equalled `A.δ`. -/
theorem toF_hShi_from_pack : SanctionUpperChord A.toF.F A.δ :=
  A.toParams_chordPack.2.1

/-- The affine member's transition is sanction-semiconcave with modulus `0`,
from the pack. Affine-restricted. **Edited in place (plan item BJ4.3):** the
modulus was the deleted field `A.toF.MF`, which equalled `0`. -/
theorem toF_hFsc_from_pack : SanctionSemiconcave A.toF.F 0 :=
  A.toParams_chordPack.2.2.2

/-- **The abandoned equality route is available exactly here.**  The affine
member does satisfy `CornerSectionTop`, and its band is that equality read
two-sidedly.  `wobbleEconF_not_cornerSectionTop` shows the general family also
contains economies where no such `γ` exists (§5). -/
theorem toF_cornerSectionTop : CornerSectionTop A.toF.F (1 - A.δ) :=
  A.toParams_chordPack.2.2.1

theorem toF_hband_from_cornerTop : CornerStateChord A.toF.F A.toF.glo A.toF.ghi :=
  cornerStateChord_of_cornerSectionTop A.toF_cornerSectionTop

/-- The `Foundations`-level shortcut `affine_cornerStateChord` gives the same
band; it is definitionally `cornerStateChord_of_cornerSectionTop` applied to
`affine_cornerSectionTop`, so the two routes are not merely equivalent but
identical. -/
theorem toF_hband_from_shortcut : CornerStateChord A.toF.F A.toF.glo A.toF.ghi :=
  affine_cornerStateChord A.δ

/-- The realised recursion is affine — this is precisely what the general
family exists to relax. -/
theorem toF_realised (y : ℝ) : A.toF.F y 1 = (1 - A.δ) * y + A.δ := by
  simp only [toF_F, AbstractGame.affineF]; ring

/-! ## 3. The derived constants agree, and the cone collapses

Every one of these is `rfl`: the general family's closed forms, evaluated at
the affine rates, are *syntactically* the affine family's own closed forms —
not merely numerically equal. -/

@[simp] theorem toF_toParams : A.toF.toParams = A.toParams := rfl

@[simp] theorem toF_stageS0 : A.toF.stageS0 = A.stageS0 := rfl
@[simp] theorem toF_stageSlopeS : A.toF.stageSlopeS = A.stageSlopeS := rfl
@[simp] theorem toF_stageNormS : A.toF.stageNormS = A.stageNormS := rfl
@[simp] theorem toF_stageSlopeT : A.toF.stageSlopeT = A.stageSlopeT := rfl

/-- `K_S` agrees: `bellmanLipConstant β_S (1−δ) (r+w)` either way. -/
@[simp] theorem toF_KS : A.toF.KS = A.KS := rfl

/-- `M_S` agrees. -/
@[simp] theorem toF_MS : A.toF.MS = A.MS := rfl

/-- `g_T` agrees. -/
@[simp] theorem toF_gT : A.toF.gT = A.gT := rfl

/-- **The cone collapses to the slope-pinned ball.**  `g_S` is
`bellmanLowerSlopeConstant β_S glo (r+w)` and `K_S` is
`bellmanLipConstant β_S ghi (r+w)`; the two closed forms are the same
function, and `glo = ghi` here, so the lower slope and the Lipschitz rate
coincide.  This is exactly the slope pin that
`SymbolicEconomy.carrierS_diff` / `valLipGainBall_clip_diff` runs on. -/
@[simp] theorem toF_gS_eq_KS : A.toF.gS = A.toF.KS := rfl

@[simp] theorem toF_gS : A.toF.gS = A.KS := rfl

/-- The general family's gain ball, at the affine rates, IS the affine
family's carrier. -/
theorem toF_gainBall :
    valLipGainBall A.toF.MS A.toF.KS A.toF.gS 0 = A.carrierS := rfl

/-! ## 4. (Retired.) The curvature margin at the affine member

This section showed that the general family's curvature margin `hCurv` was free
at the affine member (`affine_curv_margin_iff`, `toF_curv_margin_iff`,
`toF_curv_margin`, with the collapse `toF_SigV : Σ_V = 0`). The margin and the
modulus were deleted with the curvature block (plan item BJ4.3, 2026-10-08), and
these lemmas with them: the embedding no longer has a margin to discharge. -/

end SymbolicEconomy

/-! ### 4a. The Riccati constant with a curved stage payoff

Kept from the retired §4 as a fact about the Riccati constant
`(ψ + β·K·M_state)/(1 − β·ghi²)`: with a strictly curved stage payoff (`ψ > 0`)
it is strictly positive even at zero state curvature. It explained why the
deleted curvature margin was free at the affine member only because the
Sender's corner stage payoff `U_S(y, ·, 1) = (u₀ − q/2) + (r+w)·y` is affine in
the state. -/

/-- **With a curved stage payoff the Riccati term is not zero.**  At
`M_state = 0` and `M_F = 0` the expression `β_S·(Σ·δ² + K·0)`, with `Σ` the
Riccati constant at stage curvature `ψ`, is strictly positive whenever `ψ` is.
Economy-free; it no longer feeds any margin (plan item BJ4.3). -/
theorem curv_margin_lhs_pos_of_stage_curved
    {βS ghi ψ K δ : ℝ} (hβ : 0 < βS) (hψ : 0 < ψ) (hδ : δ ≠ 0)
    (hΘ : 0 < 1 - βS * ghi ^ 2) :
    0 < βS * (bellmanSemiconcaveConstant βS ghi ψ K 0 * δ ^ 2 + K * 0) := by
  rw [bellmanSemiconcaveConstant_affine, mul_zero, add_zero]
  have hpos : 0 < ψ / (1 - βS * ghi ^ 2) := div_pos hψ hΘ
  have hδ2 : 0 < δ ^ 2 := by positivity
  exact mul_pos hβ (mul_pos hpos hδ2)

namespace SymbolicEconomy

variable (A : SymbolicEconomy)

/-! ## 5. The carrier is EXACTLY the affine family's carrier

Since plan item BJ4.3 (2026-10-08) `SymbolicEconomyF.carrierS` is the gain ball
alone, and §3 shows the ball is `SymbolicEconomy.carrierS` on the nose, so the
two carriers are definitionally equal. Until then the general carrier also
intersected a semiconcavity clause at modulus `Σ_V = 0`, and the identification
needed that a slope-pinned ball member is affine through the clip
(`carrierS_clip_semiconcave_zero`, kept below as a fact about the affine
carrier). -/

/-- A slope-pinned carrier member is affine through the clip on `[0,1]`, hence
concave there with modulus `0`. Affine-restricted. -/
theorem carrierS_clip_semiconcave_zero {V : Val} (hV : V ∈ A.carrierS) :
    SemiconcaveOnSet (fun z => V (Sanctions.clipS' z)) (Set.Icc (0 : ℝ) 1) 0 := by
  intro z₁ hz₁ z₂ hz₂ t ht0 ht1
  have hm : t * z₁ + (1 - t) * z₂ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hz₁.1, hz₂.1], by nlinarith [hz₁.2, hz₂.2]⟩
  have h1 := A.carrierS_diff hV hm hz₁
  have h2 := A.carrierS_diff hV hm hz₂
  have hzero : t * V (Sanctions.clipS' z₁) + (1 - t) * V (Sanctions.clipS' z₂)
      - V (Sanctions.clipS' (t * z₁ + (1 - t) * z₂)) = 0 := by
    linear_combination t * h1 + (1 - t) * h2
  show t * V (Sanctions.clipS' z₁) + (1 - t) * V (Sanctions.clipS' z₂)
      - V (Sanctions.clipS' (t * z₁ + (1 - t) * z₂))
    ≤ (0 : ℝ) / 2 * (t * (1 - t) * (z₁ - z₂) ^ 2)
  rw [hzero]
  norm_num

/-- Affine carrier membership is general-family carrier membership at `A.toF`
(definitionally, since plan item BJ4.3). Affine-restricted. -/
theorem mem_toF_carrierS {V : Val} (hV : V ∈ A.carrierS) : V ∈ A.toF.carrierS :=
  hV

/-- The converse (definitional since plan item BJ4.3). Affine-restricted. -/
theorem mem_carrierS_of_toF {V : Val} (hV : V ∈ A.toF.carrierS) : V ∈ A.carrierS :=
  hV

/-- **Nothing is lost.**  The general family's carrier, at the embedded affine
member, is identical to the affine family's carrier — so every theorem already
proved about `SymbolicEconomy.carrierS` applies unchanged, and every theorem
proved about `SymbolicEconomyF.carrierS` specialises to it. Since plan item
BJ4.3 the identity is `rfl` (both are the same gain ball). Affine-restricted. -/
theorem toF_carrierS : A.toF.carrierS = A.carrierS := rfl

theorem toF_carrierS_nonempty : A.toF.carrierS.Nonempty := A.toF.carrierS_nonempty

/-! ## 6. Consistency: the general machinery re-derives the affine results

Because the carriers coincide and `A.toF.toParams = A.toParams` definitionally,
the general-family theorems land back on exactly the affine family's
statements.

**Scope of the cross-check (plan item BJ4.3, 2026-10-08).** The general
family's Sender uniqueness is now the compliance-local `DAUOnI_on_cone`, from
strict monotonicity in the sanction (the carrier's lower slope, the sanction
lower chord and `hCorner`); it never substitutes the exact affine value, and
since the carriers coincide definitionally no extraction is used at all. So
`toF_DAUOnI_on_carrier` is an affine-extraction-free proof of uniqueness at
physical compliance. Uniqueness at every real compliance level
(`toF_DAU_on_carrier`) is the affine family's own slope-pinned result; the
general family's curvature route to it was deleted. -/

/-- **`SymbolicEconomy.DAU_on_carrier`, kept by name.** Sender argmax uniqueness
at every real compliance level on the affine carrier. Affine-restricted.

**Changed proof (plan item BJ4.3, 2026-10-08).** This used to re-derive the
statement through the general family's curvature route (`DAU_on_cone`), which
was deleted with the curvature block; it now reads the affine family's own
slope-pinned proof. The statement is unchanged. The general family's
independent route gives the compliance-local form, `toF_DAUOnI_on_carrier`. -/
theorem toF_DAU_on_carrier {V : Val} (hV : V ∈ A.carrierS) :
    A.toParams.DynamicArgmaxUnique V :=
  A.DAU_on_carrier hV

/-- **Compliance-local Sender uniqueness on the affine carrier, through the
general family** (plan item BJ4.3, 2026-10-08): `DAUOnI_on_cone` at `A.toF`,
whose `Params` and carrier are `A`'s definitionally. Strict monotonicity in the
sanction, with no exact affine value. Affine-restricted (the member is
`A.toF`). -/
theorem toF_DAUOnI_on_carrier {V : Val} (hV : V ∈ A.carrierS) :
    A.toParams.DynamicArgmaxUniqueOnI V :=
  A.toF.DAUOnI_on_cone (A.mem_toF_carrierS hV)

/-- **The carried margins survive the restatement.**  `SymbolicEconomyF`
prices them with band rates and `dlo` where `SymbolicEconomy` writes `1 − δ` and
`δ`. Re-deriving them through the general family reproduces the affine family's
own value-slope margins verbatim — a Rule-13 drift check on the restatement. -/
theorem toF_corner_margin : A.q + A.k - A.u₀ < A.βS * A.δ * A.KS :=
  A.toF.corner_margin

/-- **The affine Sender stage margin, kept by name.** `β_S·K_S·δ < m_S` with
`m_S = u₀ + r·x̄ − q·s̄`. Affine-restricted. Until plan item BJ4.1 (2026-10-07)
this re-derived the affine margin through `A.toF.sender_stage_margin`; the
general family no longer carries the Sender stage margin or the floor `s̄`, so
the statement is now read off the affine family's own field `A.hSMargin`
(`SymbolicEconomy.sender_stage_margin`). The statement is unchanged. -/
theorem toF_sender_stage_margin :
    A.βS * A.KS * A.δ < A.u₀ + A.r * A.xb - A.q * A.sbar :=
  A.sender_stage_margin

theorem toF_target_loss_margin : A.c - A.n * A.xb ≤ A.βT * A.gT * A.δ :=
  A.toF.target_loss_margin

/-- The general chord-based carrier invariance, specialised back to the affine
carrier. -/
theorem toF_carrierS_invariant {V W : Val} (hV : V ∈ A.carrierS)
    (himg : ∀ y : ↥(Sanctions.S : Set ℝ),
      W y = A.stageS0 + A.stageSlopeS * y.val
        + A.βS * V (Sanctions.clipS' (A.toParams.F y.val 1))) :
    W ∈ A.carrierS :=
  A.mem_carrierS_of_toF (A.toF.carrierS_invariant (A.mem_toF_carrierS hV) himg)

end SymbolicEconomy

/-! ## 7. The embedding is STRICT

The general family is not merely a restatement of the affine one: it contains
an economy whose realised recursion is a parabola, which no `SymbolicEconomy`
can produce. -/

/-- **`wobbleEconF` is outside the image of `toF`.** -/
theorem wobbleEconF_not_in_toF_image :
    ¬ ∃ A : SymbolicEconomy, wobbleEconF.F = A.toF.F := by
  rintro ⟨A, h⟩
  exact wobbleEconF_F_ne_affineF A.δ h

/-- ... and the abandoned equality route, which discharges every `toF` member's
band (`toF_cornerSectionTop`), fails there. -/
theorem toF_image_cornerSectionTop_but_wobble_not :
    (∀ A : SymbolicEconomy, ∃ γ : ℝ, CornerSectionTop A.toF.F γ)
      ∧ ¬ ∃ γ : ℝ, CornerSectionTop wobbleEconF.F γ :=
  ⟨fun A => ⟨1 - A.δ, A.toF_cornerSectionTop⟩, wobbleEconF_not_cornerSectionTop⟩

end -- noncomputable section

end Examples

end Sanctions

#print axioms Sanctions.Examples.SymbolicEconomy.toF
#print axioms Sanctions.Examples.SymbolicEconomy.toF_carrierS
#print axioms Sanctions.Examples.SymbolicEconomy.toF_gS_eq_KS
#print axioms Sanctions.Examples.curv_margin_lhs_pos_of_stage_curved
#print axioms Sanctions.Examples.SymbolicEconomy.toF_corner_margin
#print axioms Sanctions.Examples.SymbolicEconomy.toF_sender_stage_margin
#print axioms Sanctions.Examples.SymbolicEconomy.toF_target_loss_margin
#print axioms Sanctions.Examples.SymbolicEconomy.toF_DAU_on_carrier
#print axioms Sanctions.Examples.SymbolicEconomy.toF_DAUOnI_on_carrier
#print axioms Sanctions.Examples.SymbolicEconomy.toF_carrierS_invariant
#print axioms Sanctions.Examples.wobbleEconF_not_in_toF_image
