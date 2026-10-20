/-
Sanctions/Examples/PlacableSenderNetDefianceWitnesses.lean

**The net defiance condition holds where the loss-offset condition fails** (step 2, target
2a, 2026-10-10; Rule 9: existence certificates and nothing more).

Three members of the enriched subclass, each differing from a pinned member only in the
Target's discount factor:

* `collapseAffineFifth`: the rally-free tight affine member `collapseAffine b` at
  `β_T = 1/5` (`r = 0`, `σ_V = 0`, so `L_resp = 0`). ND holds at `g = g_T = 100/3`:
  `c − ℓ_lo μ/k_hi = 4 − 1 = 3 ≤ 10/3 = β_T d_lo g_T`.
* `affineFifthC`: the affine member `placableAffine` at `β_T = 1/5` (`r = 1/2`, `σ_V = 1`,
  `μ = 23/8`, `L_resp = 5/8`). ND holds at `g = g_eff = 3350/101`, where the balance (ND-b)
  binds: `73/24 ≤ 335/101`.
* `quadDiagQuarterC`: the non-affine member `placableQuadDiag` at `β_T = 1/4` (transition
  `quadDiagF`, `μ = 141/50`, `L_resp = 17/25`). ND holds at `g = g_eff = 8188/247`:
  `153/50 ≤ 4094/1235`.

At all three the loss-offset condition fails: `β_T d_lo g_T = 10/3 < 4 = c`. Every other
hypothesis of the four-case theorem under ND (`four_cell_net`) holds there (interiority,
placability, the sharp relief margin, zero-sanction neutrality, a nondecreasing response
through the flat transition), so at each member a full-defiance equilibrium exists in both
readings in which the Target looks ahead. This shows that the hypotheses of `four_cell_net`
are jointly satisfiable outside the loss-offset region, at an affine and at a non-affine
transition. It says nothing about how typical such members are, and nothing about
uniqueness of equilibrium: at the collapse member a non-defiance equilibrium can coexist
with the full-defiance one just above the threshold `2/11`.

Rule 22: `quadDiagF` is refuted against the affine law at every rate
(`placableQuadDiag_F_ne_affineF`). Rule 3: no field, no hypothesis; every statement is about
a concrete member.
-/
import Sanctions.Examples.PlacableSenderNetDefiance10
import Sanctions.Examples.PlacableSenderCollapseWitness

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Mechanism

noncomputable section

/-! ## 1. The rally-free tight affine member at `β_T = 1/5` -/

/-- The rally-free, tight-modulus affine member `collapseAffine b` at `β_T = 1/5`.
Scope: at the example economy only (not general). -/
abbrev collapseAffineFifth : ChordEconomyCs := collapseAffine (1 / 5) (by norm_num) (by norm_num)

/-- `g_T = 30/(1 − (1/5)(1/2)) = 100/3` at the member.
Scope: at the example economy only (not general). -/
theorem collapseAffineFifth_gT : collapseAffineFifth.gT = 100 / 3 := by
  norm_num [ChordEconomy.gT, PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord,
    collapseAffineCs, collapseAffineF, placableAffine]

/-- `μ = 3` at the member (`σ_V = 0`, `M_s = 0`).
Scope: at the example economy only (not general). -/
theorem collapseAffineFifth_mu : collapseAffineFifth.mu = 3 := by
  norm_num [ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, PlacableEconomyFcs.toChordCs,
    PlacableEconomyF.toChord, collapseAffineCs, collapseAffineF, placableAffine]

/-- `L_resp = 0` at the member (`r = 0`, `σ_V = σ_C = 0`, `M_mix = 0`).
Scope: at the example economy only (not general). -/
theorem collapseAffineFifth_Lresp : collapseAffineFifth.Lresp = 0 := by
  norm_num [ChordEconomyTwoSided.Lresp, ChordEconomy.plLresp, ChordEconomy.KS, chKS,
    ChordEconomyTwoSided.SigC, chSigC, PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord,
    collapseAffineCs, collapseAffineF, placableAffine]

/-- `M_tot = 3` at the member.
Scope: at the example economy only (not general). -/
theorem collapseAffineFifth_Mtot : collapseAffineFifth.Mtot = 3 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, collapseAffineCs, collapseAffineF,
    placableAffine]

/-- **The loss-offset condition fails at the member**: `β_T d_lo g_T = 10/3 < 4 = c`.
Scope: at the example economy only (not general). -/
theorem collapseAffineFifth_not_lossOffset : ¬ collapseAffineFifth.LossOffset := by
  unfold ChordEconomy.LossOffset
  rw [collapseAffineFifth_gT]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, collapseAffineCs,
    collapseAffineF, placableAffine]

/-- **ND holds at the member, at `g = g_T = 100/3`**: `c − ℓ_lo μ/k_hi = 3 ≤ 10/3`, and the
balance holds at `g_T` because `L_resp = 0`.
Scope: at the example economy only (not general). -/
theorem collapseAffineFifth_netDefianceAt : collapseAffineFifth.NetDefianceAt (100 / 3) := by
  rw [← collapseAffineFifth_gT]
  refine collapseAffineFifth.netDefianceAt_gT_of_Lresp_eq_zero collapseAffineFifth_Lresp ?_
  rw [collapseAffineFifth_mu, collapseAffineFifth_gT]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, collapseAffineCs,
    collapseAffineF, placableAffine]

/-- The sharp relief margin `ℓ_hi M_tot = 3 < 12 = k_lo p_lo` at the member.
Scope: at the example economy only (not general). -/
theorem collapseAffineFifth_relief :
    collapseAffineFifth.ℓhi * collapseAffineFifth.Mtot
      < collapseAffineFifth.klo * collapseAffineFifth.plo := by
  rw [collapseAffineFifth_Mtot]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, collapseAffineCs,
    collapseAffineF, placableAffine]

/-- Zero-sanction neutrality at the member.
Scope: at the example economy only (not general). -/
theorem collapseAffineFifth_neutral : collapseAffineFifth.ZeroSanctionNeutral :=
  (collapseAffineF (1 / 5) (by norm_num) (by norm_num)).toChord_zeroSanctionNeutral

/-- A nondecreasing response at the member (flat transition, `τ_x = 0`).
Scope: at the example economy only (not general). -/
theorem collapseAffineFifth_mono :
    MonotoneOn (collapseAffineFifth.responsePath collapseAffineFifth.VSstar) (Icc (0 : ℝ) 1) :=
  collapseAffineFifth.responsePath_monotoneOn_of_margin
    (collapseAffineFifth.margin_of_flat rfl rfl rfl)

/-! ## 2. The affine member at `β_T = 1/5` -/

/-- The affine member `placableAffineCs` at `β_T = 1/5` (every other field as the pinned
member).
Scope: at the example economy only (not general). -/
def placableAffineFifth : PlacableEconomyFcs :=
  { placableAffineCs with
    toPlacableEconomyF :=
      { placableAffine with βT := 1/5, hβT0 := by norm_num, hβT1 := by norm_num } }

/-- The member as an enriched chord economy.
Scope: at the example economy only (not general). -/
abbrev affineFifthC : ChordEconomyCs := placableAffineFifth.toChordCs

/-- `g_T = 100/3` at the member.
Scope: at the example economy only (not general). -/
theorem affineFifthC_gT : affineFifthC.gT = 100 / 3 := by
  norm_num [ChordEconomy.gT, PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord,
    placableAffineFifth, placableAffineCs, placableAffine]

/-- `μ = 23/8` at the member.
Scope: at the example economy only (not general). -/
theorem affineFifthC_mu : affineFifthC.mu = 23 / 8 := by
  norm_num [ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, PlacableEconomyFcs.toChordCs,
    PlacableEconomyF.toChord, placableAffineFifth, placableAffineCs, placableAffine]

/-- `L_resp = 5/8` at the member.
Scope: at the example economy only (not general). -/
theorem affineFifthC_Lresp : affineFifthC.Lresp = 5 / 8 := by
  norm_num [ChordEconomyTwoSided.Lresp, ChordEconomy.plLresp, ChordEconomy.KS, chKS,
    ChordEconomyTwoSided.SigC, chSigC, PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord,
    placableAffineFifth, placableAffineCs, placableAffine]

/-- `M_tot = 3` at the member.
Scope: at the example economy only (not general). -/
theorem affineFifthC_Mtot : affineFifthC.Mtot = 3 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineFifth,
    placableAffineCs, placableAffine]

/-- **The loss-offset condition fails at the member**: `β_T d_lo g_T = 10/3 < 4 = c`.
Scope: at the example economy only (not general). -/
theorem affineFifthC_not_lossOffset : ¬ affineFifthC.LossOffset := by
  unfold ChordEconomy.LossOffset
  rw [affineFifthC_gT]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineFifth,
    placableAffineCs, placableAffine]

/-- **ND holds at the member, at `g = 3350/101`** (`= g_eff < g_T`): `73/24 ≤ 335/101`, and
the balance binds, `(3350/101)(9/10) + (69/101)(5/23) = 30`.
Scope: at the example economy only (not general). -/
theorem affineFifthC_netDefianceAt : affineFifthC.NetDefianceAt (3350 / 101) := by
  have hθ : (0 : ℝ) ≤ affineFifthC.c - affineFifthC.β_T * affineFifthC.dlo * (3350 / 101) := by
    norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineFifth,
      placableAffineCs, placableAffine]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [affineFifthC_mu]
    norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineFifth,
      placableAffineCs, placableAffine]
  · rw [max_eq_right hθ, affineFifthC_Lresp, affineFifthC_mu]
    norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineFifth,
      placableAffineCs, placableAffine]

/-- Interiority at the member (`A = 2 < 3 = q`).
Scope: at the example economy only (not general). -/
theorem affineFifthC_interior : affineFifthC.Interior := by
  change placableAffineFifth.toPlacableEconomyF.Interior
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableAffineFifth, placableAffineCs, placableAffine]

/-- Placability at the member (`A = 2 ≤ 3 = k`).
Scope: at the example economy only (not general). -/
theorem affineFifthC_placable : affineFifthC.Placable := by
  change placableAffineFifth.toPlacableEconomyF.Placable
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableAffineFifth, placableAffineCs, placableAffine]

/-- The sharp relief margin `3 < 12` at the member.
Scope: at the example economy only (not general). -/
theorem affineFifthC_relief :
    affineFifthC.ℓhi * affineFifthC.Mtot < affineFifthC.klo * affineFifthC.plo := by
  rw [affineFifthC_Mtot]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineFifth,
    placableAffineCs, placableAffine]

/-- Zero-sanction neutrality at the member.
Scope: at the example economy only (not general). -/
theorem affineFifthC_neutral : affineFifthC.ZeroSanctionNeutral :=
  placableAffineFifth.toPlacableEconomyF.toChord_zeroSanctionNeutral

/-- A nondecreasing response at the member (flat transition, `τ_x = 0`).
Scope: at the example economy only (not general). -/
theorem affineFifthC_mono :
    MonotoneOn (affineFifthC.responsePath affineFifthC.VSstar) (Icc (0 : ℝ) 1) :=
  affineFifthC.responsePath_monotoneOn_of_margin (affineFifthC.margin_of_flat rfl rfl rfl)

/-! ## 3. The non-affine member at `β_T = 1/4` -/

/-- The non-affine member `placableQuadDiagCs` at `β_T = 1/4` (every other field as the
pinned member).
Scope: at the example economy only (not general). -/
def placableQuadDiagQuarter : PlacableEconomyFcs :=
  { placableQuadDiagCs with
    toPlacableEconomyF :=
      { placableQuadDiag with βT := 1/4, hβT0 := by norm_num, hβT1 := by norm_num } }

/-- The member as an enriched chord economy.
Scope: at the example economy only (not general). -/
abbrev quadDiagQuarterC : ChordEconomyCs := placableQuadDiagQuarter.toChordCs

/-- `g_T = 30/(1 − (1/4)(2/5)) = 100/3` at the member.
Scope: at the example economy only (not general). -/
theorem quadDiagQuarterC_gT : quadDiagQuarterC.gT = 100 / 3 := by
  norm_num [ChordEconomy.gT, PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord,
    placableQuadDiagQuarter, placableQuadDiagCs, placableQuadDiag]

/-- `μ = 141/50` at the member.
Scope: at the example economy only (not general). -/
theorem quadDiagQuarterC_mu : quadDiagQuarterC.mu = 141 / 50 := by
  norm_num [ChordEconomy.mu, plMu, ChordEconomy.KS, chKS, PlacableEconomyFcs.toChordCs,
    PlacableEconomyF.toChord, placableQuadDiagQuarter, placableQuadDiagCs, placableQuadDiag]

/-- `L_resp = 17/25` at the member.
Scope: at the example economy only (not general). -/
theorem quadDiagQuarterC_Lresp : quadDiagQuarterC.Lresp = 17 / 25 := by
  norm_num [ChordEconomyTwoSided.Lresp, ChordEconomy.plLresp, ChordEconomy.KS, chKS,
    ChordEconomyTwoSided.SigC, chSigC, PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord,
    placableQuadDiagQuarter, placableQuadDiagCs, placableQuadDiag]

/-- `M_tot = 45/14` at the member.
Scope: at the example economy only (not general). -/
theorem quadDiagQuarterC_Mtot : quadDiagQuarterC.Mtot = 45 / 14 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagQuarter,
    placableQuadDiagCs, placableQuadDiag]

/-- **The loss-offset condition fails at the member**: `β_T d_lo g_T = 10/3 < 4 = c`.
Scope: at the example economy only (not general). -/
theorem quadDiagQuarterC_not_lossOffset : ¬ quadDiagQuarterC.LossOffset := by
  unfold ChordEconomy.LossOffset
  rw [quadDiagQuarterC_gT]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagQuarter,
    placableQuadDiagCs, placableQuadDiag]

/-- **ND holds at the member, at `g = 8188/247`** (`= g_eff < g_T`): `153/50 ≤ 4094/1235`,
and the balance binds, `(8188/247)(9/10) + (846/1235)(34/141) = 30`.
Scope: at the example economy only (not general). -/
theorem quadDiagQuarterC_netDefianceAt : quadDiagQuarterC.NetDefianceAt (8188 / 247) := by
  have hθ : (0 : ℝ)
      ≤ quadDiagQuarterC.c - quadDiagQuarterC.β_T * quadDiagQuarterC.dlo * (8188 / 247) := by
    norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagQuarter,
      placableQuadDiagCs, placableQuadDiag]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [quadDiagQuarterC_mu]
    norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagQuarter,
      placableQuadDiagCs, placableQuadDiag]
  · rw [max_eq_right hθ, quadDiagQuarterC_Lresp, quadDiagQuarterC_mu]
    norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagQuarter,
      placableQuadDiagCs, placableQuadDiag]

/-- Interiority at the member.
Scope: at the example economy only (not general). -/
theorem quadDiagQuarterC_interior : quadDiagQuarterC.Interior := by
  change placableQuadDiagQuarter.toPlacableEconomyF.Interior
  unfold PlacableEconomyF.Interior plAppetite plKS
  norm_num [placableQuadDiagQuarter, placableQuadDiagCs, placableQuadDiag]

/-- Placability at the member.
Scope: at the example economy only (not general). -/
theorem quadDiagQuarterC_placable : quadDiagQuarterC.Placable := by
  change placableQuadDiagQuarter.toPlacableEconomyF.Placable
  unfold PlacableEconomyF.Placable plAppetite plKS
  norm_num [placableQuadDiagQuarter, placableQuadDiagCs, placableQuadDiag]

/-- The sharp relief margin `45/14 < 12` at the member.
Scope: at the example economy only (not general). -/
theorem quadDiagQuarterC_relief :
    quadDiagQuarterC.ℓhi * quadDiagQuarterC.Mtot < quadDiagQuarterC.klo * quadDiagQuarterC.plo := by
  rw [quadDiagQuarterC_Mtot]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagQuarter,
    placableQuadDiagCs, placableQuadDiag]

/-- Zero-sanction neutrality at the member.
Scope: at the example economy only (not general). -/
theorem quadDiagQuarterC_neutral : quadDiagQuarterC.ZeroSanctionNeutral :=
  placableQuadDiagQuarter.toPlacableEconomyF.toChord_zeroSanctionNeutral

/-- A nondecreasing response at the member (flat transition, `τ_x = 0`, `M_cx = M_mix = 0`).
Scope: at the example economy only (not general). -/
theorem quadDiagQuarterC_mono :
    MonotoneOn (quadDiagQuarterC.responsePath quadDiagQuarterC.VSstar) (Icc (0 : ℝ) 1) :=
  quadDiagQuarterC.responsePath_monotoneOn_of_margin
    (quadDiagQuarterC.margin_of_flat rfl rfl rfl)

/-! ## 4. The existence certificates -/

/-- **ND without the loss-offset condition, with full-defiance equilibria in both
forward-looking-Target readings** (Rule 9: an existence certificate). There is an enriched
chord economy satisfying every hypothesis of `four_cell_net` (interiority, placability, a
nondecreasing response, the sharp relief margin, zero-sanction neutrality and ND) at which
the loss-offset condition fails, and at which full-defiance equilibria of the Target-only
reading and of the forward-looking reading exist. The member is `collapseAffineFifth`.
Scope: at the example economy only (not general). -/
theorem exists_netDefiance_not_lossOffset :
    ∃ E : ChordEconomyCs, E.Interior ∧ E.Placable ∧
      MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1) ∧
      E.ℓhi * E.Mtot < E.klo * E.plo ∧ E.ZeroSanctionNeutral ∧ E.NetDefiance ∧
      ¬ E.LossOffset ∧
      (∃ Eq : E.toParams.RegimeEquilibrium ContinuationProfile.p10,
        ∀ x ∈ Sanctions.I, Eq.α x = 0) ∧
      (∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0) :=
  ⟨collapseAffineFifth, collapseAffine_interior _ _, collapseAffine_placable _ _,
    collapseAffineFifth_mono, collapseAffineFifth_relief, collapseAffineFifth_neutral,
    ⟨_, collapseAffineFifth_netDefianceAt⟩, collapseAffineFifth_not_lossOffset,
    collapseAffineFifth.exists_targetOnly_defiance_equilibrium_iff.2
      (collapseAffineFifth.defianceBestReply10_of_netDefianceStage
        (collapseAffineFifth.netDefianceStage_of_netDefiance
          ⟨_, collapseAffineFifth_netDefianceAt⟩)),
    collapseAffineFifth.exists_defiance_equilibrium_of_netDefiance collapseAffineFifth_mono
      ⟨_, collapseAffineFifth_netDefianceAt⟩⟩

/-- **The same off the affine law and with a binding balance** (Rule 9, Rule 22): the
non-affine member `quadDiagQuarterC` (transition `quadDiagF`, `L_resp > 0`) satisfies every
hypothesis of `four_cell_net`, fails the loss-offset condition, and carries full-defiance
equilibria in both forward-looking-Target readings.
Scope: at the example economy only (not general). -/
theorem exists_netDefiance_not_lossOffset_nonaffine :
    ∃ E : ChordEconomyCs, E.F ≠ AbstractGame.affineF E.δ ∧ E.Interior ∧ E.Placable ∧
      MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1) ∧
      E.ℓhi * E.Mtot < E.klo * E.plo ∧ E.ZeroSanctionNeutral ∧ E.NetDefiance ∧
      ¬ E.LossOffset ∧
      (∃ Eq : E.toParams.RegimeEquilibrium ContinuationProfile.p10,
        ∀ x ∈ Sanctions.I, Eq.α x = 0) ∧
      (∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0) :=
  ⟨quadDiagQuarterC, placableQuadDiag_F_ne_affineF _, quadDiagQuarterC_interior,
    quadDiagQuarterC_placable, quadDiagQuarterC_mono, quadDiagQuarterC_relief,
    quadDiagQuarterC_neutral, ⟨_, quadDiagQuarterC_netDefianceAt⟩,
    quadDiagQuarterC_not_lossOffset,
    quadDiagQuarterC.exists_targetOnly_defiance_equilibrium_iff.2
      (quadDiagQuarterC.defianceBestReply10_of_netDefianceStage
        (quadDiagQuarterC.netDefianceStage_of_netDefiance ⟨_, quadDiagQuarterC_netDefianceAt⟩)),
    quadDiagQuarterC.exists_defiance_equilibrium_of_netDefiance quadDiagQuarterC_mono
      ⟨_, quadDiagQuarterC_netDefianceAt⟩⟩

/-- **The affine member with `r = 1/2` at `β_T = 1/5`** (Rule 9): every hypothesis of
`four_cell_net`, the loss-offset condition failing, and full-defiance equilibria in both
forward-looking-Target readings.
Scope: at the example economy only (not general). -/
theorem affineFifthC_netDefiance_not_lossOffset :
    affineFifthC.Interior ∧ affineFifthC.Placable ∧
      MonotoneOn (affineFifthC.responsePath affineFifthC.VSstar) (Icc (0 : ℝ) 1) ∧
      affineFifthC.ℓhi * affineFifthC.Mtot < affineFifthC.klo * affineFifthC.plo ∧
      affineFifthC.ZeroSanctionNeutral ∧ affineFifthC.NetDefiance ∧ ¬ affineFifthC.LossOffset ∧
      (∃ Eq : affineFifthC.toParams.RegimeEquilibrium ContinuationProfile.p10,
        ∀ x ∈ Sanctions.I, Eq.α x = 0) ∧
      (∃ Eq : affineFifthC.toParams.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Sanctions.I, Eq.α x = 0) :=
  ⟨affineFifthC_interior, affineFifthC_placable, affineFifthC_mono, affineFifthC_relief,
    affineFifthC_neutral, ⟨_, affineFifthC_netDefianceAt⟩, affineFifthC_not_lossOffset,
    affineFifthC.exists_targetOnly_defiance_equilibrium_iff.2
      (affineFifthC.defianceBestReply10_of_netDefianceStage
        (affineFifthC.netDefianceStage_of_netDefiance ⟨_, affineFifthC_netDefianceAt⟩)),
    affineFifthC.exists_defiance_equilibrium_of_netDefiance affineFifthC_mono
      ⟨_, affineFifthC_netDefianceAt⟩⟩

end

end Examples
end Sanctions
