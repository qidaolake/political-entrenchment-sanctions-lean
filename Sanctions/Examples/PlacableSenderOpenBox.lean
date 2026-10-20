/-
Sanctions/Examples/PlacableSenderOpenBox.lean

**Open-set robustness of the placable-Sender family at its affine member**:
every coefficient vector within `1/20` of `placableAffine`'s nine payoff
coefficients — with the rally softening `n` kept in its sign domain, so the
box is a neighbourhood *relative to* `n ≥ 0` and contains the full-dimensional
open sub-box `n > 0` — is an admissible member with the same affine transition
and the same discounts, on which the rally margin is vacuous, both continuation
channels are active at the composed equilibrium, the two readings separate,
the closed loop is a contraction with one globally attracting steady state,
and (doc 65) the relief margin holds, so all four cells are ordered.

This is the "robust noncorner behavioural class" of doc 40's third choice,
stated as a theorem over the box rather than as a Rule 9C numerical remark:
the family's defining inequalities are strict where they need to be and the
member sits at positive distance from every one of them. The box is a product
of closed intervals of radius `1/20`; the open box of the same radius is
inside it, so the statement is an open-set statement.

Rule 9: the box is a set of witnesses, so it licenses existence on every point
of the box and nothing about points outside it; Rule 22: affine-restricted and
marked so — the transition is `affineF (1/2)` throughout, and the discounts are
fixed, so this is not an open-set statement in function space. Rule 3: no new
assumption; the fields are those of `PlacableEconomyF`, and the subclass
member `placableBoxCs` carries the modulus `0`.

**Quadratic–linear family only** (doc 104, sign-off M6). The box is a box of the
family's coefficients, so it is an open-set statement in those coefficients and
not in the chord economy's rates. Its points' results are read through
`toChord`/`toChordCs`, and the closed-form cells are the family's.

Renovation item BJ2.3 (2026-10-07): the family no longer carries the interiority and
stage relief fields, only the sign field `hcn : n < c`. Their proofs on the box moved,
unchanged, to the lemmas `placableBox_interior` and `placableBox_stageRelief`; the
results below read them through the chord forms `placableBox_chordInterior` and
`placableBox_chordLossOffset`, with unchanged statements.
-/
import Sanctions.Examples.PlacableSenderWitnesses
import Sanctions.Examples.PlacableSenderRegime10
import Sanctions.Examples.PlacableSenderRegime01

namespace Sanctions
namespace Examples

open Set Filter Topology AbstractGame

noncomputable section

/-- Nine payoff coefficients within `1/20` of the affine member's. -/
structure BoxCoeffs where
  q : ℝ
  u₀ : ℝ
  k : ℝ
  r : ℝ
  w : ℝ
  ℓ : ℝ
  c : ℝ
  n : ℝ
  v : ℝ
  hq : q ∈ Icc (59/20 : ℝ) (61/20)
  hu₀ : u₀ ∈ Icc (19/20 : ℝ) (21/20)
  hk : k ∈ Icc (59/20 : ℝ) (61/20)
  hr : r ∈ Icc (9/20 : ℝ) (11/20)
  hw : w ∈ Icc (19/20 : ℝ) (21/20)
  hℓ : ℓ ∈ Icc (19/20 : ℝ) (21/20)
  hc : c ∈ Icc (79/20 : ℝ) (81/20)
  hn : n ∈ Icc (0 : ℝ) (1/20)
  hv : v ∈ Icc (599/20 : ℝ) (601/20)

/-- The affine member's coefficients are the centre of the box (non-vacuity). -/
def BoxCoeffs.centre : BoxCoeffs :=
  ⟨3, 1, 3, 1/2, 1, 1, 4, 0, 30, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The member at a box point**: the affine member with its nine payoff
coefficients replaced. Every margin is re-proved at the box's worst corner. -/
def placableBox (B : BoxCoeffs) : PlacableEconomyF :=
  { placableAffine with
    q := B.q
    u₀ := B.u₀
    k := B.k
    r := B.r
    w := B.w
    ℓ := B.ℓ
    c := B.c
    n := B.n
    v := B.v
    hu₀ := by linarith [B.hu₀.1]
    hr := by linarith [B.hr.1]
    hw := by linarith [B.hw.1]
    hℓ := by linarith [B.hℓ.1]
    hn := B.hn.1
    hCurv := by
      change (1/2 : ℝ) * (1 * (1/2) ^ 2 + plKS (1/2) (1/2) B.r B.w * 0) < B.q
      norm_num
      linarith [B.hq.1]
    hSigV := by
      change plSigImg (1/2) B.q B.r 1 (1/2) (1/2) (plKS (1/2) (1/2) B.r B.w) 0 0 0 ≤ 1
      unfold plSigImg plSig plRho plMu
      norm_num
      have hden : (0 : ℝ) < B.q - 1/8 := by linarith [B.hq.1]
      have hfrac : (B.r + 1/8) ^ 2 / (B.q - 1/8) ≤ 7/8 := by
        rw [div_le_iff₀ hden]
        nlinarith [B.hr.1, B.hr.2, B.hq.1]
      linarith
    hk := by linarith [B.hk.1]
    hv := by linarith [B.hv.1]
    hcn := by linarith [B.hn.2, B.hc.1] }

/-- **Placability holds on the whole box** (a hypothesis of the family since round AP). -/
theorem placableBox_placable (B : BoxCoeffs) : (placableBox B).Placable := by
  change plAppetite (1/2) B.u₀ B.r (plKS (1/2) (1/2) B.r B.w) (1/2) ≤ B.k
  unfold plAppetite plKS
  norm_num
  linarith [B.hu₀.2, B.hr.2, B.hw.2, B.hk.1]

/-- **The loss-offset margin holds on the whole box** (a hypothesis since round AP). -/
theorem placableBox_lossOffset (B : BoxCoeffs) : (placableBox B).LossOffset := by
  change B.c ≤ (1/2) * (1/2) * plGTn (1/2) (1/2) B.v B.n B.u₀ B.q
  unfold plGTn
  have hnn : 0 ≤ B.n * B.u₀ / B.q :=
    div_nonneg (mul_nonneg B.hn.1 (by linarith [B.hu₀.1])) (by linarith [B.hq.1])
  norm_num
  linarith [B.hc.2, B.hv.1, hnn]

/-- **Interiority holds on the whole box** (a field of the family until renovation item
BJ2.3, 2026-10-07, now a hypothesis; the proof is the former field's). Affine-restricted. -/
theorem placableBox_interior (B : BoxCoeffs) : (placableBox B).Interior := by
  change plAppetite (1/2) B.u₀ B.r (plKS (1/2) (1/2) B.r B.w) (1/2) < B.q
  unfold plAppetite plKS
  norm_num
  linarith [B.hu₀.2, B.hr.2, B.hw.2, B.hq.1]

/-- **The stage relief margin holds on the whole box** (a field of the family until
renovation item BJ2.3, now a hypothesis; the proof is the former field's).
Affine-restricted. -/
theorem placableBox_stageRelief (B : BoxCoeffs) : (placableBox B).StageRelief := by
  change B.ℓ * B.q < B.k * (B.c - B.n)
  have h1 : B.ℓ * B.q ≤ (21/20) * (61/20) :=
    mul_le_mul B.hℓ.2 B.hq.2 (by linarith [B.hq.1]) (by norm_num)
  have h2 : (59/20 : ℝ) * (79/20 - 1/20) ≤ B.k * (B.c - B.n) :=
    mul_le_mul B.hk.1 (by linarith [B.hc.1, B.hn.2]) (by norm_num) (by linarith [B.hk.1])
  linarith

/-- Interiority on the whole box in the chord form (renovation item BJ2.3).
Affine-restricted. -/
theorem placableBox_chordInterior (B : BoxCoeffs) : (placableBox B).toChord.Interior :=
  (placableBox B).toChord_interior (placableBox_interior B)

/-- The loss-offset margin on the whole box in the chord form; the floor condition
`u₀ ≤ q` comes from interiority (renovation item BJ2.3). Affine-restricted. -/
theorem placableBox_chordLossOffset (B : BoxCoeffs) : (placableBox B).toChord.LossOffset :=
  (placableBox B).toChord_lossOffset ((placableBox B).u₀_le_q (placableBox_interior B))
    (placableBox_lossOffset B)

theorem placableBox_F (B : BoxCoeffs) : (placableBox B).F = AbstractGame.affineF (1/2) := rfl
theorem placableBox_q (B : BoxCoeffs) : (placableBox B).q = B.q := rfl
theorem placableBox_Mcx (B : BoxCoeffs) : (placableBox B).Mcx = 0 := rfl
theorem placableBox_Mmix (B : BoxCoeffs) : (placableBox B).Mmix = 0 := rfl

/-- **The rally margin is vacuous on the whole box** (flat transition). -/
theorem placableBox_margin (B : BoxCoeffs) :
    (placableBox B).βS * ((placableBox B).SigC * (placableBox B).ghi * (placableBox B).dhi
      + ((placableBox B).KS + 2 * (placableBox B).SigC) * (placableBox B).Mmix)
      ≤ (placableBox B).r :=
  (placableBox B).familyMargin_of_flat rfl rfl

theorem placableBox_SigC (B : BoxCoeffs) : (placableBox B).toChord.SigC = 0 := by
  rw [PlacableEconomyF.toChord_SigC]
  change plSigC (1/2) (placableBox B).KS 0 (1/2) = 0
  unfold plSigC; ring

/-- **The closed loop contracts on the whole box**: `L_loop = 1/2 + 2(r + 1/8)/(q − 1/8) < 1`. -/
theorem placableBox_Lloop_lt_one (B : BoxCoeffs) : (placableBox B).toChord.Lloop < 1 := by
  change (1/2 : ℝ) + (1/2) * (4 * (placableBox B).toChord.Lresp / (placableBox B).toChord.mu) < 1
  have hL : (placableBox B).toChord.Lresp = B.r + 1/8 := by
    unfold ChordEconomyTwoSided.Lresp ChordEconomy.plLresp
    rw [placableBox_SigC]
    show B.r + (1/2) * (max 1 0 * (1/2) * (1/2) + ((placableBox B).toChord.KS + 2 * max 1 0) * 0)
      = B.r + 1/8
    norm_num
  have hμ : (placableBox B).toChord.mu = B.q - 1/8 := by
    change plMu (1/2) B.q 1 (1/2) (placableBox B).toChord.KS 0 = B.q - 1/8
    unfold plMu; ring
  rw [hL, hμ]
  have hden : (0 : ℝ) < B.q - 1/8 := by linarith [B.hq.1]
  have hfrac : 4 * (B.r + 1/8) / (B.q - 1/8) < 1 := by
    rw [div_lt_one hden]
    linarith [B.hr.2, B.hq.1]
  linarith

/-- The box member in the enriched subclass: sanction-section modulus `0`. -/
def placableBoxCs (B : BoxCoeffs) : PlacableEconomyFcs where
  toPlacableEconomyF := placableBox B
  Mcs := 0
  hMcs0 := by norm_num
  hFcs := affineF_half_cs

/-- On the box both curvature moduli vanish, so the Sender objective's
curvature ceiling is the cost curvature itself. -/
theorem placableBoxCs_Mtot (B : BoxCoeffs) : (placableBoxCs B).toChordCs.Mtot = B.q := by
  unfold ChordEconomyCs.Mtot
  have hSigC : (placableBoxCs B).toChordCs.SigC = 0 := placableBox_SigC B
  have hM : (placableBoxCs B).toChordCs.Mcs = 0 := rfl
  have hq : (placableBoxCs B).toChordCs.Qbar = B.q := rfl
  rw [hSigC, hM, hq]; ring

/-- **The relief margin holds on the whole box**: `2ℓ·max(q, k) ≤ 1281/200 <
2301/200 ≤ k(c − n)` at the worst corners (exact arithmetic, doc 65). -/
theorem placableBox_relief (B : BoxCoeffs) :
    2 * (placableBoxCs B).toChordCs.ℓhi
        * max (placableBoxCs B).toChordCs.Mtot (placableBoxCs B).toChordCs.klo
      < (placableBoxCs B).toChordCs.klo * (placableBoxCs B).toChordCs.plo := by
  rw [placableBoxCs_Mtot]
  change 2 * B.ℓ * max B.q B.k < B.k * (B.c - B.n)
  have hmax : max B.q B.k ≤ 61/20 := max_le B.hq.2 B.hk.2
  have hmax0 : 0 ≤ max B.q B.k := le_trans (by linarith [B.hq.1]) (le_max_left B.q B.k)
  have h1 : 2 * B.ℓ * max B.q B.k ≤ 2 * (21/20) * (61/20) :=
    mul_le_mul (by linarith [B.hℓ.2]) hmax hmax0 (by norm_num)
  have h2 : (59/20 : ℝ) * (79/20 - 1/20) ≤ B.k * (B.c - B.n) :=
    mul_le_mul B.hk.1 (by linarith [B.hc.1, B.hn.2]) (by norm_num) (by linarith [B.hk.1])
  linarith

/-- **The four cells on the whole box** (doc 65), in closed form: wash-out under
`00` and `01`, convergence to `u₀/(q − r)` under `10`, to a strictly higher state
under `11`, at every point of the box. -/
theorem placableBox_four_cells (B : BoxCoeffs) :
    (∀ x₀ ∈ Sanctions.I, Tendsto (((placableBox B).toChord.myopicPath
        (placableBox_chordInterior B)
        ((placableBox B).toChord_stageRelief (placableBox_stageRelief B))
      ((placableBox B).toChord_placable (placableBox_placable B))) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto (((placableBoxCs B).toChordCs.senderOnlyPath'
        (placableBox_chordInterior B)
      ((placableBox B).toChord_placable (placableBox_placable B))
      ((placableBoxCs B).toChordCs.reliefSharp_of_relief (placableBox_relief B))
      (placableBox B).toChord_zeroSanctionNeutral) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableBox B).toChord.targetOnlyPath
      (placableBox_chordLossOffset B) x₀) atTop
      (𝓝 (placableBox B).steady10)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I,
      (placableBox B).toChord.responsePath (placableBox B).toChord.VSstar z = z ∧
      (placableBox B).steady10 < z ∧
      Tendsto ((placableBox B).toChord.dynamicPath
        (placableBox_chordLossOffset B)
        ((placableBox B).toChord_margin (placableBox_margin B)) x₀) atTop (𝓝 z)) ∧
    0 < (placableBox B).steady10 :=
  (placableBoxCs B).four_cell_closedForm (placableBox_interior B) (placableBox_lossOffset B)
    (placableBox_placable B) (placableBox_margin B)
    ((placableBoxCs B).toChordCs.reliefSharp_of_relief (placableBox_relief B))

/-- Every point of the box satisfies the stage flip `ℓq < u₀(c − n)`, the
hypothesis of the activation results since round Q2. -/
theorem placableBox_flip (B : BoxCoeffs) :
    (placableBox B).ℓ * (placableBox B).q
      < (placableBox B).u₀ * ((placableBox B).c - (placableBox B).n) := by
  change B.ℓ * B.q < B.u₀ * (B.c - B.n)
  have h1 : B.ℓ * B.q ≤ (21/20) * (61/20) :=
    mul_le_mul B.hℓ.2 B.hq.2 (by linarith [B.hq.1]) (by norm_num)
  have h2 : (19/20 : ℝ) * (79/20 - 1/20) ≤ B.u₀ * (B.c - B.n) :=
    mul_le_mul B.hu₀.1 (by linarith [B.hc.1, B.hn.2]) (by norm_num) (by linarith [B.hu₀.1])
  linarith

/-- **Open-set robustness.** At every point of the box: both continuation
channels change behaviour at the composed equilibrium; the Target-only reading
converges to `u₀/(q − r)`; the forward-looking closed loop has one globally
attracting steady state; and the Sender-only reading washes out, so all four
cells (`placableBox_four_cells`) are ordered on the box. -/
theorem placableBox_robust (B : BoxCoeffs) :
    (∀ x ∈ Sanctions.I,
      (placableBox B).toChord.toParams.ContinuationChangesSenderChoiceAt
        (((placableBox B).toChord.equilibriumTop_of_flat
          (placableBox_chordLossOffset B)) rfl rfl rfl).V_S x
        ((((placableBox B).toChord.equilibriumTop_of_flat
          (placableBox_chordLossOffset B)) rfl rfl rfl).α x)
      ∧ (placableBox B).toChord.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => (placableBox B).toChord.response
            (((placableBox B).toChord.equilibriumTop_of_flat
              (placableBox_chordLossOffset B)) rfl rfl rfl).V_S y b)
          (((placableBox B).toChord.equilibriumTop_of_flat
            (placableBox_chordLossOffset B)) rfl rfl rfl).V_T x) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableBox B).toChord.targetOnlyPath
      (placableBox_chordLossOffset B) x₀) atTop
      (𝓝 (placableBox B).steady10)) ∧
    (∃ z ∈ Sanctions.I, (placableBox B).toChord.closedLoop z = z ∧
      (∀ y ∈ Sanctions.I, (placableBox B).toChord.closedLoop y = y → y = z) ∧
      ∀ x ∈ Sanctions.I, Tendsto (fun n => (placableBox B).toChord.closedLoop^[n] x) atTop (𝓝 z)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto (((placableBoxCs B).toChordCs.senderOnlyPath
        (placableBox_chordInterior B)
      ((placableBox B).toChord_placable (placableBox_placable B)) (placableBox_relief B)
      (placableBox B).toChord_zeroSanctionNeutral) x₀) atTop (𝓝 0)) :=
  ⟨(placableBox B).toChord.both_channels_active_of_flat
      ((placableBox B).toChord.uhi_lt_q (placableBox_chordInterior B))
      (placableBox_chordLossOffset B)
      ((placableBox B).toChord_placable (placableBox_placable B))
      (((placableBox B).toChord_flip_iff ((placableBox B).u₀_le_q (placableBox_interior B))).2
        (placableBox_flip B)) rfl rfl rfl,
   fun _ hx₀ => (placableBox B).targetOnlyPath_tendsto (placableBox_interior B)
      (placableBox_lossOffset B) hx₀,
   (placableBox B).toChord.closedLoop_unique_attracting_of_lt_one (placableBox_Lloop_lt_one B),
   fun _ hx₀ => (placableBoxCs B).toChordCs.senderOnlyPath_tendsto_zero
      (placableBox_chordInterior B)
      ((placableBox B).toChord_placable (placableBox_placable B)) (placableBox_relief B)
      (placableBox B).toChord_zeroSanctionNeutral hx₀⟩

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.placableBox
#print axioms Sanctions.Examples.placableBox_Lloop_lt_one
#print axioms Sanctions.Examples.placableBox_robust
#print axioms Sanctions.Examples.placableBox_relief
#print axioms Sanctions.Examples.placableBox_four_cells

end Examples
end Sanctions
