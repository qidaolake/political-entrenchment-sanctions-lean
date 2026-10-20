/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Theory.Bellman.SenderLowerSlopeCone
import Sanctions.Foundations.ReflectedArgmaxShift

/-!
# How fast the Sender's value can fall: the mirror of the lower-slope cone

Step 2, target 2b (2026-10-10): the sign of the Sender's stake as a parameter.

`SenderLowerSlopeCone.lean` bounds the Sender's value from below: under a joint state chord
it rises at least at rate `g`. This file proves the mirror bound: under the mirrored chord
the value **falls** at least at rate `h`. No new predicate is introduced. "`V` falls at rate
at least `h`" is written `LowerSlopeOnValueOn (-V) (Icc 0 1) h`, so closedness comes from
`lowerSlopeCone_isClosed` composed with negation.

## What is proved

* `bellmanS_BCF_preserves_negLowerSlope_generalF` (N3) — the Sender Bellman operator keeps
  the set of values falling at rate at least `h`, under the joint chord
  `ΔU_S − β_S·h·ΔF ≤ −h·Δy` along the Target policy. Sign-agnostic in `h`.
* `V_S_negLowerSlope_generalF` (N4) — hence the constructed Sender value `p.V_S α hα` (the
  Banach fixed point) falls at rate at least `h` (Rule 15: trapped, not hypothesised).
* `negJointChord_of_stateChords` (N5) and `V_S_negLowerSlope_of_stateChords` — if the
  composed stage payoff falls at rate at least `w ≥ 0` at every sanction and the transition
  rises in the state at rate at least `gl` with `β_S·gl < 1`, the joint chord holds with
  `h = w/(1 − β_S·gl)`, so the value falls at that rate.
* `V_S_lowerSlope_of_stateLowerChords` — the companion bound from the other side: if the
  composed stage payoff falls at most at rate `w ≥ 0` and the transition rises in the state at
  most at rate `gh` with `β_S·gh < 1`, the value falls at most at rate `w/(1 − β_S·gh)`. This
  is the existing `V_S_mem_lowerSlopeCone_generalF` at the negative slope `−w/(1 − β_S·gh)`.
* `zeroSanctionOp`, `reliefValue`, `reliefValue_negLowerSlope` (N13) — the Sender's value
  along zero sanctions, `V(y) = U_S(y,0,0) + β_S·V(F(y,0))`, as a Banach fixed point, and its
  fall rate `w₀/(1 − β_S·gl)` when the zero-sanction payoff falls at rate `w₀`.

The economic reading: a Sender whose coalition loses when hard-liners in the Target gain
(a *hostile* stake) has a continuation value that falls with the political state, and the
rate is the stage loss compounded through the transition's persistence.

Rule 3: every hypothesis is a theorem binder over the existing `U_S` and `F`; no `Params`
field, no structure field, no new `Prop`. Rule 15: the values are constructed fixed points.
Rule 22: general in `F`.
-/

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The fall-rate cone, its closedness and its seed -/

/-- **The set of values falling at rate at least `h` is closed** in the sup norm: it is the
preimage of the lower-slope cone under negation.
Scope: general class (any `Params`; sign-agnostic in `h`). -/
theorem negLowerSlopeCone_isClosed (h : ℝ) :
    IsClosed {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ |
      LowerSlopeOnValueOn (-V) (Set.Icc (0 : ℝ) 1) h} :=
  (lowerSlopeCone_isClosed h).preimage continuous_neg

/-- **The linear value `y ↦ −h·y` falls at rate `h`**: the seed of the fall-rate cone.
Scope: general class (any `Params`; sign-agnostic in `h`). -/
theorem neg_linSeed_mem_negLowerSlopeCone (h : ℝ) :
    LowerSlopeOnValueOn (-(linSeed (-h))) (Set.Icc (0 : ℝ) 1) h := by
  intro y₁ y₂ _ _ hle
  rw [dist_eq_sub_of_le hle]
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply, linSeed_apply]
  exact le_of_eq (by ring)

/-! ## N3. The Bellman operator keeps the fall rate -/

/-- **The Sender's Bellman operator keeps a fall rate (N3).** If, at every feasible sanction
and every pair of states `y₁ ≤ y₂`, the composed stage payoff along the Target policy `α`,
less the discounted value of the induced rise in next period's state priced at `h`, falls by
at least `h` per unit — `ΔU_S − β_S·h·ΔF ≤ −h·Δy` — then `bellmanS_BCF` maps values that fall
at rate at least `h` to values that fall at rate at least `h`. The mirror of
`bellmanS_BCF_preserves_lowerSlopeCone_generalF`; the upper sup-difference bound
`sSup_image_sub_sSup_image_upperBound_of_pointwise` replaces the lower one.
Scope: general class (any `Params`, any continuous Target policy; sign-agnostic in `h`). -/
theorem bellmanS_BCF_preserves_negLowerSlope_generalF
    {α : ℝ → ℝ} (hα : Continuous α) {h : ℝ}
    (h_joint : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      (p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s) - p.β_S * h * (p.F y₂ s - p.F y₁ s)
        ≤ -(h * (y₂ - y₁)))
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV : LowerSlopeOnValueOn (-V) (Set.Icc (0 : ℝ) 1) h) :
    LowerSlopeOnValueOn (-(p.bellmanS_BCF α hα V)) (Set.Icc (0 : ℝ) 1) h := by
  intro y₁ y₂ _ _ hle
  have hβ : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hd : dist y₁ y₂ = y₂.val - y₁.val := dist_eq_sub_of_le hle
  have h_point : ∀ s ∈ Sanctions.I,
      p.integrandS α (fun z => V z) (y₂.val, s) - p.integrandS α (fun z => V z) (y₁.val, s)
        ≤ -(h * dist y₁ y₂) := by
    intro s hs
    have hy₁ : y₁.val ∈ Sanctions.I := y₁.property
    have hy₂ : y₂.val ∈ Sanctions.I := y₂.property
    have hU := h_joint s hs y₁.val y₁.property y₂.val y₂.property hle
    have hF₁ : p.F y₁.val s ∈ Set.Icc (0 : ℝ) 1 := p.F_mem _ _ hy₁ hs
    have hF₂ : p.F y₂.val s ∈ Set.Icc (0 : ℝ) 1 := p.F_mem _ _ hy₂ hs
    have hFle : p.F y₁.val s ≤ p.F y₂.val s := p.F_mono_x s hle
    have hord : Sanctions.clipS' (p.F y₁.val s) ≤ Sanctions.clipS' (p.F y₂.val s) :=
      Sanctions.clipS'_mono hFle
    have hVslope := hV (Sanctions.clipS' (p.F y₁.val s))
      (Sanctions.clipS' (p.F y₂.val s))
      (by rw [Sanctions.clipS'_val_eq_of_mem hF₁]; exact hF₁)
      (by rw [Sanctions.clipS'_val_eq_of_mem hF₂]; exact hF₂) hord
    have hdF : dist (Sanctions.clipS' (p.F y₁.val s))
        (Sanctions.clipS' (p.F y₂.val s)) = p.F y₂.val s - p.F y₁.val s := by
      rw [Sanctions.AbstractGame.Params.clipS'_dist_eq_of_mem hF₁ hF₂, abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [hdF] at hVslope
    simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply] at hVslope
    have hVscaled : p.β_S * (V (Sanctions.clipS' (p.F y₂.val s))
          - V (Sanctions.clipS' (p.F y₁.val s)))
        ≤ p.β_S * (-(h * (p.F y₂.val s - p.F y₁.val s))) :=
      mul_le_mul_of_nonneg_left (by linarith) hβ
    change (p.U_S y₂.val (α y₂.val) s + p.β_S * V (Sanctions.clipS' (p.F y₂.val s)))
        - (p.U_S y₁.val (α y₁.val) s + p.β_S * V (Sanctions.clipS' (p.F y₁.val s)))
      ≤ -(h * dist y₁ y₂)
    rw [hd]
    linarith [hU, hVscaled]
  have hbdd := p.integrandS_image_bddAbove hα V.continuous y₁.val
  have hIne : (Sanctions.I : Set ℝ).Nonempty := ⟨0, by simp [Sanctions.I]⟩
  have key :=
    Sanctions.Foundations.ReflectedArgmax.sSup_image_sub_sSup_image_upperBound_of_pointwise
      hIne h_point hbdd
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply]
  change h * dist y₁ y₂
      ≤ -sSup ((fun s => p.integrandS α (fun z => V z) (y₂.val, s)) '' Sanctions.I)
        - -sSup ((fun s => p.integrandS α (fun z => V z) (y₁.val, s)) '' Sanctions.I)
  linarith

/-! ## N4. The constructed Sender value falls at rate `h` -/

/-- **The constructed Sender value falls at rate at least `h` (N4)**, under the joint chord
of `bellmanS_BCF_preserves_negLowerSlope_generalF`. Same trapping argument as
`V_S_mem_lowerSlopeCone_generalF`: the fall-rate cone is closed, the linear seed `y ↦ −h·y` is
in it, and the operator keeps it, so the Banach fixed point lies in it. Rule 15: `p.V_S α hα`
is constructed.
Scope: general class (any `Params`, any continuous Target policy; sign-agnostic in `h`). -/
theorem V_S_negLowerSlope_generalF
    {α : ℝ → ℝ} (hα : Continuous α) {h : ℝ}
    (h_joint : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      (p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s) - p.β_S * h * (p.F y₂ s - p.F y₁ s)
        ≤ -(h * (y₂ - y₁))) :
    LowerSlopeOnValueOn (-(p.V_S α hα)) (Set.Icc (0 : ℝ) 1) h := by
  have hcontr : ContractingWith p.β_S_nnreal (p.bellmanS_BCF α hα) :=
    p.bellmanS_BCF_contracting hα
  have h_eq : p.V_S α hα = hcontr.fixedPoint := by
    unfold V_S; congr
  obtain ⟨W, hW_fix, hW_mem⟩ :=
    Sanctions.StokeyLucas.fixedPoint_mem_of_mapsTo p.β_S_nnreal_lt_one
      (p.bellmanS_BCF α hα) hcontr.2
      {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ | LowerSlopeOnValueOn (-V) (Set.Icc (0 : ℝ) 1) h}
      (negLowerSlopeCone_isClosed h) ⟨linSeed (-h), neg_linSeed_mem_negLowerSlopeCone h⟩
      (fun _ hW => p.bellmanS_BCF_preserves_negLowerSlope_generalF hα h_joint hW)
  rw [h_eq, ← hcontr.fixedPoint_unique hW_fix]
  exact hW_mem

/-! ## N5. The joint chord from two primitive chords -/

/-- **The joint chord from a falling stage payoff and a persistent transition (N5).** If the
composed stage payoff along `α` falls at rate at least `w ≥ 0` at every feasible sanction, and
the transition rises in the state at rate at least `gl` with `β_S·gl < 1`, then the joint chord
of N3 holds at `h = w/(1 − β_S·gl)`: the stage loss compounded through persistence.
At full defiance the stage bound is the hostile stake bound (approved hypothesis 3).
Scope: general class (any `Params`, any Target policy; sign-agnostic machinery). -/
theorem negJointChord_of_stateChords {α : ℝ → ℝ} {w gl : ℝ} (hw : 0 ≤ w)
    (hβgl : p.β_S * gl < 1)
    (hU : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s ≤ -(w * (y₂ - y₁)))
    (hF : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s) :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      (p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
          - p.β_S * (w / (1 - p.β_S * gl)) * (p.F y₂ s - p.F y₁ s)
        ≤ -((w / (1 - p.β_S * gl)) * (y₂ - y₁)) := by
  intro s hs y₁ hy₁ y₂ hy₂ hle
  have hβ : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hpos : 0 < 1 - p.β_S * gl := by linarith
  set h := w / (1 - p.β_S * gl) with hh_def
  have hh : 0 ≤ h := div_nonneg hw hpos.le
  have hmul : h * (1 - p.β_S * gl) = w := div_mul_cancel₀ _ hpos.ne'
  have hFs := mul_le_mul_of_nonneg_left (hF s hs y₁ hy₁ y₂ hy₂ hle) (mul_nonneg hβ hh)
  have hUs := hU s hs y₁ hy₁ y₂ hy₂ hle
  have hw' : w * (y₂ - y₁) = h * (y₂ - y₁) - p.β_S * h * (gl * (y₂ - y₁)) := by
    rw [← hmul]; ring
  linarith

/-- **The Sender's value falls at the compounded rate (N4 ∘ N5).** If the composed stage
payoff along a continuous Target policy `α` falls at rate at least `w ≥ 0` at every feasible
sanction and the transition rises in the state at rate at least `gl` (`β_S·gl < 1`), then the
constructed Sender value falls at rate at least `w/(1 − β_S·gl)`.
At full defiance the stage bound is the hostile stake bound, uniform in the sanction
(approved hypothesis 3).
Scope: general class (any `Params`, any continuous Target policy). -/
theorem V_S_negLowerSlope_of_stateChords {α : ℝ → ℝ} (hα : Continuous α) {w gl : ℝ}
    (hw : 0 ≤ w) (hβgl : p.β_S * gl < 1)
    (hU : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s ≤ -(w * (y₂ - y₁)))
    (hF : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s) :
    LowerSlopeOnValueOn (-(p.V_S α hα)) (Set.Icc (0 : ℝ) 1) (w / (1 - p.β_S * gl)) :=
  p.V_S_negLowerSlope_generalF hα (p.negJointChord_of_stateChords hw hβgl hU hF)

/-- **The Sender's value falls at most at the compounded Lipschitz rate.** If the composed
stage payoff along `α` falls at most at rate `w ≥ 0` at every feasible sanction
(`ΔU_S ≥ −w·Δy`) and the transition rises in the state at most at rate `gh` (`β_S·gh < 1`),
then the constructed Sender value falls at most at rate `K = w/(1 − β_S·gh)`: it lies in the
lower-slope cone with the negative slope `−K`. This is the existing sign-agnostic
`V_S_mem_lowerSlopeCone_generalF` at `g = −K`; no new cone is used.
Scope: general class (any `Params`, any continuous Target policy). -/
theorem V_S_lowerSlope_of_stateLowerChords {α : ℝ → ℝ} (hα : Continuous α) {w gh : ℝ}
    (hw : 0 ≤ w) (hβgh : p.β_S * gh < 1)
    (hU : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      -(w * (y₂ - y₁)) ≤ p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
    (hF : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.F y₂ s - p.F y₁ s ≤ gh * (y₂ - y₁)) :
    LowerSlopeOnValueOn (p.V_S α hα) (Set.Icc (0 : ℝ) 1) (-(w / (1 - p.β_S * gh))) := by
  apply p.V_S_mem_lowerSlopeCone_generalF hα
  intro s hs y₁ hy₁ y₂ hy₂ hle
  have hβ : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hpos : 0 < 1 - p.β_S * gh := by linarith
  set K := w / (1 - p.β_S * gh) with hK_def
  have hK : 0 ≤ K := div_nonneg hw hpos.le
  have hmul : K * (1 - p.β_S * gh) = w := div_mul_cancel₀ _ hpos.ne'
  have hFs := mul_le_mul_of_nonneg_left (hF s hs y₁ hy₁ y₂ hy₂ hle) (mul_nonneg hβ hK)
  have hUs := hU s hs y₁ hy₁ y₂ hy₂ hle
  have hw' : w * (y₂ - y₁) = K * (y₂ - y₁) - p.β_S * K * (gh * (y₂ - y₁)) := by
    rw [← hmul]; ring
  nlinarith

/-! ## N13. The Sender's value along zero sanctions -/

/-- **The zero-sanction operator** `V ↦ (y ↦ U_S(y, 0, 0) + β_S·V(F(y, 0)))`: the Sender's
Bellman recursion when it never sanctions and the Target's compliance is worth nothing to it at
zero sanction. The `Params`-level form of `ChordEconomyCs.relaxOp`. -/
def zeroSanctionOp (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) =>
        p.U_S y.val 0 0 + p.β_S * V (Sanctions.clipS' (p.F y.val 0)),
      by
      have hF : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => p.F y.val 0) :=
        p.F_continuous.comp (continuous_subtype_val.prodMk continuous_const)
      have hU : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => p.U_S y.val 0 0) :=
        p.U_S_continuous.comp
          (continuous_subtype_val.prodMk (continuous_const.prodMk continuous_const))
      exact hU.add
        (continuous_const.mul (V.continuous.comp (Sanctions.clipS'_continuous.comp hF)))⟩

/-- The zero-sanction operator, pointwise.
Scope: general class (any `Params`). -/
theorem zeroSanctionOp_apply (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (y : ↥(Sanctions.S : Set ℝ)) :
    p.zeroSanctionOp V y = p.U_S y.val 0 0 + p.β_S * V (Sanctions.clipS' (p.F y.val 0)) :=
  rfl

/-- **The zero-sanction operator is a `β_S`-contraction.**
Scope: general class (any `Params`). -/
theorem zeroSanctionOp_contracting : ContractingWith p.β_S_nnreal p.zeroSanctionOp := by
  refine ⟨p.β_S_nnreal_lt_one, ?_⟩
  apply lipschitzWith_of_pointwise_dist_le
  intro V W y
  rw [zeroSanctionOp_apply, zeroSanctionOp_apply, Real.dist_eq]
  have hβ : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have h1 : |(p.U_S y.val 0 0 + p.β_S * V (Sanctions.clipS' (p.F y.val 0)))
      - (p.U_S y.val 0 0 + p.β_S * W (Sanctions.clipS' (p.F y.val 0)))|
      = p.β_S * |V (Sanctions.clipS' (p.F y.val 0)) - W (Sanctions.clipS' (p.F y.val 0))| := by
    rw [show ∀ a b c : ℝ, (a + p.β_S * b) - (a + p.β_S * c) = p.β_S * (b - c) from
      fun a b c => by ring, abs_mul, abs_of_nonneg hβ]
  rw [h1]
  have h2 := BoundedContinuousFunction.dist_coe_le_dist (f := V) (g := W)
    (Sanctions.clipS' (p.F y.val 0))
  rw [Real.dist_eq] at h2
  have := mul_le_mul_of_nonneg_left h2 hβ
  convert this using 2

/-- **The relief value**: the Sender's value along zero sanctions, the unique fixed point of
`zeroSanctionOp` (Rule 15: Banach). In every equilibrium whose realised sanction is zero at
every state, and in which compliance is worth nothing to the Sender at zero sanction, the
Sender's value is this function (`equilibrium_V_S_eq_reliefValue`, `SenderStakeSign.lean`). -/
def reliefValue : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  ContractingWith.fixedPoint p.zeroSanctionOp p.zeroSanctionOp_contracting

/-- The relief value is a fixed point of the zero-sanction operator.
Scope: general class (any `Params`). -/
theorem reliefValue_fix : p.zeroSanctionOp p.reliefValue = p.reliefValue :=
  ContractingWith.fixedPoint_isFixedPt p.zeroSanctionOp_contracting

/-- Every fixed point of the zero-sanction operator is the relief value (Banach uniqueness).
Scope: general class (any `Params`). -/
theorem eq_reliefValue_of_fix {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV : p.zeroSanctionOp V = V) : V = p.reliefValue :=
  ContractingWith.fixedPoint_unique p.zeroSanctionOp_contracting hV

/-- **The zero-sanction operator keeps the fall rate `w₀/(1 − β_S·gl)`**, when the Sender's
zero-sanction payoff at defiance falls at rate at least `w₀ ≥ 0` and the zero-sanction section
of the transition rises in the state at rate at least `gl` (`β_S·gl < 1`).
At defiance the stage bound is the hostile stake bound at zero sanction (approved
hypothesis 3 at `s = 0`).
Scope: general class (any `Params`). -/
theorem zeroSanctionOp_preserves_negLowerSlope {w gl : ℝ} (hw : 0 ≤ w)
    (hβgl : p.β_S * gl < 1)
    (hU0 : ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ 0 0 - p.U_S y₁ 0 0 ≤ -(w * (y₂ - y₁)))
    (hF0 : ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0)
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV : LowerSlopeOnValueOn (-V) (Set.Icc (0 : ℝ) 1) (w / (1 - p.β_S * gl))) :
    LowerSlopeOnValueOn (-(p.zeroSanctionOp V)) (Set.Icc (0 : ℝ) 1) (w / (1 - p.β_S * gl)) := by
  intro y₁ y₂ _ _ hle
  have hβ : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hpos : 0 < 1 - p.β_S * gl := by linarith
  set h := w / (1 - p.β_S * gl) with hh_def
  have hh : 0 ≤ h := div_nonneg hw hpos.le
  have hmul : h * (1 - p.β_S * gl) = w := div_mul_cancel₀ _ hpos.ne'
  have hd : dist y₁ y₂ = y₂.val - y₁.val := dist_eq_sub_of_le hle
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have hF₁ : p.F y₁.val 0 ∈ Set.Icc (0 : ℝ) 1 := p.F_mem _ _ y₁.property h0I
  have hF₂ : p.F y₂.val 0 ∈ Set.Icc (0 : ℝ) 1 := p.F_mem _ _ y₂.property h0I
  have hFle : p.F y₁.val 0 ≤ p.F y₂.val 0 := p.F_mono_x 0 hle
  have hVslope := hV (Sanctions.clipS' (p.F y₁.val 0)) (Sanctions.clipS' (p.F y₂.val 0))
    (by rw [Sanctions.clipS'_val_eq_of_mem hF₁]; exact hF₁)
    (by rw [Sanctions.clipS'_val_eq_of_mem hF₂]; exact hF₂) (Sanctions.clipS'_mono hFle)
  have hdF : dist (Sanctions.clipS' (p.F y₁.val 0))
      (Sanctions.clipS' (p.F y₂.val 0)) = p.F y₂.val 0 - p.F y₁.val 0 := by
    rw [Sanctions.AbstractGame.Params.clipS'_dist_eq_of_mem hF₁ hF₂, abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  rw [hdF] at hVslope
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply] at hVslope
  have hVscaled : p.β_S * (V (Sanctions.clipS' (p.F y₂.val 0))
        - V (Sanctions.clipS' (p.F y₁.val 0)))
      ≤ p.β_S * (-(h * (p.F y₂.val 0 - p.F y₁.val 0))) :=
    mul_le_mul_of_nonneg_left (by linarith) hβ
  have hFs := mul_le_mul_of_nonneg_left (hF0 y₁.val y₁.property y₂.val y₂.property hle)
    (mul_nonneg hβ hh)
  have hUs := hU0 y₁.val y₁.property y₂.val y₂.property hle
  have hw' : w * (y₂.val - y₁.val)
      = h * (y₂.val - y₁.val) - p.β_S * h * (gl * (y₂.val - y₁.val)) := by
    rw [← hmul]; ring
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply, zeroSanctionOp_apply]
  rw [hd]
  linarith

/-- **The relief value falls at rate at least `w₀/(1 − β_S·gl)` (N13)**, when the Sender's
zero-sanction payoff at defiance falls at rate at least `w₀ ≥ 0` and the zero-sanction
section of the transition rises in the state at rate at least `gl` (`β_S·gl < 1`). Trapped
in the closed fall-rate cone, seeded with `y ↦ −h·y` (Rule 15).
At defiance the stage bound is the hostile stake bound at zero sanction (approved
hypothesis 3 at `s = 0`), used for the relief price.
Scope: general class (any `Params`). -/
theorem reliefValue_negLowerSlope {w gl : ℝ} (hw : 0 ≤ w) (hβgl : p.β_S * gl < 1)
    (hU0 : ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ 0 0 - p.U_S y₁ 0 0 ≤ -(w * (y₂ - y₁)))
    (hF0 : ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0) :
    LowerSlopeOnValueOn (-p.reliefValue) (Set.Icc (0 : ℝ) 1) (w / (1 - p.β_S * gl)) := by
  have hcontr := p.zeroSanctionOp_contracting
  obtain ⟨W, hW_fix, hW_mem⟩ :=
    Sanctions.StokeyLucas.fixedPoint_mem_of_mapsTo p.β_S_nnreal_lt_one
      p.zeroSanctionOp hcontr.2
      {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ |
        LowerSlopeOnValueOn (-V) (Set.Icc (0 : ℝ) 1) (w / (1 - p.β_S * gl))}
      (negLowerSlopeCone_isClosed _) ⟨linSeed (-(w / (1 - p.β_S * gl))),
        neg_linSeed_mem_negLowerSlopeCone _⟩
      (fun _ hW => p.zeroSanctionOp_preserves_negLowerSlope hw hβgl hU0 hF0 hW)
  rw [← p.eq_reliefValue_of_fix hW_fix]
  exact hW_mem

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
