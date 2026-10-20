/-
Sanctions/Examples/PlacableSenderUniqueness.lean

**Under the loss-offset margin, the constructed defiance equilibrium is the
only equilibrium in the monotone class, under a general transition** (round AR,
2026-09-23; doc 102 §1 row 9, on the user's word; on the abstract payoffs since
round AV, 2026-09-25, doc 104).

The class: top-selector feedback Stackelberg equilibria whose compliance policy
is nonincreasing in the state and whose realised sanction rule is nondecreasing
in the state. Both are hypotheses on the quantifier, stated as such; nothing is
asserted about equilibria outside the class.

**The argument.** (1) The Target's value is its own joint integrand at its
policy (`V_T_eq_at_policy`). Along the profile the stage payoff's increment is
at least `v_lo·Δy − c·Δs`: less compliance at the higher state does not lower it
(T2), the lower state rate is at least `v_lo` (T6, `n_lo ≥ 0`), and the pain rate
is at most `c` (T4); the successor rises by at least `g_lo·Δy + d_lo·Δs`; under
the margin `c ≤ β_T d_lo g_T⁰`, with `g_T⁰ = v_lo/(1 − β_T g_lo)`, the deficit of
the value below the slope `g_T⁰`
therefore satisfies `Δ(y₁,y₂) ≥ β_T·Δ(F₁,F₂)`, and its infimum `D` over all
pairs — finite, since the value is bounded — satisfies `D ≥ β_T·D`, so `D ≥ 0`:
the Target's value has lower slope `g_T⁰` (`target_lowerSlope_of_monotone_class`;
no operator, no continuity of the rule is used). (2) At any state, the
deviation from the policy to full defiance raises the sanction (the greatest
selector is antitone in compliance under decreasing differences, placation S10,
with no uniqueness, `σ_dyn_top_antitoneOn_a_of_DD`), and the pain of that rise
is covered by the continuation gain at slope `g_T⁰` through the lower sanction
chord — the margin again — while the compliance saved is worth at least
`ℓ_lo·α(x)`; so `α(x) = 0` (`policy_eq_zero_of_monotone_class`). (3) The Sender's
value is then
the unique fixed point of the Bellman operator at defiance, the constructed
`VSstar`; the Target's the unique fixed point of the Target operator at
`VSstar`, the constructed `VTdef`; the rule is the constructed response
(`unique_equilibrium_of_monotone_class`).

**The margin used.** The unrefined form `c ≤ β_T d_lo v_lo/(1 − β_T g_lo)`, which
coincides with the floor-refined `LossOffset` at `n_lo = 0` and implies it in
general (`LossOffset₀.toLossOffset`). The refined form prices the rally term at
the sanction floor `b = σ(0,0)`, which the constructed defiance profile attains
but an arbitrary member of the class need not; using the unrefined form keeps
the statement honest over the whole class. **No zero-sanction neutrality** is
read anywhere in the chain (sign-off M2). Rule 3: a hypothesis on the quantifier,
no field. Rule 22: general in `F`.

**Round BB (2026-09-28): the policy condition is not needed.**
`unique_equilibrium_of_rule_monotone` (`Examples/PlacableSenderDefianceCore.lean`)
proves the same conclusion for every equilibrium whose realised rule is
nondecreasing, and this theorem follows from it
(`unique_equilibrium_of_monotone_class_of_rule_monotone`). It stays as it is
because it is a pinned headline row.
-/
import Sanctions.Examples.PlacableSenderBracket
import Sanctions.Examples.PlacableSenderAllEquilibria

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-- The unrefined Target slope `v_lo/(1 − β_T g_lo)`. -/
def gT₀ : ℝ := E.vlo / (1 - E.β_T * E.glo)

theorem gT₀_pos : 0 < E.gT₀ := by
  unfold gT₀
  exact div_pos E.hvlo (by linarith [E.βT_glo_lt_one])

theorem gT₀_mul : E.gT₀ * (1 - E.β_T * E.glo) = E.vlo := by
  unfold gT₀
  exact div_mul_cancel₀ _ (by linarith [E.βT_glo_lt_one])

theorem gT₀_le_gT : E.gT₀ ≤ E.gT := by
  unfold gT₀ gT
  have h : 0 ≤ E.nlo * E.sfloor := mul_nonneg E.hnlo E.sfloor_mem.1
  apply div_le_div_of_nonneg_right (by linarith) (by linarith [E.βT_glo_lt_one])

/-- **The unrefined loss-offset margin** `c ≤ β_T d_lo g_T⁰`; the `LossOffset`
at `n_lo = 0`, and stronger in general (`LossOffset₀.toLossOffset`). -/
def LossOffset₀ : Prop := E.c ≤ E.β_T * E.dlo * E.gT₀

theorem LossOffset₀.toLossOffset {E : ChordEconomy} (h : E.LossOffset₀) : E.LossOffset := by
  have h1 : E.c ≤ E.β_T * E.dlo * E.gT₀ := h
  have h2 := mul_le_mul_of_nonneg_left E.gT₀_le_gT (mul_nonneg E.hβT0.le E.hdlo0.le)
  show E.c ≤ E.β_T * E.dlo * E.gT
  linarith

/-- The realised sanction rule of an equilibrium: the greatest selector at the
policy. -/
def rule (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (x : ℝ) : ℝ :=
  E.toParams.σ_dyn_top Eq.V_S x (Eq.α x)

theorem rule_eq (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (x : ℝ) :
    E.rule Eq x = E.toParams.dynamicEquilibriumRule Eq x := rfl

theorem rule_mem (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (x : ℝ) :
    E.rule Eq x ∈ Sanctions.I := E.toParams.σ_dyn_top_mem_I _ _ _

/-- A nonincreasing policy makes the Sender's value monotone (round AM's cone),
when a larger concession is never worth more to the Sender in itself. Not read
by the uniqueness chain below. -/
theorem V_S_monotone_of_antitone (hZ : E.ZeroSanctionAntitone)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hanti : AntitoneOn Eq.α Sanctions.S) : Monotone Eq.V_S := by
  have h := E.V_S_lowerSlope_of_antitone hZ Eq hanti
  intro y₁ y₂ hle
  have := h y₁ y₂ y₁.property y₂.property hle
  have hd : 0 ≤ E.gS * dist y₁ y₂ := mul_nonneg E.gS_pos.le dist_nonneg
  linarith

/-- **The Target's value at its own policy**, unfolded. -/
theorem V_T_eq (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (y : ↥(Sanctions.S : Set ℝ)) :
    Eq.V_T y = E.toParams.U_T y.val (Eq.α y.val) (E.rule Eq y.val)
      + E.β_T * Eq.V_T (Sanctions.clipS' (E.F y.val (E.rule Eq y.val))) := by
  rw [Params.FeedbackStackelbergEquilibriumTop.V_T_eq_at_policy]
  rfl

/-- The deficit of the Target's value below the slope `g_T⁰` at a pair of states. -/
def deficit (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (y₁ y₂ : ↥(Sanctions.S : Set ℝ)) : ℝ :=
  Eq.V_T y₂ - Eq.V_T y₁ - E.gT₀ * (y₂.val - y₁.val)

theorem deficit_bddBelow (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) :
    BddBelow (Set.range (fun p : ↥(Sanctions.S : Set ℝ) × ↥(Sanctions.S : Set ℝ) =>
      E.deficit Eq p.1 p.2)) := by
  refine ⟨-(2 * ‖Eq.V_T‖ + E.gT₀), ?_⟩
  rintro _ ⟨⟨y₁, y₂⟩, rfl⟩
  simp only [deficit]
  have h1 := BoundedContinuousFunction.norm_coe_le_norm Eq.V_T y₁
  have h2 := BoundedContinuousFunction.norm_coe_le_norm Eq.V_T y₂
  rw [Real.norm_eq_abs] at h1 h2
  have hy₁ := y₁.property
  have hy₂ := y₂.property
  have hg := E.gT₀_pos
  have h3 : E.gT₀ * (y₂.val - y₁.val) ≤ E.gT₀ := by nlinarith [hy₁.1, hy₂.2]
  have h4 := abs_le.mp h1
  have h5 := abs_le.mp h2
  linarith

/-- **The one-step deficit inequality along the profile**, under the unrefined
margin, for a nonincreasing policy and a nondecreasing rule:
`Δ(y₁,y₂) ≥ β_T·Δ(F₁,F₂)`. -/
theorem deficit_ge (hTM : E.LossOffset₀) (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hanti : AntitoneOn Eq.α Sanctions.S) (hrule : MonotoneOn (E.rule Eq) Sanctions.S)
    (y₁ y₂ : ↥(Sanctions.S : Set ℝ)) (hle : y₁ ≤ y₂) :
    E.deficit Eq y₁ y₂
      ≥ E.β_T * E.deficit Eq (Sanctions.clipS' (E.F y₁.val (E.rule Eq y₁.val)))
          (Sanctions.clipS' (E.F y₂.val (E.rule Eq y₂.val))) := by
  have hy₁ := y₁.property
  have hy₂ := y₂.property
  have hyle : y₁.val ≤ y₂.val := hle
  have hα : Eq.α y₂.val ≤ Eq.α y₁.val := hanti hy₁ hy₂ hyle
  have hs : E.rule Eq y₁.val ≤ E.rule Eq y₂.val := hrule hy₁ hy₂ hyle
  have hs₁ := E.rule_mem Eq y₁.val
  have hs₂ := E.rule_mem Eq y₂.val
  have hF₁ := E.F_mem _ _ hy₁ hs₁
  have hF₂ := E.F_mem _ _ hy₂ hs₂
  have hz₁ : E.F y₁.val (E.rule Eq y₁.val) ≤ E.F y₁.val (E.rule Eq y₂.val) := E.F_mono_s _ hs
  have hz₂ : E.F y₁.val (E.rule Eq y₂.val) ≤ E.F y₂.val (E.rule Eq y₂.val) := E.F_mono_x _ hyle
  have hband := (E.hbandAll _ hs₂) y₁.val hy₁ y₂.val hy₂ hyle
  have hchord := E.hSlo hy₁ hs₁ hs₂ hs
  have hsucc : E.glo * (y₂.val - y₁.val) + E.dlo * (E.rule Eq y₂.val - E.rule Eq y₁.val)
      ≤ E.F y₂.val (E.rule Eq y₂.val) - E.F y₁.val (E.rule Eq y₁.val) := by
    linarith [hband.1, hchord]
  have hV₁ := E.V_T_eq Eq y₁
  have hV₂ := E.V_T_eq Eq y₂
  simp only [deficit]
  rw [hV₁, hV₂]
  simp only [Sanctions.clipS'_val_eq_of_mem hF₁, Sanctions.clipS'_val_eq_of_mem hF₂]
  have hTM' : E.c ≤ E.β_T * E.dlo * E.gT₀ := hTM
  have hg := E.gT₀_mul
  have hβ := E.hβT0.le
  have hg0 := E.gT₀_pos.le
  have ha₁ := Eq.α_mem y₁.val hy₁
  have ha₂ := Eq.α_mem y₂.val hy₂
  -- the pain term is covered by the continuation at slope `g_T⁰` through `d_lo`
  have hA : 0 ≤ (E.rule Eq y₂.val - E.rule Eq y₁.val) * (E.β_T * E.dlo * E.gT₀ - E.c) :=
    mul_nonneg (sub_nonneg.mpr hs) (by linarith)
  -- less compliance at the higher state does not lower the stage payoff (T2)
  have hC := E.hUT_costLo y₂.val hy₂ (E.rule Eq y₂.val) hs₂ (Eq.α y₂.val) ha₂ (Eq.α y₁.val) ha₁ hα
  have hC' : 0 ≤ E.ℓlo * (Eq.α y₁.val - Eq.α y₂.val) := mul_nonneg E.hℓlo.le (by linarith)
  -- the state and pain rates at the fixed compliance `α y₁` (T6, T4)
  have hSt := E.UT_state_chord_ge hy₁ hy₂ ha₁ hs₁ hs₂ hyle hs
  have hn : 0 ≤ E.nlo * E.rule Eq y₁.val * (y₂.val - y₁.val) :=
    mul_nonneg (mul_nonneg E.hnlo hs₁.1) (by linarith)
  have hD := mul_le_mul_of_nonneg_left hsucc (mul_nonneg hβ hg0)
  have hgΔ : E.gT₀ * (y₂.val - y₁.val)
      = E.vlo * (y₂.val - y₁.val) + E.β_T * E.gT₀ * (E.glo * (y₂.val - y₁.val)) := by
    rw [← hg]; ring
  nlinarith [hA, hC, hC', hSt, hn, hD, hgΔ]

/-- The deficits at ordered pairs of states. -/
def deficitSet (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) : Set ℝ :=
  (fun p : ↥(Sanctions.S : Set ℝ) × ↥(Sanctions.S : Set ℝ) => E.deficit Eq p.1 p.2) ''
    {p | p.1 ≤ p.2}

theorem deficitSet_bddBelow (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) :
    BddBelow (E.deficitSet Eq) := by
  obtain ⟨b, hb⟩ := E.deficit_bddBelow Eq
  refine ⟨b, ?_⟩
  rintro _ ⟨⟨y₁, y₂⟩, -, rfl⟩
  exact hb ⟨(y₁, y₂), rfl⟩

theorem deficitSet_nonempty (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) :
    (E.deficitSet Eq).Nonempty := by
  let z : ↥(Sanctions.S : Set ℝ) := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
  exact ⟨E.deficit Eq z z, ⟨(z, z), (le_refl z : z ≤ z), rfl⟩⟩

/-- **The Target's value in the monotone class has lower slope `g_T⁰`** (the
infimum trick: with `D` the infimum of the deficit over ordered pairs,
`D ≥ β_T D`, so `D ≥ 0`). -/
theorem target_lowerSlope_of_monotone_class (hTM : E.LossOffset₀)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hanti : AntitoneOn Eq.α Sanctions.S) (hrule : MonotoneOn (E.rule Eq) Sanctions.S) :
    Params.LowerSlopeOnValueOn Eq.V_T (Icc (0 : ℝ) 1) E.gT₀ := by
  have hbdd := E.deficitSet_bddBelow Eq
  have hne := E.deficitSet_nonempty Eq
  set D := sInf (E.deficitSet Eq) with hD
  have hstep : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), y₁ ≤ y₂ → E.β_T * D ≤ E.deficit Eq y₁ y₂ := by
    intro y₁ y₂ hle
    have h := E.deficit_ge hTM Eq hanti hrule y₁ y₂ hle
    have hyle : y₁.val ≤ y₂.val := hle
    have hs : E.rule Eq y₁.val ≤ E.rule Eq y₂.val := hrule y₁.property y₂.property hyle
    have hz : E.F y₁.val (E.rule Eq y₁.val) ≤ E.F y₂.val (E.rule Eq y₂.val) :=
      (E.F_mono_s _ hs).trans (E.F_mono_x _ hyle)
    have hmem : E.deficit Eq (Sanctions.clipS' (E.F y₁.val (E.rule Eq y₁.val)))
        (Sanctions.clipS' (E.F y₂.val (E.rule Eq y₂.val))) ∈ E.deficitSet Eq :=
      ⟨(_, _), Sanctions.clipS'_mono hz, rfl⟩
    have h2 := csInf_le hbdd hmem
    have h3 := mul_le_mul_of_nonneg_left h2 E.hβT0.le
    linarith
  have hDD : E.β_T * D ≤ D := by
    apply le_csInf hne
    rintro _ ⟨⟨y₁, y₂⟩, hle, rfl⟩
    exact hstep y₁ y₂ hle
  have hD0 : 0 ≤ D := by
    by_contra hcon
    have hneg : D < 0 := not_le.mp hcon
    have := mul_lt_mul_of_neg_right E.hβT1 hneg
    linarith
  intro y₁ y₂ _ _ hle
  have h := (hD0.trans (csInf_le hbdd ⟨(y₁, y₂), hle, rfl⟩))
  simp only [deficit] at h
  have hd : dist y₁ y₂ = y₂.val - y₁.val := by
    have hyle : y₁.val ≤ y₂.val := hle
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hd]
  linarith

/-- **In the monotone class the Target defies at every state**: the deviation
from `α(x)` to full defiance raises the sanction (the greatest selector is
antitone in compliance), the pain of the rise is covered by the continuation
at slope `g_T⁰` through the lower sanction chord (the margin), and the
compliance saved is worth at least `ℓ_lo·α(x)`. -/
theorem policy_eq_zero_of_monotone_class (hTM : E.LossOffset₀)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hanti : AntitoneOn Eq.α Sanctions.S) (hrule : MonotoneOn (E.rule Eq) Sanctions.S)
    {x : ℝ} (hx : x ∈ Sanctions.I) : Eq.α x = 0 := by
  have hslope := E.target_lowerSlope_of_monotone_class hTM Eq hanti hrule
  have hαI := Eq.α_mem x hx
  by_contra hne
  have hpos : 0 < Eq.α x := lt_of_le_of_ne hαI.1 (Ne.symm hne)
  have hopt := Eq.α_opt_top x hx (show (0:ℝ) ∈ Sanctions.I from ⟨le_rfl, zero_le_one⟩)
  simp only [Set.mem_setOf_eq] at hopt
  -- unfold both integrands
  set s₀ := E.toParams.σ_dyn_top Eq.V_S x 0 with hs₀def
  set sα := E.toParams.σ_dyn_top Eq.V_S x (Eq.α x) with hsαdef
  have hs : sα ≤ s₀ :=
    E.toParams.σ_dyn_top_antitoneOn_a_of_DD Eq.V_S x (E.stage_decreasingDifferences x hx)
      ⟨le_rfl, zero_le_one⟩ hαI hpos.le
  have hs₀I := E.toParams.σ_dyn_top_mem_I Eq.V_S x 0
  have hsαI := E.toParams.σ_dyn_top_mem_I Eq.V_S x (Eq.α x)
  have hF₀ := E.F_mem _ _ hx hs₀I
  have hFα := E.F_mem _ _ hx hsαI
  have hz : E.F x sα ≤ E.F x s₀ := E.F_mono_s x hs
  have hchord : E.dlo * (s₀ - sα) ≤ E.F x s₀ - E.F x sα := E.hSlo hx hsαI hs₀I hs
  have hsl := E.clip_lowerSlope_of hslope _ hFα _ hF₀ hz
  have hTM' : E.c ≤ E.β_T * E.dlo * E.gT₀ := hTM
  unfold Params.joint_T_top_integrand at hopt
  have hβ := E.hβT0.le
  have hA : E.β_T * E.dlo * E.gT₀ * (s₀ - sα)
      ≤ E.β_T * (Eq.V_T (Sanctions.clipS' (E.F x s₀)) - Eq.V_T (Sanctions.clipS' (E.F x sα))) := by
    have h1 := mul_le_mul_of_nonneg_left hchord (mul_nonneg hβ E.gT₀_pos.le)
    have h2 := mul_le_mul_of_nonneg_left hsl hβ
    nlinarith [h1, h2]
  have hB : 0 ≤ (s₀ - sα) * (E.β_T * E.dlo * E.gT₀ - E.c) :=
    mul_nonneg (sub_nonneg.mpr hs) (by linarith)
  -- the stage: pain at most `c` per unit, compliance cost at least `ℓ_lo` per unit
  have hU := E.UT_sub_le hx zero_mem_I hαI hs₀I hsαI hpos.le hs
  have hD : 0 < E.ℓlo * Eq.α x := mul_pos E.hℓlo hpos
  have hopt' : E.U_T x 0 s₀ + E.β_T * Eq.V_T (Sanctions.clipS' (E.F x s₀))
      ≤ E.U_T x (Eq.α x) sα + E.β_T * Eq.V_T (Sanctions.clipS' (E.F x sα)) := hopt
  nlinarith [hopt', hA, hB, hU, hD]

/-- **The uniqueness theorem.** Under the unrefined loss-offset margin, every
top-selector equilibrium whose compliance policy is nonincreasing in the state
and whose realised sanction rule is nondecreasing in the state has full
defiance at every feasible state, the constructed Sender value `VSstar`, the
constructed Target value `VTdef`, and the constructed response as its rule. -/
theorem unique_equilibrium_of_monotone_class (hTM : E.LossOffset₀)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hanti : AntitoneOn Eq.α Sanctions.S) (hrule : MonotoneOn (E.rule Eq) Sanctions.S) :
    (∀ x ∈ Sanctions.I, Eq.α x = 0) ∧ Eq.V_S = E.VSstar ∧ Eq.V_T = E.VTdef ∧
    ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = E.responsePath E.VSstar x := by
  have hα : ∀ x ∈ Sanctions.I, Eq.α x = 0 :=
    fun x hx => E.policy_eq_zero_of_monotone_class hTM Eq hanti hrule hx
  -- the Sender's value is the fixed point at defiance
  have hVS : Eq.V_S = E.VSstar := by
    have hfix : E.toParams.bellmanS_BCF (fun _ => 0) continuous_const Eq.V_S = Eq.V_S := by
      rw [← E.toParams.bellmanS_BCF_congr_on Eq.hα continuous_const hα Eq.V_S]
      exact Eq.V_S_fix.symm
    have hcontr := E.toParams.bellmanS_BCF_contracting (α := fun _ => 0) continuous_const
    have h1 : Eq.V_S = hcontr.fixedPoint := hcontr.fixedPoint_unique hfix
    have h2 : E.VSstar = hcontr.fixedPoint := hcontr.fixedPoint_unique E.VSstar_fix
    rw [h1, h2]
  -- the Target's value is the fixed point of the Target operator at `VSstar`
  have hVT : Eq.V_T = E.VTdef := by
    have hfix : E.targetOp E.VSstar_mem Eq.V_T = Eq.V_T := by
      ext y
      rw [targetOp_apply, E.V_T_eq Eq y, rule, hα y.val y.property, hVS,
          ← E.response_eq_top E.VSstar_mem y.property 0]
      rfl
    have hcontr := E.targetOp_contracting E.VSstar_mem
    have h1 : Eq.V_T = hcontr.fixedPoint := hcontr.fixedPoint_unique hfix
    exact h1
  refine ⟨hα, hVS, hVT, fun x hx => ?_⟩
  show E.toParams.σ_dyn_top Eq.V_S x (Eq.α x) = E.responsePath E.VSstar x
  rw [hα x hx, hVS, ← E.response_eq_top E.VSstar_mem hx 0]
  rfl

/-- The constructed defiance equilibrium is in the class (its policy is
constant and its rule is the monotone response), so the class is nonempty
(Rule 9B). -/
theorem equilibriumTop_mem_monotone_class (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    AntitoneOn (E.equilibriumTop hTM hmono).α Sanctions.S ∧
    MonotoneOn (E.rule (E.equilibriumTop hTM hmono)) Sanctions.S := by
  refine ⟨fun _ _ _ _ _ => le_rfl, ?_⟩
  intro x hx y hy hxy
  show E.toParams.σ_dyn_top E.VSstar x 0 ≤ E.toParams.σ_dyn_top E.VSstar y 0
  rw [← E.response_eq_top E.VSstar_mem hx 0, ← E.response_eq_top E.VSstar_mem hy 0]
  exact hmono hx hy hxy

end ChordEconomy

end

#print axioms Sanctions.Examples.ChordEconomy.target_lowerSlope_of_monotone_class
#print axioms Sanctions.Examples.ChordEconomy.policy_eq_zero_of_monotone_class
#print axioms Sanctions.Examples.ChordEconomy.unique_equilibrium_of_monotone_class

end Examples
end Sanctions
