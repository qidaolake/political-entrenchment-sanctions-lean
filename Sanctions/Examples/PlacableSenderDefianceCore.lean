/-
Sanctions/Examples/PlacableSenderDefianceCore.lean

**Uniqueness in the monotone-rule class, with no condition on the policy; no
sanction-free equilibrium** (round BB, 2026-09-28; doc 110 items R12a, G1 and
C2b, on the user's word).

The chord-economy corollaries of the defiance core
(`Theory/Equilibrium/DefianceCore.lean`). Every chord economy satisfies the
core's hypotheses, with `g_lo`, `d_lo`, `c`, `v_lo`, `ℓ_lo` read off its fields:

* T2 at compliance `0`: compliance costs at least `ℓ_lo` per unit;
* T4 at full defiance: the pain is at most `c` per unit;
* T6 at full defiance, with `n_lo·s ≥ 0` dropped: the state rate is at least `v_lo`;
* S10 as a sign: `k_lo ≥ 0` gives decreasing differences;
* the two lower chords;
* and `LossOffset₀`, which is the core's margin exactly.

Round BG (2026-10-06): the core now reads only consequences of T2 and S10, the
sign of the compliance cost (`weakCost_of_linearCost`) and decreasing
differences against full defiance (`DD0_of_decreasingDifferencesOn`), and no
longer reads `d_lo ≥ 0`. `target_lowerSlope_of_rule_monotone` passes those
consequences; the statements here are unchanged.

Four results follow.

1. **`unique_equilibrium_of_rule_monotone`.** Under the unrefined loss-offset
   margin, every top-selector equilibrium whose realised sanction rule is
   nondecreasing in the state has full defiance, the constructed Sender value
   `VSstar`, the constructed Target value `VTdef`, and the constructed response
   as its rule. This is headline row 46 (`unique_equilibrium_of_monotone_class`)
   **without its policy condition**: 2 premises instead of 3, removing the
   policy-monotonicity hypothesis. It does not show that its class is strictly
   larger: under the margin both classes reduce to full defiance. Row 46 follows
   as a corollary
   (`unique_equilibrium_of_monotone_class_of_rule_monotone`); it stays pinned,
   unchanged.
2. **`no_zero_rule_equilibrium`.** Under the same margin, no top-selector
   equilibrium sanctions at zero at every state. A zero rule is nondecreasing, so
   such an equilibrium would be in the class, hence full defiance, and its rule
   would be the forward-looking response, which is positive at every state. No
   zero-sanction neutrality and no `ChordEconomyCs` field is read.
3. **`lossOffset₀_iff_βT_ge`.** The margin in patience form: it holds exactly when
   `β_T ≥ c/(d_lo·v_lo + c·g_lo)`, a bound with no Sender parameter
   (doc 110 item C3a); `unique_equilibrium_of_patient_target` restates item 1 with
   it.
4. **Non-vacuity (Rule 9B).** `LossOffset₀` holds at the quartic member
   `qwDefiance` (`9/2 ≤ 7`), which lies outside the quadratic–linear family, and
   its constructed defiance equilibrium is in the class
   (`qwDefiance_rule_monotone_class_nonempty`).

**Scope.** The class is a restriction on the quantifier: top-selector equilibria
(continuous Target policies) with a nondecreasing realised rule. Equilibria
whose rule falls somewhere are not covered; whether any exist is open. Rule 22:
general in `F`. Rule 3: no new hypothesis; the result removes one.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.
-/
import Sanctions.Examples.PlacableSenderDefianceValues
import Sanctions.Theory.Equilibrium.DefianceCore
import Sanctions.Examples.ChordEconomyQuarticWitness

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-- The chord economy's lower state chord, in the core's form. -/
theorem core_band : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
    E.glo * (y₂ - y₁) ≤ E.F y₂ s - E.F y₁ s :=
  fun s hs y₁ hy₁ y₂ hy₂ hle => (E.hbandAll s hs y₁ hy₁ y₂ hy₂ hle).1

/-- T2 at compliance `0`: compliance costs at least `ℓ_lo` per unit. -/
theorem core_cost : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
    E.ℓlo * a ≤ E.U_T x 0 s - E.U_T x a s := by
  intro x hx s hs a ha
  have h := E.hUT_costLo x hx s hs 0 zero_mem_I a ha ha.1
  linarith

/-- T4 at full defiance: the pain is at most `c` per unit. -/
theorem core_pain : ∀ x ∈ Icc (0 : ℝ) 1,
    Params.LowerLossSlopeOn (fun s => E.U_T x 0 s) (Icc (0 : ℝ) 1) E.c := by
  intro x hx s₁ hs₁ s₂ hs₂ hle
  have h := E.hUT_painHi x hx 0 zero_mem_I s₁ hs₁ s₂ hs₂ hle
  simp only
  linarith

/-- T6 at full defiance, with the rally envelope `n_lo·s ≥ 0` dropped. -/
theorem core_state : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
    E.vlo * (y₂ - y₁) ≤ E.U_T y₂ 0 s - E.U_T y₁ 0 s := by
  intro s hs y₁ hy₁ y₂ hy₂ hle
  have h := E.hUT_stateLo 0 zero_mem_I s hs y₁ hy₁ y₂ hy₂ hle
  have hn : 0 ≤ E.nlo * s * (y₂ - y₁) := mul_nonneg (mul_nonneg E.hnlo hs.1) (by linarith)
  nlinarith [h, hn]

/-- The core's margin is `LossOffset₀`. -/
theorem core_margin (hTM : E.LossOffset₀) :
    E.c ≤ E.toParams.β_T * E.dlo * E.toParams.defianceSlope E.glo E.vlo := hTM

/-- The core's slope is `g_T⁰`. -/
theorem core_slope : E.toParams.defianceSlope E.glo E.vlo = E.gT₀ := rfl

/-- **The Target's value has lower slope `g_T⁰` in the monotone-rule class**,
with no policy condition. -/
theorem target_lowerSlope_of_rule_monotone (hTM : E.LossOffset₀)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hrule : MonotoneOn (E.rule Eq) Sanctions.S) :
    Params.LowerSlopeOnValueOn Eq.V_T (Icc (0 : ℝ) 1) E.gT₀ :=
  (Eq.lowerSlope_of_rule_monotone E.core_band E.hSlo
    (fun x hx => E.toParams.DD0_of_decreasingDifferencesOn (E.stage_decreasingDifferences x hx))
    (E.toParams.weakCost_of_linearCost E.core_cost E.hℓlo.le) E.core_pain E.core_state
    E.hvlo.le (E.core_margin hTM) hrule).toOn _

/-- **In the monotone-rule class the Target defies at every state**, with no
policy condition. -/
theorem policy_eq_zero_of_rule_monotone (hTM : E.LossOffset₀)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hrule : MonotoneOn (E.rule Eq) Sanctions.S) {x : ℝ} (hx : x ∈ Sanctions.I) :
    Eq.α x = 0 :=
  Eq.policy_eq_zero_of_rule_monotone E.core_band E.hSlo E.stage_decreasingDifferences
    E.core_cost E.hℓlo E.core_pain E.core_state E.hvlo.le (E.core_margin hTM) hrule hx

/-- **Uniqueness in the monotone-rule class.** Under the unrefined loss-offset
margin, every top-selector equilibrium whose realised sanction rule is
nondecreasing in the state has full defiance at every feasible state, the
constructed Sender value `VSstar`, the constructed Target value `VTdef`, and the
constructed response as its rule. Row 46 without its policy condition. -/
theorem unique_equilibrium_of_rule_monotone (hTM : E.LossOffset₀)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hrule : MonotoneOn (E.rule Eq) Sanctions.S) :
    (∀ x ∈ Sanctions.I, Eq.α x = 0) ∧ Eq.V_S = E.VSstar ∧ Eq.V_T = E.VTdef ∧
    ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = E.responsePath E.VSstar x := by
  have hα : ∀ x ∈ Sanctions.I, Eq.α x = 0 :=
    fun x hx => E.policy_eq_zero_of_rule_monotone hTM Eq hrule hx
  exact ⟨hα, E.values_eq_of_policy_zero Eq hα⟩

/-- **Row 46 is a corollary.** `unique_equilibrium_of_monotone_class` follows
from `unique_equilibrium_of_rule_monotone`; its policy condition is not used. -/
theorem unique_equilibrium_of_monotone_class_of_rule_monotone (hTM : E.LossOffset₀)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (_hanti : AntitoneOn Eq.α Sanctions.S) (hrule : MonotoneOn (E.rule Eq) Sanctions.S) :
    (∀ x ∈ Sanctions.I, Eq.α x = 0) ∧ Eq.V_S = E.VSstar ∧ Eq.V_T = E.VTdef ∧
    ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = E.responsePath E.VSstar x :=
  E.unique_equilibrium_of_rule_monotone hTM Eq hrule

/-- **No sanction-free equilibrium on the defiance side.** Under the unrefined
loss-offset margin, no top-selector equilibrium has a realised sanction rule
equal to zero at every feasible state. -/
theorem no_zero_rule_equilibrium (hTM : E.LossOffset₀)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) :
    ¬ ∀ x ∈ Sanctions.I, E.rule Eq x = 0 := by
  intro h0
  have hrule : MonotoneOn (E.rule Eq) Sanctions.S := by
    intro x hx y hy _
    rw [h0 x hx, h0 y hy]
  have hα : ∀ x ∈ Sanctions.I, Eq.α x = 0 :=
    fun x hx => E.policy_eq_zero_of_rule_monotone hTM Eq hrule hx
  have hpos := E.rule_pos_of_policy_zero Eq hα zero_mem_I
  rw [h0 0 zero_mem_I] at hpos
  exact lt_irrefl 0 hpos


end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The patience form of the unrefined margin** (doc 110 item C3a). `LossOffset₀`
holds exactly when the Target's discount factor is at least
`c/(d_lo·v_lo + c·g_lo)`. The bound involves no Sender parameter; it falls as the
Target values entrenchment more (`v_lo`), as the sanction entrenches faster
(`d_lo`) and as entrenchment persists (`g_lo`), and rises with the pain `c`. It is
a sufficient condition, not a threshold: the converse of the margin is refuted at
a constructed equilibrium (`loss_offset_converse_counterexample`). -/
theorem lossOffset₀_iff_βT_ge :
    E.LossOffset₀ ↔ E.c / (E.dlo * E.vlo + E.c * E.glo) ≤ E.β_T := by
  have hden : 0 < E.dlo * E.vlo + E.c * E.glo :=
    add_pos_of_pos_of_nonneg (mul_pos E.hdlo0 E.hvlo) (mul_nonneg E.c_pos.le E.hglo0)
  have h1 : 0 < 1 - E.β_T * E.glo := by linarith [E.βT_glo_lt_one]
  have e : E.β_T * E.dlo * (E.vlo / (1 - E.β_T * E.glo))
      = (E.β_T * E.dlo * E.vlo) / (1 - E.β_T * E.glo) := by ring
  change E.c ≤ E.β_T * E.dlo * (E.vlo / (1 - E.β_T * E.glo)) ↔ _
  rw [e, le_div_iff₀ h1, div_le_iff₀ hden]
  constructor <;> intro h <;> linarith

/-- **A patient enough Target defies in every monotone-rule equilibrium.** If
`β_T ≥ c/(d_lo·v_lo + c·g_lo)`, every top-selector equilibrium whose realised
rule is nondecreasing has full defiance, the constructed values and the
constructed response. A restricted-class, sufficient-condition analogue of a
patience threshold for conflict; it says nothing about equilibria whose rule
falls somewhere, or about patience below the bound. -/
theorem unique_equilibrium_of_patient_target
    (hβ : E.c / (E.dlo * E.vlo + E.c * E.glo) ≤ E.β_T)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hrule : MonotoneOn (E.rule Eq) Sanctions.S) :
    (∀ x ∈ Sanctions.I, Eq.α x = 0) ∧ Eq.V_S = E.VSstar ∧ Eq.V_T = E.VTdef ∧
    ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = E.responsePath E.VSstar x :=
  E.unique_equilibrium_of_rule_monotone (E.lossOffset₀_iff_βT_ge.mpr hβ) Eq hrule

end ChordEconomyRelief


/-! ## Non-vacuity at the quartic member (Rule 9B) -/

/-- **The unrefined loss-offset margin holds at the quartic defiance member**:
`c = 9/2 ≤ β_T·d_lo·v_lo/(1 − β_T·g_lo) = (1/2)(2/5)·28/(4/5) = 7`. -/
theorem qwDefiance_lossOffset₀ : qwDefiance.toChordEconomy.LossOffset₀ := by
  change (9 / 2 : ℝ) ≤ 1 / 2 * (2 / 5) * (28 / (1 - 1 / 2 * (2 / 5)))
  norm_num

/-- **The monotone-rule class is inhabited at the quartic member**: its
constructed defiance equilibrium has a nondecreasing realised rule, so
`unique_equilibrium_of_rule_monotone` applies to a member outside the
quadratic–linear family. -/
theorem qwDefiance_rule_monotone_class_nonempty :
    ∃ Eq : qwDefiance.toParams.FeedbackStackelbergEquilibriumTop,
      MonotoneOn (qwDefiance.toChordEconomy.rule Eq) Sanctions.S :=
  ⟨_, (qwDefiance.toChordEconomy.equilibriumTop_mem_monotone_class qwDefiance_lossOffset
    (qwDefiance.toChordEconomyTwoSided.responsePath_monotoneOn_of_margin
      (qw_rallyMargin _ _ _))).2⟩

end

#print axioms Sanctions.Examples.ChordEconomy.target_lowerSlope_of_rule_monotone
#print axioms Sanctions.Examples.ChordEconomy.policy_eq_zero_of_rule_monotone
#print axioms Sanctions.Examples.ChordEconomy.unique_equilibrium_of_rule_monotone
#print axioms Sanctions.Examples.ChordEconomy.unique_equilibrium_of_monotone_class_of_rule_monotone
#print axioms Sanctions.Examples.ChordEconomy.no_zero_rule_equilibrium
#print axioms Sanctions.Examples.ChordEconomyRelief.lossOffset₀_iff_βT_ge
#print axioms Sanctions.Examples.ChordEconomyRelief.unique_equilibrium_of_patient_target
#print axioms Sanctions.Examples.qwDefiance_lossOffset₀
#print axioms Sanctions.Examples.qwDefiance_rule_monotone_class_nonempty

end Examples
end Sanctions
