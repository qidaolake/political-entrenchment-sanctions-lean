/-
Sanctions/Examples/PlacableSenderDefianceEpisode.lean

**Placable episodes, the low basin and the `11` cell at every full-defiance
equilibrium** (renovation item BH3.3, 2026-10-06).

`PlacableSenderEpisode.lean`, the forward-looking obstruction of
`PlacableSenderLowBasin.lean` and the `11` clause of `four_cell_rule_chain`
(`PlacableSenderRegime01.lean`) are stated at the constructed forward-looking
equilibrium `equilibriumTop_of_margin hTM hmargin`. Their proofs read the
loss-offset margin `hTM` and the rally margin `hmargin` only to name that
equilibrium. What they use is that its realised sanction rule is the constructed
response `responsePath VSstar` on `[0, 1]`. Every full-defiance equilibrium
(Target policy `α ≡ 0` on `[0, 1]`) has that rule (`values_eq_of_policy_zero`, no
hypothesis beyond the class). So each result holds at every such equilibrium,
with neither margin:

* `rule_ge_sfloor_of_policy_zero`: the realised rule is at least the sanction
  floor `b = σ(0, 0)` at every feasible state;
* `placable_post_episode_nonexit_of_policy_zero` and
  `placable_highEpisode_nonexit_of_policy_zero`: an imposed episode that ends in
  `[b, 1]` (or a non-maximal episode held long enough) is followed by permanent
  residence in `[b, 1]` and a sanction never below `b`;
* `no_lowBasin_containing_zero_of_policy_zero`: no low basin containing `0`
  satisfies the low-basin level condition;
* `rule_gt_stage_of_policy_zero`: the realised rule lies strictly above the stage
  selector `σ(x, 0)` and strictly below one (interiority is still read here);
* `four_cell_rule_chain_of_policy_zero`: the four-cell rule chain with the `11`
  cell read at any full-defiance equilibrium. The loss-offset margin stays,
  because it names the `10` cell's equilibrium; the rally margin is gone.

The constructed-equilibrium statements are re-derived from these forms at the
foot of the file (the `_via_policy_zero` names), and `type_of%` checks confirm
that each re-derivation has the original's exact statement. The originals are
untouched (the round BB pattern of `PlacableSenderReliefAtDefiance.lean`).

**Scope and existence (Rule 9).** Each statement quantifies over full-defiance
equilibria, so it says nothing for an economy that has none. Existence is a
separate fact. A full-defiance equilibrium exists exactly when full defiance is a
Target best reply at the defiance-profile values (`exists_defiance_equilibrium_iff`,
`PlacableSenderPatienceExistence.lean`); the constructed `equilibriumTop` is one under
the loss-offset margin and a nondecreasing response, hence under (LO) and (RM).
Nothing here concerns equilibria in which the Target complies somewhere.

Rule 22: general in `F` (chord conditions only). Rule 3: no new hypothesis; the
loss-offset and rally margins are dropped where they only named the equilibrium.
-/
import Sanctions.Examples.PlacableSenderDefianceValues
import Sanctions.Examples.PlacableSenderLowBasin

namespace Sanctions
namespace Examples

open Set AbstractGame Sanctions.TransitionChords

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## The sanction floor and the imposed episodes -/

/-- **The realised rule of every full-defiance equilibrium is at least the sanction
floor** `b = σ(0, 0)`, at every feasible state. General in `F`. This is
`dynamicRule_ge_sfloor` at any equilibrium whose Target policy is zero on `[0, 1]`.
That lemma takes the loss-offset margin and the rally margin, but only to name the
constructed equilibrium; neither is assumed here. Every full-defiance equilibrium
realises the constructed response (`values_eq_of_policy_zero`), which exceeds the
stage selector and so is at least its value at state `0`. -/
theorem rule_ge_sfloor_of_policy_zero (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.sfloor ≤ E.toParams.dynamicTopRealizedRule Eq.V_S Eq.α x := by
  change E.sfloor ≤ E.toParams.dynamicEquilibriumRule Eq x
  rw [(E.values_eq_of_policy_zero Eq hα).2.2 x hx]
  exact E.responsePath_ge_sfloor E.VSstar_mem hx

/-- **Post-episode non-exit at every full-defiance equilibrium.** An imposed
sanction schedule that ends in `[b, 1]`, with `b = σ(0, 0)` the sanction floor, is
followed under any full-defiance equilibrium by permanent residence in `[b, 1]`, a
realised sanction never below `b`, and no relief cutoff strictly below `b`. General
in `F`. This is `placable_post_episode_nonexit_generalF` with the loss-offset margin
and the rally margin dropped: they only named the constructed equilibrium, and the
weak-floor input now comes from `rule_ge_sfloor_of_policy_zero`. -/
theorem placable_post_episode_nonexit_of_policy_zero
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ)
    (hT : E.toParams.episodePath u x₀ T ∈ Set.Icc (E.sfloor) 1) :
    (∀ n, E.toParams.splicedPath Eq.V_S Eq.α u T x₀ (T + n) ∈ Set.Icc (E.sfloor) 1) ∧
    (∀ n, E.sfloor ≤ E.toParams.splicedSanction Eq.V_S Eq.α u T x₀ (T + n)) ∧
    (∀ q, q < E.sfloor → ∀ n,
      ¬ E.toParams.splicedSanction Eq.V_S Eq.α u T x₀ (T + n) ≤ q) :=
  E.toParams.equilibriumTop_post_episode_nonexit_generalF Eq u T x₀ (by rw [E.F_diag])
    (fun x hx => E.rule_ge_sfloor_of_policy_zero Eq hα ⟨le_trans E.sfloor_mem.1 hx.1, hx.2⟩) hT

/-- **Entry under a non-maximal episode, then non-exit, at every full-defiance
equilibrium.** A schedule held at or above some `h > b` for at least the derived
horizon ends in `[b, 1]` from every start, and the post-episode conclusions follow.
General in `F`. This is `placable_highEpisode_nonexit_generalF` with the loss-offset
margin and the rally margin dropped; strict adjustment still comes from the positive
lower sanction chord (`toParams_strictAdjustment`). -/
theorem placable_highEpisode_nonexit_of_policy_zero
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {h : ℝ} (hxh : E.sfloor < h) (hh1 : h ≤ 1)
    {u : ℕ → ℝ} (hu_mem : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) {T : ℕ} (hu : ∀ n < T, h ≤ u n)
    (hT : E.toParams.highEpisodeHorizon h (E.sfloor) ≤ T)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n, E.toParams.splicedPath Eq.V_S Eq.α u T x₀ (T + n) ∈ Set.Icc (E.sfloor) 1) ∧
    (∀ n, E.sfloor ≤ E.toParams.splicedSanction Eq.V_S Eq.α u T x₀ (T + n)) ∧
    (∀ q, q < E.sfloor → ∀ n,
      ¬ E.toParams.splicedSanction Eq.V_S Eq.α u T x₀ (T + n) ≤ q) :=
  E.toParams.equilibriumTop_highEpisode_nonexit_generalF Eq
    E.toParams_strictAdjustment E.sfloor_mem.1 hxh hh1 (by rw [E.F_diag])
    (fun x hx => E.rule_ge_sfloor_of_policy_zero Eq hα ⟨le_trans E.sfloor_mem.1 hx.1, hx.2⟩)
    hu_mem hu hT hx₀

/-! ## The low basin -/

/-- **No low basin containing `0` at any full-defiance equilibrium.** At state `0`
the realised rule is at least the sanction floor `b = σ(0, 0) > 0`, while
`min(0, s̄_low) ≤ 0`, so the low-basin level condition fails on every `[0, x̄]`.
General in `F`. This is `dynamic_no_lowBasin_containing_zero` with the loss-offset
margin and the rally margin dropped: they only named the constructed equilibrium.
The obstruction is still about full-defiance equilibria, not every equilibrium of
the same primitives. -/
theorem no_lowBasin_containing_zero_of_policy_zero
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {xbar : ℝ} (hxbar : 0 ≤ xbar) (sbar_low : ℝ) :
    ¬ ∀ x ∈ Set.Icc (0 : ℝ) xbar,
      E.toParams.dynamicTopRealizedRule Eq.V_S Eq.α x ≤ min x sbar_low := by
  intro h
  have h0 := h 0 ⟨le_rfl, hxbar⟩
  have hb := E.rule_ge_sfloor_of_policy_zero Eq hα zero_mem_I
  have hpos : 0 < E.sfloor := E.sfloor_pos
  have : min (0 : ℝ) sbar_low ≤ 0 := min_le_left _ _
  linarith

/-! ## The `11` cell -/

/-- **The `11` cell at every full-defiance equilibrium**: at every feasible state the
realised rule lies strictly above the stage selector `σ(x, 0)` and strictly below
one. General in `F`. This is the `11` clause of `four_cell_rule_chain` without the
loss-offset margin and the rally margin, which only named the constructed
equilibrium. Interiority stays: the lower bound reads its stage part `u_hi < q`, and
the upper bound reads the cap `A/q < 1`. -/
theorem rule_gt_stage_of_policy_zero (hInt : E.Interior)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.σ x 0 < E.toParams.dynamicEquilibriumRule Eq x ∧
      E.toParams.dynamicEquilibriumRule Eq x < 1 := by
  rw [(E.values_eq_of_policy_zero Eq hα).2.2 x hx]
  exact ⟨E.responsePath_gt_stage (E.uhi_lt_q hInt) E.VSstar_mem hx,
    lt_of_le_of_lt (E.responsePath_le_cap E.VSstar_mem hx) (E.cap_lt_one hInt)⟩

end ChordEconomy

namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided ChordEconomyRelief

variable (E : ChordEconomyCs)

/-- **The common-state rule chain across the four cells, with the `11` cell at any
full-defiance equilibrium.** At every feasible state the realised sanction is zero in
the constructed `00` and `01` cells, equals the positive stage selector in the
constructed `10` cell, and in the `11` cell, read at any equilibrium whose Target
policy is zero on `[0, 1]`, lies strictly above the `10` rule and strictly below one.
General in `F`. This is `four_cell_rule_chain` without the rally margin, which only
named the constructed `11` equilibrium. The loss-offset margin stays because it names
the `10` cell's equilibrium; interiority, placability, the sharp relief margin and
zero-sanction neutrality stay for the other cells. -/
theorem four_cell_rule_chain_of_policy_zero (hInt : E.Interior) (hTM : E.LossOffset)
    (hP : E.Placable) (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo)
    (hN : E.ZeroSanctionNeutral)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    ∀ x ∈ Sanctions.I,
      E.pM.dynamicEquilibriumRule
          (E.myopicEquilibriumTop hInt (E.stageRelief_of_reliefSharp hrelief) hP) x = 0 ∧
      E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN) x = 0 ∧
      0 < E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x ∧
      E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x
        < E.toParams.dynamicEquilibriumRule Eq x ∧
      E.toParams.dynamicEquilibriumRule Eq x < 1 := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := E.rule_gt_stage_of_policy_zero hInt Eq hα hx
  refine ⟨(E.myopicRule_eq_zero hInt (E.stageRelief_of_reliefSharp hrelief) hP) hx,
      (E.senderOnlyRule_eq_zero' hInt hP) hrelief hN hx, ?_, ?_, hhi⟩
  · rw [(E.targetOnlyRule_eq_stage hTM) hx]
    exact E.stage_argmax_pos hx
  · rw [(E.targetOnlyRule_eq_stage hTM) hx]
    exact hlo

end ChordEconomyCs

/-! ## The constructed-equilibrium statements as corollaries

Each theorem below has exactly the statement of an original at the constructed
equilibrium `equilibriumTop_of_margin hTM hmargin`, and is proved from the
full-defiance form at that equilibrium (its Target policy is zero by construction).
Like the originals, they are stated on `ChordEconomyTwoSided` since renovation item BJ3.1
(2026-10-07), as the rally margin reads the two-sided curvature data. -/

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- `dynamicRule_ge_sfloor`, re-derived from `rule_ge_sfloor_of_policy_zero`. General
in `F`. -/
theorem dynamicRule_ge_sfloor_via_policy_zero (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.sfloor ≤ E.toParams.dynamicTopRealizedRule ((E.equilibriumTop_of_margin hTM) hmargin).V_S
      ((E.equilibriumTop_of_margin hTM) hmargin).α x :=
  E.rule_ge_sfloor_of_policy_zero _ (fun _ _ => rfl) hx

/-- `placable_post_episode_nonexit_generalF`, re-derived from
`placable_post_episode_nonexit_of_policy_zero`. General in `F`. -/
theorem placable_post_episode_nonexit_generalF_via_policy_zero (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ)
    (hT : E.toParams.episodePath u x₀ T ∈ Set.Icc (E.sfloor) 1) :
    (∀ n, E.toParams.splicedPath ((E.equilibriumTop_of_margin hTM) hmargin).V_S
        ((E.equilibriumTop_of_margin hTM) hmargin).α u T x₀ (T + n) ∈ Set.Icc (E.sfloor) 1) ∧
    (∀ n, E.sfloor ≤ E.toParams.splicedSanction ((E.equilibriumTop_of_margin hTM) hmargin).V_S
        ((E.equilibriumTop_of_margin hTM) hmargin).α u T x₀ (T + n)) ∧
    (∀ q, q < E.sfloor → ∀ n,
      ¬ E.toParams.splicedSanction ((E.equilibriumTop_of_margin hTM) hmargin).V_S
        ((E.equilibriumTop_of_margin hTM) hmargin).α u T x₀ (T + n) ≤ q) :=
  E.placable_post_episode_nonexit_of_policy_zero _ (fun _ _ => rfl) u T x₀ hT

/-- `placable_highEpisode_nonexit_generalF`, re-derived from
`placable_highEpisode_nonexit_of_policy_zero`. General in `F`. -/
theorem placable_highEpisode_nonexit_generalF_via_policy_zero (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {h : ℝ} (hxh : E.sfloor < h) (hh1 : h ≤ 1)
    {u : ℕ → ℝ} (hu_mem : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) {T : ℕ} (hu : ∀ n < T, h ≤ u n)
    (hT : E.toParams.highEpisodeHorizon h (E.sfloor) ≤ T)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n, E.toParams.splicedPath ((E.equilibriumTop_of_margin hTM) hmargin).V_S
        ((E.equilibriumTop_of_margin hTM) hmargin).α u T x₀ (T + n) ∈ Set.Icc (E.sfloor) 1) ∧
    (∀ n, E.sfloor ≤ E.toParams.splicedSanction ((E.equilibriumTop_of_margin hTM) hmargin).V_S
        ((E.equilibriumTop_of_margin hTM) hmargin).α u T x₀ (T + n)) ∧
    (∀ q, q < E.sfloor → ∀ n,
      ¬ E.toParams.splicedSanction ((E.equilibriumTop_of_margin hTM) hmargin).V_S
        ((E.equilibriumTop_of_margin hTM) hmargin).α u T x₀ (T + n) ≤ q) :=
  E.placable_highEpisode_nonexit_of_policy_zero _ (fun _ _ => rfl) hxh hh1 hu_mem hu hT hx₀

/-- `dynamic_no_lowBasin_containing_zero`, re-derived from
`no_lowBasin_containing_zero_of_policy_zero`. General in `F`. -/
theorem dynamic_no_lowBasin_containing_zero_via_policy_zero (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {xbar : ℝ} (hxbar : 0 ≤ xbar) (sbar_low : ℝ) :
    ¬ ∀ x ∈ Set.Icc (0 : ℝ) xbar,
      E.toParams.dynamicTopRealizedRule ((E.equilibriumTop_of_margin hTM) hmargin).V_S
        ((E.equilibriumTop_of_margin hTM) hmargin).α x ≤ min x sbar_low :=
  E.no_lowBasin_containing_zero_of_policy_zero _ (fun _ _ => rfl) hxbar sbar_low

end ChordEconomyTwoSided

namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided ChordEconomyRelief

variable (E : ChordEconomyCs)

/-- `four_cell_rule_chain`, re-derived from `four_cell_rule_chain_of_policy_zero`.
General in `F`. -/
theorem four_cell_rule_chain_via_policy_zero (hInt : E.Interior) (hTM : E.LossOffset)
    (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    ∀ x ∈ Sanctions.I,
      E.pM.dynamicEquilibriumRule
          (E.myopicEquilibriumTop hInt (E.stageRelief_of_reliefSharp hrelief) hP) x = 0 ∧
      E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN) x = 0 ∧
      0 < E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x ∧
      E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x
        < E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x ∧
      E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x < 1 :=
  E.four_cell_rule_chain_of_policy_zero hInt hTM hP hrelief hN _ (fun _ _ => rfl)

end ChordEconomyCs

/-! ## The corollaries have exactly the original statements

Proof irrelevance makes two proofs of one proposition equal, so the checks below
compare the *types*: each re-derived theorem's type is definitionally equal to the
original's (and is written with the same binders, in the same order). A drift in
either statement breaks the check. -/

example : type_of% @ChordEconomyTwoSided.dynamicRule_ge_sfloor_via_policy_zero
    = type_of% @ChordEconomyTwoSided.dynamicRule_ge_sfloor := rfl

example : type_of% @ChordEconomyTwoSided.placable_post_episode_nonexit_generalF_via_policy_zero
    = type_of% @ChordEconomyTwoSided.placable_post_episode_nonexit_generalF := rfl

example : type_of% @ChordEconomyTwoSided.placable_highEpisode_nonexit_generalF_via_policy_zero
    = type_of% @ChordEconomyTwoSided.placable_highEpisode_nonexit_generalF := rfl

example : type_of% @ChordEconomyTwoSided.dynamic_no_lowBasin_containing_zero_via_policy_zero
    = type_of% @ChordEconomyTwoSided.dynamic_no_lowBasin_containing_zero := rfl

example : type_of% @ChordEconomyCs.four_cell_rule_chain_via_policy_zero
    = type_of% @ChordEconomyCs.four_cell_rule_chain := rfl

end

#print axioms Sanctions.Examples.ChordEconomy.rule_ge_sfloor_of_policy_zero
#print axioms Sanctions.Examples.ChordEconomy.placable_post_episode_nonexit_of_policy_zero
#print axioms Sanctions.Examples.ChordEconomy.placable_highEpisode_nonexit_of_policy_zero
#print axioms Sanctions.Examples.ChordEconomy.no_lowBasin_containing_zero_of_policy_zero
#print axioms Sanctions.Examples.ChordEconomy.rule_gt_stage_of_policy_zero
#print axioms Sanctions.Examples.ChordEconomyCs.four_cell_rule_chain_of_policy_zero

end Examples
end Sanctions
