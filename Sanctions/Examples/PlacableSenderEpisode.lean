/-
Sanctions/Examples/PlacableSenderEpisode.lean

**The finite-episode theorem specialised to a chord economy's constructed
forward-looking equilibrium** (doc 68, L5; on the abstract payoffs since round
AV, 2026-09-25, doc 104).

At `E := equilibriumTop_of_margin hmargin` the realised sanction exceeds the
stage selector at every state, hence exceeds the sanction floor
`b := σ(0, 0)` (the stage selector at state `0`; `u₀/q` on the
quadratic–linear family). With pivot and floor both equal to `b` — `F(b, b) = b` by the diagonal —
the weak-floor hypotheses of `equilibriumTop_post_episode_nonexit_generalF` are
discharged from the economy's own primitives, and an imposed sanction episode
that ends in `[b, 1]` is followed by permanent residence there with the
sanction never below `b`. The non-maximal-episode entry clause follows the same
way from `equilibriumTop_highEpisode_nonexit_generalF`, strict adjustment being
a consequence of the positive lower sanction chord.

**Scope.** This is weak basin invariance and a sanction floor, under the rally
margin the composed equilibrium already needs. It is not the ratchet
`R(x) ≥ x` on `[b,1]` (false at the top, where the response is interior), not
a nondecreasing sanction path, and not hysteresis: at the affine member the
closed loop contracts, and the unshocked path also settles above `b`. The
episode is not shown necessary for entrenchment. Rule 22: general in `F`.

Renovation item BH3.3 (2026-10-06): the loss-offset margin and the rally margin are read
here only to name the constructed equilibrium. The same conclusions hold at every
full-defiance equilibrium with neither margin (`rule_ge_sfloor_of_policy_zero`,
`placable_post_episode_nonexit_of_policy_zero` and
`placable_highEpisode_nonexit_of_policy_zero`, in `PlacableSenderDefianceEpisode.lean`),
and the three statements here are re-derived from them there.

Renovation item BJ3.1 (2026-10-07): the rally margin reads the two-sided curvature data,
so the three margin-form theorems are stated on `ChordEconomyTwoSided` (until then on
`ChordEconomy`, otherwise unchanged); `toParams_strictAdjustment` stays on the base class.
-/
import Sanctions.Examples.PlacableSenderRegimes
import Sanctions.Theory.LockIn.FiniteEpisodePersistence

namespace Sanctions
namespace Examples

open Set AbstractGame Sanctions.TransitionChords

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-- Strict adjustment of the economy's transition, from the positive lower
sanction chord. -/
theorem toParams_strictAdjustment : E.toParams.StrictAdjustment :=
  E.toParams.strictAdjustment_of_sanctionLowerChord E.hdlo0 E.hSlo

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- The constructed forward-looking rule is at least the sanction floor
`b = σ(0, 0)` at every feasible state (it exceeds the stage selector, which is
at least its value at `0`). The form at every full-defiance equilibrium, without
either margin, is `rule_ge_sfloor_of_policy_zero` (renovation item BH3.3). General in `F`;
on the two-sided extension since renovation item BJ3.1 (2026-10-07). -/
theorem dynamicRule_ge_sfloor (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.sfloor ≤ E.toParams.dynamicTopRealizedRule ((E.equilibriumTop_of_margin hTM) hmargin).V_S
      ((E.equilibriumTop_of_margin hTM) hmargin).α x := by
  have h1 : E.toParams.dynamicTopRealizedRule ((E.equilibriumTop_of_margin hTM) hmargin).V_S
      ((E.equilibriumTop_of_margin hTM) hmargin).α x = E.responsePath E.VSstar x :=
    (E.dynamicRule_eq_responsePath hTM) hmargin hx
  rw [h1]
  exact E.responsePath_ge_sfloor E.VSstar_mem hx

/-- **Post-episode non-exit on a chord economy.** An imposed sanction
schedule that ends in `[b, 1]`, `b = σ(0, 0)` the sanction floor, is followed,
under the constructed forward-looking equilibrium, by permanent residence there,
a realised sanction never below `b`, and no relief cutoff strictly below `b`.
The form at every full-defiance equilibrium, without either margin, is
`placable_post_episode_nonexit_of_policy_zero` (renovation item BH3.3). General in `F`;
on the two-sided extension since renovation item BJ3.1 (2026-10-07). -/
theorem placable_post_episode_nonexit_generalF (hTM : E.LossOffset)
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
  E.toParams.equilibriumTop_post_episode_nonexit_generalF ((E.equilibriumTop_of_margin hTM) hmargin)
    u T x₀ (by rw [E.F_diag])
    (fun x hx => (E.dynamicRule_ge_sfloor hTM) hmargin ⟨le_trans E.sfloor_mem.1 hx.1, hx.2⟩) hT

/-- **Entry under a non-maximal episode, then non-exit, on a chord economy**:
a schedule held at or above some `h > b` for at least the derived horizon ends
in `[b, 1]` from every start, and the conclusions above follow. The form at every
full-defiance equilibrium, without either margin, is
`placable_highEpisode_nonexit_of_policy_zero` (renovation item BH3.3). General in `F`;
on the two-sided extension since renovation item BJ3.1 (2026-10-07). -/
theorem placable_highEpisode_nonexit_generalF (hTM : E.LossOffset)
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
  E.toParams.equilibriumTop_highEpisode_nonexit_generalF ((E.equilibriumTop_of_margin hTM) hmargin)
    E.toParams_strictAdjustment E.sfloor_mem.1 hxh hh1 (by rw [E.F_diag])
    (fun x hx => (E.dynamicRule_ge_sfloor hTM) hmargin ⟨le_trans E.sfloor_mem.1 hx.1,
        hx.2⟩) hu_mem hu hT hx₀

end ChordEconomyTwoSided

end

#print axioms Sanctions.Examples.ChordEconomyTwoSided.placable_post_episode_nonexit_generalF
#print axioms Sanctions.Examples.ChordEconomyTwoSided.placable_highEpisode_nonexit_generalF

end Examples
end Sanctions
