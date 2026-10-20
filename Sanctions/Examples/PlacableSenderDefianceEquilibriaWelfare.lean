/-
Sanctions/Examples/PlacableSenderDefianceEquilibriaWelfare.lean

**The planner-efficient boundary and relief participation at every full-defiance
equilibrium** (renovation item BH3.4, 2026-10-06).

Two results are stated at the constructed forward-looking equilibrium
`equilibriumTop_of_margin hTM hmargin`:

* `PlacableEconomyF.exists_planner_efficient_completion_at_equilibrium`
  (`PlacableSenderWelfareCompletion.lean`): on the boundary `r = n = 0` a
  positive-weight completion makes the equilibrium's play planner-optimal at
  `β_P = β_S`;
* `ChordEconomyTwoSided.relief_participation_of_margin` and its four-premise form
  `relief_participation_of_margin_at_defiance`
  (`PlacableSenderReliefParticipation.lean`, `PlacableSenderReliefAtDefiance.lean`):
  an imposed spell of zero sanctions followed by the equilibrium is acceptable to
  neither incumbent.

Both read the equilibrium only through its values and its realised rule. Every
full-defiance equilibrium (Target policy `α ≡ 0` on `[0, 1]`) has the constructed
Sender value `VSstar`, the Target value `VTdef` and the realised rule
`responsePath VSstar` (`values_eq_of_policy_zero`, no hypothesis beyond the class).
So:

* `exists_planner_efficient_completion_of_policy_zero` holds at every
  full-defiance equilibrium with **neither** the loss-offset margin nor the rally
  margin. Neither was used beyond naming the equilibrium, and with `r = 0` the
  rally margin forces a flat transition certificate
  (`flat_of_margin_of_r_eq_zero`), so the boundary clause no longer carries that
  restriction in its statement.
* `relief_participation_of_policy_zero_at_defiance` holds at every full-defiance
  equilibrium under the loss-offset margin and a nondecreasing realised response
  `hmono`, in place of the rally margin. Both are still read: they make the
  carrier Target value `VTstar` exist, and the Target's one-period step uses the
  loss-offset margin. `relief_participation_of_policy_zero` is its any-sequence
  form under `ZeroSanctionNoGain`.

The constructed-equilibrium statements (`exists_planner_efficient_completion_at_equilibrium`,
`relief_participation_of_margin_at_defiance`, `relief_participation_of_margin`) are
re-derived from these forms at the foot of the file (the `_via_policy_zero` names),
and `type_of%` checks confirm each has the original's exact statement. The originals
are untouched.

**Existence (Rule 9).** Each statement quantifies over full-defiance equilibria, so it
says nothing for an economy that has none. A full-defiance equilibrium exists exactly
when full defiance is a Target best reply at the defiance-profile values
(`exists_defiance_equilibrium_iff`, `PlacableSenderPatienceExistence.lean`). The
constructed `equilibriumTop hTM hmono` is one under the loss-offset margin and a
nondecreasing response. The rally margin is a sufficient condition for the latter,
and on the boundary `r = 0` it forces a flat transition certificate
(`flat_of_margin_of_r_eq_zero`). The affine member `placableBoundary` (`r = n = 0`)
inhabits the boundary (`placableBoundary_planner_efficient_at_equilibrium`). No member
with `r = n = 0`, a non-flat transition and a full-defiance equilibrium is exhibited
here, so the gain is that the statement no longer forces flatness, not a new inhabited
regime.

Rule 22: general in `F` (chord conditions only; the completion stays on the
quadratic–linear family, where it represents the payoff). Rule 3: no new hypothesis;
the loss-offset margin and the rally margin are dropped from the planner result, and
the rally margin is weakened to `hmono` in the relief result.
-/
import Sanctions.Examples.PlacableSenderDefianceValues
import Sanctions.Examples.PlacableSenderReliefAtDefiance

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Finset

noncomputable section

/-! ## The planner-efficient boundary -/

namespace PlacableEconomyF

variable (E : PlacableEconomyF)

/-- **The planner-efficient completion at every full-defiance equilibrium.** On the
boundary `r = n = 0` there is a positive-weight completion whose welfare is the
Sender's stage payoff at every state and action. For any top-selector equilibrium of
the member's chord economy whose Target policy is zero on `[0, 1]`, the plan
`equilibriumPlan` is that equilibrium's play (its Target policy and its realised
sanction rule, at every feasible state), and at planner discount `β_S` that play is
optimal against every time-dependent plan over both actions, from every feasible
start. General in `F`. This is `exists_planner_efficient_completion_at_equilibrium`
without the loss-offset margin and without the rally margin. Both only named the
constructed equilibrium; every full-defiance equilibrium realises the constructed
response (`values_eq_of_policy_zero`). Existence of such an equilibrium is a separate
fact (see the module docstring). -/
theorem exists_planner_efficient_completion_of_policy_zero (hr : E.r = 0) (hn : E.n = 0)
    (Eq : E.toChord.toParams.FeedbackStackelbergEquilibriumTop)
    (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    ∃ C : E.WelfareCompletion,
      (∀ x a s, C.welfare x a s = E.toParams.U_S x a s) ∧
      (∀ x : ↥(Sanctions.S : Set ℝ),
        (E.equilibriumPlan x).1.1 = Eq.α x.1 ∧
        (E.equilibriumPlan x).2.1 = E.toChord.toParams.dynamicEquilibriumRule Eq x.1) ∧
      ∀ (π : InfiniteHorizonVerification.MarkovPlan ↥(Sanctions.S : Set ℝ)
            (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
        (x₀ : ↥(Sanctions.S : Set ℝ)),
        InfiniteHorizonVerification.discountedPayoff (E.plannerStage C) E.plannerStep E.βS π x₀
          ≤ InfiniteHorizonVerification.discountedPayoff (E.plannerStage C) E.plannerStep E.βS
              (InfiniteHorizonVerification.stationaryPlan E.equilibriumPlan) x₀ := by
  obtain ⟨C, hW, hopt⟩ := E.exists_planner_efficient_completion hr hn
  exact ⟨C, hW, fun x => ⟨(hα x.1 x.2).symm,
    ((E.toChord.values_eq_of_policy_zero Eq hα).2.2 x.1 x.2).symm⟩, hopt⟩

end PlacableEconomyF

/-! ## Relief participation -/

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **Relief participation at every full-defiance equilibrium, at the Target's
optimum.** Given the loss-offset margin `LossOffset`, a nondecreasing realised
response `hmono`, a feasible start and a nonempty spell, for any top-selector
equilibrium whose Target policy is zero on `[0, 1]`, with that equilibrium's own
values as terminal values:

1. the Sender strictly loses from the spell played against defiance, by at least the
   stage-gain floor `G_S`;
2. the Target weakly loses from it; and
3. defiance is the Target's best compliance sequence during the spell.

General in `F`. This is `relief_participation_of_margin_at_defiance` at any
full-defiance equilibrium, with the rally margin weakened to `hmono` (the margin was
read only to make the response nondecreasing). The loss-offset margin and `hmono`
stay: they make the carrier Target value `VTstar` exist and equal the equilibrium's
`VTdef` (`VTdef_eq_VTstar`), and the Target's one-period step reads the margin.
Existence of such an equilibrium is a separate fact; under these two hypotheses the
constructed `equilibriumTop hTM hmono` is one. -/
theorem relief_participation_of_policy_zero_at_defiance (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {T : ℕ} (hT : 0 < T) :
    (∑ t ∈ range T, E.β_S ^ t * E.toParams.U_S (E.reliefState x₀ t) 0 0
        + E.β_S ^ T * Eq.V_S (Sanctions.clipS' (E.reliefState x₀ T))
        + E.stageGainFloor
      ≤ Eq.V_S (Sanctions.clipS' x₀)) ∧
    (∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) 0 0
        + E.β_T ^ T * Eq.V_T (Sanctions.clipS' (E.reliefState x₀ T))
      ≤ Eq.V_T (Sanctions.clipS' x₀)) ∧
    (∀ a : ℕ → ℝ, (∀ t, a t ∈ Sanctions.I) →
      ∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) (a t) 0
          + E.β_T ^ T * Eq.V_T (Sanctions.clipS' (E.reliefState x₀ T))
        ≤ ∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) 0 0
          + E.β_T ^ T * Eq.V_T (Sanctions.clipS' (E.reliefState x₀ T))) := by
  obtain ⟨hVS, hVT, -⟩ := E.values_eq_of_policy_zero Eq hα
  rw [hVS, hVT, E.VTdef_eq_VTstar hTM hmono]
  exact ⟨E.senderReliefValue_defiance_lt hx₀ hT,
    (E.targetReliefValue_le hTM) hmono hx₀ (fun _ => zero_mem_I) T,
    fun _ ha => (E.targetReliefValue_le_defiance hTM) hmono ha hx₀ T⟩

/-- **Relief participation at every full-defiance equilibrium, for any compliance
sequence.** Under `ZeroSanctionNoGain` as well, the Sender strictly loses and the
Target weakly loses from a nonempty spell played at any compliance sequence in
`[0, 1]`, with any full-defiance equilibrium's own values as terminal values. General
in `F`. This is `relief_participation_of_margin` at any full-defiance equilibrium, with
the rally margin weakened to `hmono`. The proof goes through
`relief_participation_of_policy_zero_at_defiance`: the Sender's spell value at `a` is
at most at defiance (`senderReliefValue_le_defiance`, the only use of
`ZeroSanctionNoGain`), and the Target's is at most at defiance (its own optimum). -/
theorem relief_participation_of_policy_zero (hZ : E.ZeroSanctionNoGain) (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {T : ℕ}
    (hT : 0 < T) :
    (∑ t ∈ range T, E.β_S ^ t * E.toParams.U_S (E.reliefState x₀ t) (a t) 0
        + E.β_S ^ T * Eq.V_S (Sanctions.clipS' (E.reliefState x₀ T))
        + E.stageGainFloor
      ≤ Eq.V_S (Sanctions.clipS' x₀)) ∧
    (∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) (a t) 0
        + E.β_T ^ T * Eq.V_T (Sanctions.clipS' (E.reliefState x₀ T))
      ≤ Eq.V_T (Sanctions.clipS' x₀)) := by
  obtain ⟨hS0, hT0, hbest⟩ :=
    (E.relief_participation_of_policy_zero_at_defiance hTM) hmono Eq hα hx₀ hT
  have hS := E.senderReliefValue_le_defiance hZ ha hx₀ T
  unfold senderReliefValue at hS
  obtain ⟨hVS, -, -⟩ := E.values_eq_of_policy_zero Eq hα
  rw [hVS] at hS0 ⊢
  exact ⟨by linarith, (hbest a ha).trans hT0⟩

end ChordEconomy

/-! ## The constructed-equilibrium statements as corollaries

Each theorem below has exactly the statement of an original at the constructed
equilibrium `equilibriumTop_of_margin hTM hmargin`, and is proved from the
full-defiance form at that equilibrium (its Target policy is zero by construction;
the rally margin gives the nondecreasing response through
`responsePath_monotoneOn_of_margin`). -/

namespace PlacableEconomyF

variable (E : PlacableEconomyF)

/-- `exists_planner_efficient_completion_at_equilibrium`, re-derived from
`exists_planner_efficient_completion_of_policy_zero`. General in `F`. Renovation item BJ2.3
(2026-10-07): as in the original, the loss-offset proof term is
`toChord_lossOffset_of_n_eq_zero`, read without interiority. -/
theorem exists_planner_efficient_completion_at_equilibrium_via_policy_zero
    (hTM : E.LossOffset) (hr : E.r = 0) (hn : E.n = 0)
    (hmargin : E.βS * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.r) :
    ∃ C : E.WelfareCompletion,
      (∀ x a s, C.welfare x a s = E.toParams.U_S x a s) ∧
      (∀ x : ↥(Sanctions.S : Set ℝ),
        (E.equilibriumPlan x).1.1
          = ((E.toChord.equilibriumTop_of_margin (E.toChord_lossOffset_of_n_eq_zero hn hTM))
              (E.toChord_margin hmargin)).α x.1 ∧
        (E.equilibriumPlan x).2.1
          = E.toChord.toParams.dynamicEquilibriumRule
              ((E.toChord.equilibriumTop_of_margin (E.toChord_lossOffset_of_n_eq_zero hn hTM))
                (E.toChord_margin hmargin)) x.1) ∧
      ∀ (π : InfiniteHorizonVerification.MarkovPlan ↥(Sanctions.S : Set ℝ)
            (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
        (x₀ : ↥(Sanctions.S : Set ℝ)),
        InfiniteHorizonVerification.discountedPayoff (E.plannerStage C) E.plannerStep E.βS π x₀
          ≤ InfiniteHorizonVerification.discountedPayoff (E.plannerStage C) E.plannerStep E.βS
              (InfiniteHorizonVerification.stationaryPlan E.equilibriumPlan) x₀ :=
  E.exists_planner_efficient_completion_of_policy_zero hr hn _ (fun _ _ => rfl)

end PlacableEconomyF

/-! The two relief-participation corollaries below are stated on `ChordEconomyTwoSided`,
like their originals, since renovation item BJ3.1 (2026-10-07): the rally margin reads the
two-sided curvature data. -/

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- `relief_participation_of_margin_at_defiance`, re-derived from
`relief_participation_of_policy_zero_at_defiance`. General in `F`. -/
theorem relief_participation_of_margin_at_defiance_via_policy_zero (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {T : ℕ} (hT : 0 < T) :
    (∑ t ∈ range T, E.β_S ^ t * E.toParams.U_S (E.reliefState x₀ t) 0 0
        + E.β_S ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_S
            (Sanctions.clipS' (E.reliefState x₀ T))
        + E.stageGainFloor
      ≤ ((E.equilibriumTop_of_margin hTM) hmargin).V_S (Sanctions.clipS' x₀)) ∧
    (∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) 0 0
        + E.β_T ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_T
            (Sanctions.clipS' (E.reliefState x₀ T))
      ≤ ((E.equilibriumTop_of_margin hTM) hmargin).V_T (Sanctions.clipS' x₀)) ∧
    (∀ a : ℕ → ℝ, (∀ t, a t ∈ Sanctions.I) →
      ∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) (a t) 0
          + E.β_T ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_T
              (Sanctions.clipS' (E.reliefState x₀ T))
        ≤ ∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) 0 0
          + E.β_T ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_T
              (Sanctions.clipS' (E.reliefState x₀ T))) :=
  (E.relief_participation_of_policy_zero_at_defiance hTM)
    (E.responsePath_monotoneOn_of_margin hmargin) _ (fun _ _ => rfl) hx₀ hT

/-- `relief_participation_of_margin`, re-derived from
`relief_participation_of_policy_zero`. General in `F`. -/
theorem relief_participation_of_margin_via_policy_zero (hZ : E.ZeroSanctionNoGain)
    (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {T : ℕ}
    (hT : 0 < T) :
    (∑ t ∈ range T, E.β_S ^ t * E.toParams.U_S (E.reliefState x₀ t) (a t) 0
        + E.β_S ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_S
            (Sanctions.clipS' (E.reliefState x₀ T))
        + E.stageGainFloor
      ≤ ((E.equilibriumTop_of_margin hTM) hmargin).V_S (Sanctions.clipS' x₀)) ∧
    (∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) (a t) 0
        + E.β_T ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_T
            (Sanctions.clipS' (E.reliefState x₀ T))
      ≤ ((E.equilibriumTop_of_margin hTM) hmargin).V_T (Sanctions.clipS' x₀)) :=
  (E.relief_participation_of_policy_zero hZ hTM)
    (E.responsePath_monotoneOn_of_margin hmargin) _ (fun _ _ => rfl) hx₀ ha hT

end ChordEconomyTwoSided

/-! ## The corollaries have exactly the original statements

Proof irrelevance makes two proofs of one proposition equal, so the checks below
compare the *types*: each re-derived theorem's type is definitionally equal to the
original's (and is written with the same binders, in the same order). A drift in
either statement breaks the check. -/

example :
    type_of% @PlacableEconomyF.exists_planner_efficient_completion_at_equilibrium_via_policy_zero
      = type_of% @PlacableEconomyF.exists_planner_efficient_completion_at_equilibrium := rfl

example : type_of% @ChordEconomyTwoSided.relief_participation_of_margin_at_defiance_via_policy_zero
    = type_of% @ChordEconomyTwoSided.relief_participation_of_margin_at_defiance := rfl

example : type_of% @ChordEconomyTwoSided.relief_participation_of_margin_via_policy_zero
    = type_of% @ChordEconomyTwoSided.relief_participation_of_margin := rfl

end

#print axioms PlacableEconomyF.exists_planner_efficient_completion_of_policy_zero
#print axioms ChordEconomy.relief_participation_of_policy_zero_at_defiance
#print axioms ChordEconomy.relief_participation_of_policy_zero

end Examples
end Sanctions
