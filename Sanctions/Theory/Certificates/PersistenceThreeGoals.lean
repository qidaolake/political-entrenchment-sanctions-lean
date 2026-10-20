/-
Sanctions/Theory/Certificates/PersistenceThreeGoals.lean

**The three persistence goals without the Target's sanction preference
(round BB, 2026-09-28; doc 110 item R6(a)).**

Headline rows 1 and 2
(`standardCompliance_three_goals_local_MS_generalF` and
`standardCompliance_three_goals_local_MS_generalF_min_drift_shock`) consume the
MS core certificate `StandardComplianceLocalCoreCertificate_MS`, which carries
the Target combined chord `h_target_combined` (the manuscript's P4 / A2 — the
Target's sanction objective is non-decreasing on the high basin). **None of
the rows' three conclusions uses it.** In the certificate proof
(`StandardComplianceLocalCoreCertificate_MS.three_goals_local_MS_generalF`)
the field only fills `JointPreferenceBasinTop.target_prefers_sanctions`, and
the three goals then read

* Goal 1 (persistence): `xbar_nonneg`, `sender_high_argmax_exists`,
  `top_rule_mono`;
* Goal 2 (dynamic above myopic): the floor from `sender_high_argmax_exists`
  plus the myopic ceiling;
* Goal 3 (shock hysteresis): Goal 1 at the post-shock state; the one conjunct
  of the shock lemma that P4 feeds is discarded.

The P4-free route already existed up to Goal 1:
`StandardCompliancePersistenceCertificate` (the MS certificate minus
`h_target_combined`, `hMyoCeiling` and the strict pivot) with
`exists_persistent_equilibrium_generalF` and
`exists_persistent_equilibrium_after_shock_generalF`. This file adds the
composites that return the *full* conclusion of rows 1 and 2 from that
certificate plus exactly the hypotheses the remaining goals use:

| Theorem | Extra hypotheses | Conclusion |
|---|---|---|
| `two_goals_generalF` | myopic ceiling | Goals 1–2 of rows 1–2 |
| `three_goals_generalF_of_preBasinAscent` | myopic ceiling, ascent on `[0, x̄]` | row 1's |
| `three_goals_generalF_min_drift_shock_of_preBasinAscent` | same | row 2's |
| `three_goals_generalF` | myopic ceiling, `hF_top`, pivot `< 1` | row 1's, verbatim |
| `three_goals_generalF_min_drift_shock` | myopic ceiling, `StrictAdjustment`, pivot `< 1` | row 2's, verbatim |

Two `example`s check that rows 1 and 2 are recovered in their exact statements
from an MS certificate through `toPersistence`, reading its myopic ceiling and
only the **upper** half of its pivot field.

## Round BH-1 (item BH1.6, 2026-10-06): no pivot bound at all

The first three rows of the table are new. `two_goals_generalF` returns Goals 1
and 2 from the certificate and the myopic ceiling, with no transition
hypothesis. The two `_of_preBasinAscent` composites replace `hF_top` (or
`StrictAdjustment`) together with `max xT xS < 1` by one hypothesis: full
sanction strictly raises every state in `[0, x̄]`, `x̄ = max xT xS`
(`LocalisedShockEntry.lean`). The pivot bound is then not needed, because
finite shock entry is proved from the attained minimum drift on the compact
interval `[0, x̄]`, and that drift is positive by the ascent hypothesis alone.
So the new composites need neither the Target combined chord (P4), nor the
strict pivot, nor `max xT xS < 1`. The two older composites are now their
corollaries, and further `example`s check that the two pinned pre-basin rows
(`standardCompliance_three_goals_local_MS_generalF_of_preBasinAscent` and its
minimum-drift form) are recovered from an MS certificate through
`toPersistence`, reading only its myopic ceiling.

## The pivot's strict lower bound is not needed

The MS certificate's `hpivot_mem : max xT xS ∈ (0, 1)` is used in rows 1 and 2
in three ways: `0 ≤ max xT xS` (which `hxT_mem` already gives), `max xT xS < 1`
(which finite shock entry needs), and `0 < max xT xS`. The last feeds only
`hsbar_pos` of `jointPreferenceBasinTopF_temporary_shock_permanent_high`,
and `hsbar_pos` is used only for the strict-positivity conjunct of the
realised sanction, which rows 1 and 2 discard. The composites here therefore
ask for `max xT xS < 1` alone. The upper bound is used by finite shock entry.
Under an affine transition (`δ < 1`) the full-sanction path from `0` stays
below `1`, so this route cannot deliver the shock goal at a pivot equal to
`1`. No Lean counterexample to the pivot-`1` statement is exhibited. The
`_of_preBasinAscent` composites (round BH-1) do not take the upper bound as a
hypothesis: ascent at full sanction on `[0, x̄]` already forces `x̄ < 1`
(`lt_one_of_preBasinAscent`), so the bound is a consequence, not an input.

## Scope (Rule 9)

Each theorem asserts the existence of **one constructed** equilibrium in the
certified carrier (the contraction fixed point), not a property of every
equilibrium; the persistence, dominance and shock conclusions are about that
equilibrium. The certificate is universal-over-carrier in its level and
direction inputs, as before. No witness is exhibited here; non-vacuity is
inherited from the MS witnesses, each of which projects onto the persistence
certificate, and each of which also satisfies P4 and `0 < x̄`. No member
outside the MS class satisfying the myopic ceiling is exhibited (Rule 9B: the
extra generality is as yet unwitnessed).

## Rule compliance

**Rule 1.** The equilibrium is constructed from the value-class row
contraction; the Target's policy is its Bellman-optimal equilibrium policy and
the Sender's action is the upper dynamic argmax. The shock phase is the
exogenous transient-shock exception; the natural dynamics resume after it.

**Rule 3.** No new assumption. The certificate is the existing
`StandardCompliancePersistenceCertificate`. The myopic ceiling is the MS
certificate's `hMyoCeiling` field verbatim, now a theorem hypothesis; `hF_top`
and `StrictAdjustment` are the existing hypotheses of rows 1 and 2; the pivot
bound is the upper half of the MS field `hpivot_mem`. Every MS certificate
supplies all of them (the `example`s), so the assumption surface strictly
shrinks, by the Target combined chord and by `0 < max xT xS` (as a list of
hypotheses; an economy the smaller list reaches and the MS rows miss is not
exhibited, see Scope). Pre-basin ascent is the existing hypothesis of the pinned
localised siblings of rows 1 and 2 (`StandardComplianceLocalised.lean`), and
both `hF_top` and `StrictAdjustment` imply it below any `x̄ < 1`.

**Rule 15.** Existence is discharged by
`exists_feedbackStackelbergTop_from_valueClass2_with_membership`, through
`exists_equilibrium_with_persistence_basin`; no fixed point is hypothesised.

**Rule 22.** General in `F`. The realised trajectories are
`dynamicTopLockInPathF` and `shockPathF`, both evolved by `p.F`; `hF_top` and
`StrictAdjustment` are ordinal conditions on `F`, not a functional form. The
affine law appears nowhere, on any of the three axes.

**Round BJ5.1 (2026-10-07).** Goal 2 compares the equilibrium with the
canonical myopic equilibrium `p.myopicFeedbackEquilibrium_canonical`, which is
built from the static selector's continuity. That condition, the joint
continuity of the static Sender selector `σ`, was the `Params` field
`σ_continuous`; it is now the class `Params.StaticSelectorContinuous`. So
every composite here whose statement names the canonical myopic equilibrium
(the five theorems of the table, including pinned headline rows 1 and 2, and
the `example`s) takes `[p.StaticSelectorContinuous]` as a binder. The content
is unchanged: the condition moved from the economy to the binder, and every
economy that had the field carries the instance. The persistence certificate
itself does not read it. General in `F`.
-/

import Sanctions.Theory.Certificates.PersistenceCertificate
import Sanctions.Theory.LockIn.LocalisedShockEntry

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

namespace StandardCompliancePersistenceCertificate

variable {p : Sanctions.AbstractGame.Params}

/-- **Goals 1 and 2 from the persistence certificate, general `F`, with no
transition hypothesis (round BH-1, item BH1.6).**

There is a forward-looking feedback Stackelberg equilibrium, lying in the
certified carriers, such that

1. from every start in the high basin `[x̄, 1]` (`x̄ = max(xT, xS)`) the
   general-`F` state path never leaves the basin, the realised sanction never
   falls below `x̄`, and the realised sanction sequence is non-decreasing;
2. on the basin the equilibrium sanction is at least the myopic benchmark's
   (the canonical myopic equilibrium's stage response).

Hypotheses in English: the persistence certificate and the myopic ceiling (the
myopic stage response is at most `max(x, x̄)` on the basin). Nothing about the
transition beyond the `Params` fields, nothing about how the Target ranks
sanction levels (P4), and no bound on the pivot. Against the MS core
`StandardComplianceLocalCoreCertificate_MS.two_goals_local_MS_generalF`, the
dropped hypotheses are the Target combined chord and the strict pivot
`max xT xS ∈ (0, 1)`. In economic terms: persistence in the basin and
dominance over the myopic benchmark come from the Sender's own incentives
(its stage margin below the pivot and interval dominance) once the Target's
equilibrium policy is substituted in; the Target's preference over sanction
levels is not used. General in `F`. -/
theorem two_goals_generalF [p.StaticSelectorContinuous]
    (C : p.StandardCompliancePersistenceCertificate)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
          ≤ max x (max C.xT C.xS)) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x) := by
  obtain ⟨E, hVT, hVS, hBasin⟩ := C.exists_equilibrium_with_persistence_basin
  refine ⟨E, hVT, hVS, fun x₀ hx₀ => ?_, ?_⟩
  · -- Goal 1: equilibrium-anchored persistence over the Sender basin (no P4).
    obtain ⟨h1, _h2, h3, h4, _hα_opt⟩ :=
      p.equilibriumTop_senderPersistenceF_long_run_nonDecreasing E hBasin hx₀
    exact ⟨h1, h3, h4⟩
  · -- Goal 2: the Sender floor plus the myopic ceiling.
    exact p.ruleDom_of_dynamic_floor_and_myopic_ceiling
      (SenderPersistenceBasinTop.level_dyn_top p hBasin) hMyoCeiling

/-- **The three persistence goals with the minimum-drift shock bound, from
pre-basin ascent (round BH-1, item BH1.6).**

Goals 1 and 2 as in `two_goals_generalF`. The shock goal: the full-sanction
drift `F(x, 1) − x` attains a positive minimum `η` on `[0, x̄]`, and the single
shock length `⌈x̄ / η⌉` puts every initial state in `[0, 1]` into the basin,
after which the equilibrium path stays there with sanctions at least `x̄`.

Hypotheses in English: the persistence certificate; the myopic ceiling; and
full sanction strictly raises every state in `[0, x̄]` (pre-basin ascent). The
binder `[p.StaticSelectorContinuous]` (round BJ5.1, 2026-10-07) says the
Sender's static best response is continuous in the state and the compliance
level: it was a `Params` field, and it is now stated here because Goal 2's
comparator, the canonical myopic equilibrium, is built from it. No content
changed.

The conclusion is headline row 2's, verbatim. Against row 2 and against
`three_goals_generalF_min_drift_shock`, the dropped hypotheses are the Target
combined chord (P4), the strict lower bound on the pivot, the pivot bound
`x̄ < 1` (a consequence of pre-basin ascent, `lt_one_of_preBasinAscent`), and
the two-sided strict adjustment F5 on the whole square, which is replaced by
its full-sanction ascent half on `[0, x̄]` only. In economic terms: a temporary
full sanction needs to push the state up only below the basin; inside the
basin the Sender's own incentives keep sanctions high. General in `F`. -/
theorem three_goals_generalF_min_drift_shock_of_preBasinAscent [p.StaticSelectorContinuous]
    (C : p.StandardCompliancePersistenceCertificate)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
          ≤ max x (max C.xT C.xS))
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) (max C.xT C.xS), x < p.F x 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
             ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ η : ℝ, 0 < η
        ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (max C.xT C.xS),
            η = p.fullShockDrift xmin)
        ∧ (∀ x ∈ Set.Icc (0 : ℝ) (max C.xT C.xS),
            η ≤ p.fullShockDrift x)
        ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))
              ∈ Set.Icc (max C.xT C.xS) 1
          ∧ (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))) n
                    ∈ Set.Icc (max C.xT C.xS) 1)
          ∧ (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))) n) := by
  obtain ⟨E, hVT, hVS, hpaths, hdom⟩ := C.two_goals_generalF hMyoCeiling
  obtain ⟨η, hη_pos, hη_attains, hη, hentry⟩ :=
    p.shockPathF_exists_min_drift_uniform_natCeil_bound_of_preBasinAscent
      C.pivot_mem.1 hF_top_pre
  refine ⟨E, hVT, hVS, hpaths, hdom, η, hη_pos, hη_attains, hη, ?_⟩
  intro x₀shock hx₀shock
  have hNentry := hentry x₀shock hx₀shock _ le_rfl
  obtain ⟨hinv, hfloor, _⟩ := hpaths _ hNentry
  exact ⟨hNentry, hinv, hfloor⟩

/-- **The three persistence goals from pre-basin ascent, row-1 shape (round
BH-1, item BH1.6).**

Goals 1 and 2 as in `two_goals_generalF`; and for every initial state in
`[0, 1]` some finite full-sanction shock after which the equilibrium path stays
in the basin with sanctions at least `x̄` forever.

Hypotheses in English: the persistence certificate; the myopic ceiling; and
full sanction strictly raises every state in `[0, x̄]`. The binder
`[p.StaticSelectorContinuous]` (round BJ5.1, 2026-10-07) says the Sender's
static best response is continuous in the state and the compliance level: it
was a `Params` field, and it is now stated here because Goal 2's comparator,
the canonical myopic equilibrium, is built from it. No content changed.

The conclusion is headline row 1's, verbatim. Against row 1 and against
`three_goals_generalF`, the dropped hypotheses are the Target combined chord
(P4), the strict lower bound on the pivot, the pivot bound `x̄ < 1`, and the
global ascent `x < F(x, 1)` on `[0, 1)`, which is needed only on `[0, x̄]`.
Proved as the corollary of the minimum-drift form with the shock length
`⌈x̄ / η⌉`. General in `F`. -/
theorem three_goals_generalF_of_preBasinAscent [p.StaticSelectorContinuous]
    (C : p.StandardCompliancePersistenceCertificate)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
          ≤ max x (max C.xT C.xS))
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) (max C.xT C.xS), x < p.F x 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀shock N) n)) := by
  obtain ⟨E, hVT, hVS, hpaths, hdom, η, -, -, -, hshock⟩ :=
    C.three_goals_generalF_min_drift_shock_of_preBasinAscent hMyoCeiling hF_top_pre
  refine ⟨E, hVT, hVS, hpaths, hdom, ?_⟩
  intro x₀shock h_nn h_le
  obtain ⟨-, h1, h2⟩ := hshock x₀shock ⟨h_nn, h_le⟩
  exact ⟨_, h1, h2⟩

/-- **The three persistence goals, general `F`, without the Target combined
chord.**

There is a forward-looking feedback Stackelberg equilibrium, lying in the
certified carriers, such that

1. from every start in the high basin `[x̄, 1]` (`x̄ = max(xT, xS)`) the
   general-`F` state path never leaves the basin, the realised sanction never
   falls below `x̄`, and the realised sanction sequence is non-decreasing;
2. on the basin the equilibrium sanction is at least the myopic benchmark's
   (the canonical myopic equilibrium's stage response);
3. after a temporary full-sanction shock of some finite length, from any
   initial state in `[0, 1]`, the post-shock equilibrium path is in the basin
   and its sanction is at least `x̄` forever.

Hypotheses in English: the persistence certificate (the equilibrium
construction data, the Sender's stage margin below the pivot, interval
dominance of the Sender's forward-looking objective, and a non-decreasing
Sender value on the carrier); the myopic ceiling (the myopic stage response is
at most `max(x, x̄)` on the basin); `x < F(x, 1)` on `[0, 1)` (full sanctions
raise the state below the top); and `x̄ < 1`.

The conclusion is headline row 1's, verbatim. There is no hypothesis on how
the Target ranks sanction levels, and no strict lower bound on the pivot.
Round BH-1: proved as the corollary of `three_goals_generalF_of_preBasinAscent`,
since global ascent and `x̄ < 1` give ascent on `[0, x̄]`
(`preBasinAscent_of_hF_top`). The statement is unchanged. -/
theorem three_goals_generalF [p.StaticSelectorContinuous]
    (C : p.StandardCompliancePersistenceCertificate)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
          ≤ max x (max C.xT C.xS))
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    (hpivot_lt_one : max C.xT C.xS < 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀shock N) n)) :=
  C.three_goals_generalF_of_preBasinAscent hMyoCeiling
    (p.preBasinAscent_of_hF_top hF_top hpivot_lt_one)

/-- **The three persistence goals with the minimum-drift shock bound, general
`F`, without the Target combined chord.**

Goals 1 and 2 as in `three_goals_generalF`. The shock goal is quantitative:
under strict adjustment, the full-sanction drift `F(x, 1) − x` attains a
positive minimum `η` on `[0, x̄]`, and the single shock length
`⌈x̄ / η⌉` puts every initial state in `[0, 1]` into the basin, after which the
equilibrium path stays there with sanctions at least `x̄`.

Hypotheses in English: the persistence certificate; the myopic ceiling;
strict adjustment of the state toward the current sanction; and `x̄ < 1`.

The conclusion is headline row 2's, verbatim. There is no hypothesis on how
the Target ranks sanction levels, and no strict lower bound on the pivot.
Round BH-1: proved as the corollary of
`three_goals_generalF_min_drift_shock_of_preBasinAscent`, since strict
adjustment and `x̄ < 1` give ascent on `[0, x̄]`
(`preBasinAscent_of_strictAdjustment`). The statement is unchanged. -/
theorem three_goals_generalF_min_drift_shock [p.StaticSelectorContinuous]
    (C : p.StandardCompliancePersistenceCertificate)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
          ≤ max x (max C.xT C.xS))
    (hAdj : p.StrictAdjustment)
    (hpivot_lt_one : max C.xT C.xS < 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
             ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ η : ℝ, 0 < η
        ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (max C.xT C.xS),
            η = p.fullShockDrift xmin)
        ∧ (∀ x ∈ Set.Icc (0 : ℝ) (max C.xT C.xS),
            η ≤ p.fullShockDrift x)
        ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))
              ∈ Set.Icc (max C.xT C.xS) 1
          ∧ (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))) n
                    ∈ Set.Icc (max C.xT C.xS) 1)
          ∧ (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))) n) :=
  C.three_goals_generalF_min_drift_shock_of_preBasinAscent hMyoCeiling
    (p.preBasinAscent_of_strictAdjustment hAdj hpivot_lt_one)

end StandardCompliancePersistenceCertificate

/-! ## Rule-13 checks: rows 1 and 2 are recovered without the Target chord

Each `example` states the conclusion of the pinned row verbatim for an MS
certificate `C`, and proves it through `C.toPersistence`, which forgets
`h_target_combined`. From `C` the proof reads the myopic ceiling
`C.hMyoCeiling` and the upper half `C.hpivot_mem.2` of the pivot field, and
nothing else beyond what `toPersistence` copies. -/

variable (p : Sanctions.AbstractGame.Params)

/-- Row 1 (`standardCompliance_three_goals_local_MS_generalF`) through the
P4-free composite. -/
example [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀shock N) n)) :=
  (StandardComplianceLocalCoreCertificate_MS.toPersistence p C).three_goals_generalF
    C.hMyoCeiling hF_top C.hpivot_mem.2

/-- Row 2 (`standardCompliance_three_goals_local_MS_generalF_min_drift_shock`)
through the P4-free composite. -/
example [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (hAdj : p.StrictAdjustment) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
             ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ η : ℝ, 0 < η
        ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (max C.xT C.xS),
            η = p.fullShockDrift xmin)
        ∧ (∀ x ∈ Set.Icc (0 : ℝ) (max C.xT C.xS),
            η ≤ p.fullShockDrift x)
        ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))
              ∈ Set.Icc (max C.xT C.xS) 1
          ∧ (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))) n
                    ∈ Set.Icc (max C.xT C.xS) 1)
          ∧ (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))) n) :=
  (StandardComplianceLocalCoreCertificate_MS.toPersistence p C).three_goals_generalF_min_drift_shock
    C.hMyoCeiling hAdj C.hpivot_mem.2

/-! ## Rule-13 checks for the round BH-1 composites (item BH1.6)

Each `example` states the conclusion of a pinned pre-basin row, or of the MS
Goals-1–2 core, verbatim for an MS certificate `C`, and proves it through
`C.toPersistence` and a new composite. From `C` the proofs read only the myopic
ceiling `C.hMyoCeiling`: neither the Target combined chord nor any half of the
pivot field `C.hpivot_mem`. -/

/-- The MS Goals-1–2 core
(`StandardComplianceLocalCoreCertificate_MS.two_goals_local_MS_generalF`) through
`two_goals_generalF`. -/
example [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x) :=
  StandardCompliancePersistenceCertificate.two_goals_generalF
    (StandardComplianceLocalCoreCertificate_MS.toPersistence p C) C.hMyoCeiling

/-- The pinned pre-basin sibling of row 1
(`standardCompliance_three_goals_local_MS_generalF_of_preBasinAscent`) through
`three_goals_generalF_of_preBasinAscent`. -/
example [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) (max C.xT C.xS), x < p.F x 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀shock N) n)) :=
  StandardCompliancePersistenceCertificate.three_goals_generalF_of_preBasinAscent
    (StandardComplianceLocalCoreCertificate_MS.toPersistence p C) C.hMyoCeiling hF_top_pre

/-- The pinned pre-basin sibling of row 2
(`standardCompliance_three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent`)
through `three_goals_generalF_min_drift_shock_of_preBasinAscent`. -/
example [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) (max C.xT C.xS), x < p.F x 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
             ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ η : ℝ, 0 < η
        ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (max C.xT C.xS),
            η = p.fullShockDrift xmin)
        ∧ (∀ x ∈ Set.Icc (0 : ℝ) (max C.xT C.xS),
            η ≤ p.fullShockDrift x)
        ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))
              ∈ Set.Icc (max C.xT C.xS) 1
          ∧ (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))) n
                    ∈ Set.Icc (max C.xT C.xS) 1)
          ∧ (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))) n) :=
  StandardCompliancePersistenceCertificate.three_goals_generalF_min_drift_shock_of_preBasinAscent
    (StandardComplianceLocalCoreCertificate_MS.toPersistence p C) C.hMyoCeiling hF_top_pre

end Params
end AbstractGame

end

end Sanctions

-- The axiom report below names declarations in full; several names pass the
-- 100-character line limit, which is accepted for these report lines only.
set_option linter.style.longLine false

#print axioms Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.two_goals_generalF
#print axioms Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF_min_drift_shock_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF
#print axioms Sanctions.AbstractGame.Params.StandardCompliancePersistenceCertificate.three_goals_generalF_min_drift_shock
