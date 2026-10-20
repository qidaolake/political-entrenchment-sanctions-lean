/-
Sanctions/Theory/Certificates/PersistenceCertificate.lean

**The persistence-only certificate (debundling round, 2026-08-09).**

`StandardComplianceLocalCoreCertificate_MS` bundles three separable
jobs: constructing an equilibrium, delivering persistence, and beating
the myopic comparator. Downstream, the general-`F` headline consumed the
whole bundle even when it only wanted persistence — so a reader could
not tell which hypotheses paid for which conclusion, and the manuscript's
stated division of labour had no formal counterpart.

This file supplies the persistence-only half. Relative to the MS core
certificate, `StandardCompliancePersistenceCertificate` **drops three
things**, each traced to the conclusion that needed it:

| Dropped | Was paying for |
|---|---|
| `h_target_combined` (P4) | conclusion (vi), the Target-side preference evidence |
| `hMyoCeiling` | Goal 2, dynamic-over-myopic dominance |
| strictness in `hpivot_mem` | Goal 3, finite shock entry — upper half only (below) |

Round BB (2026-09-28, `PersistenceThreeGoals.lean`): of the strict pivot
`max xT xS ∈ (0, 1)`, only the upper half `max xT xS < 1` pays for shock entry.
The lower half `0 < max xT xS` feeds only a strict-positivity conjunct of the
realised sanction, which rows 1 and 2 discard. Round BH-1 (2026-10-06, item
BH1.6): the upper half is not needed as an input either. Ascent at full
sanction on the pre-basin interval `[0, max xT xS]` gives finite shock entry
and implies `max xT xS < 1`; the `_of_preBasinAscent` composites in
`PersistenceThreeGoals.lean` take that one hypothesis instead.

The certificate also weakens the pivot requirement from `max xT xS ∈ (0,1)`
to plain feasibility of the two pivots, which the remaining fields already
carry.

What is dropped is the Target's *preference over sanction levels*. What
survives on the Target side is everything needed to build the
equilibrium in the first place: the value class `D`, its invariance, and
the row-contraction data `β_T`, `L_TS`, `hT_T_op`, `hsuff_T`. Calling
the residue "the Sender side" would be wrong — the Target's Bellman
operator is still contracting on the carrier, and the Target's
equilibrium policy still drives the trajectory and enters the Sender's
substituted objective. The Sender-side conditions proper are the stage
sanction margin, the interval-dominance condition after substituting the
Target policy, and monotonicity of the Sender's carrier values; those,
together with the construction data, deliver the three kinematic
conclusions over a general transition.

The strict pivot returns in
`exists_persistent_equilibrium_after_shock_generalF`. There its upper half
does the shock-entry work and its lower half gives only that theorem's own
strict-positivity conjunct; the older composites in `PersistenceThreeGoals.lean`
ask for the upper half alone, and the `_of_preBasinAscent` composites (round
BH-1) ask for neither half.

## Rule compliance

**Rule 3.** No new assumption: every field is a field of
`StandardComplianceLocalCoreCertificate_MS`, verbatim or weakened, and
`StandardComplianceLocalCoreCertificate_MS.toPersistence` exhibits the
projection. The assumption surface strictly shrinks.

**Rule 15.** The equilibrium is *constructed*, not consumed — the
existence obligation is discharged by the value-class row-contraction
route (`exists_feedbackStackelbergTop_from_valueClass2_with_membership`),
so no `∃ V, BellmanEq V` is hypothesised.

**Rule 22.** The trajectory is evolved by `p.F`. The affine law appears
nowhere in this file, in any of the three axes.

**Round BJ5.1 (2026-10-07).** The static-selector continuity condition, the
joint continuity of the static Sender selector `σ`, was the `Params` field
`σ_continuous`; it is now the class `Params.StaticSelectorContinuous`. The
persistence certificate does not read it. The projection `toPersistence` from
the MS certificate takes `[p.StaticSelectorContinuous]` only because the MS
certificate's type does (its myopic ceiling names the canonical myopic
equilibrium). General in `F`.
-/

import Sanctions.Theory.Certificates.StandardComplianceLocal
import Sanctions.Theory.Basin.SenderPersistence

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The certificate -/

/-- **Persistence-only compliance certificate.**

Carries what it takes to build a forward-looking feedback Stackelberg
equilibrium in a certified carrier and show its realised path never
leaves the high basin — and nothing else. There is no Target-side
sanction-preference hypothesis and no myopic comparator here. -/
structure StandardCompliancePersistenceCertificate where
  /-- Asymmetric value class (carrier choice). -/
  D : p.ValueClass2
  h_inv : D.IsInvariant
  /-- Row-sum contraction inputs; these construct the equilibrium. -/
  β_T : ℝ
  β_S : ℝ
  L_TS : ℝ
  L_ST : ℝ
  hβ_T_nn : 0 ≤ β_T
  hβ_S_nn : 0 ≤ β_S
  hL_TS_nn : 0 ≤ L_TS
  hL_ST_nn : 0 ≤ L_ST
  hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
    dist (D.jointTargetOp_sub h_inv (V, W))
          (D.jointTargetOp_sub h_inv (V', W'))
      ≤ β_T * dist V V' + L_TS * dist W W'
  hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
    dist (D.jointSenderOp_sub h_inv (V, W))
          (D.jointSenderOp_sub h_inv (V', W'))
      ≤ L_ST * dist V V' + β_S * dist W W'
  hsuff_T : β_T + L_TS < 1
  hsuff_S : β_S + L_ST < 1
  /-- High-basin pivots. Only feasibility is required — strict interiority
  was paying for finite shock entry, which is not claimed here. -/
  xT : ℝ
  xS : ℝ
  hxT_mem : xT ∈ Sanctions.I
  hxS_mem : xS ∈ Sanctions.I
  /-- **The LEVEL input** (manuscript P5's stage-margin route): the
  Sender's stage payoff is strictly increasing in the sanction below the
  pivot, uniformly over the carrier. This is *not* the manuscript's
  Assumption A1 — A1 is the interval-dominance direction condition
  carried by `hIDO_on` below. The inherited name
  `h_stage_sender_strictMono` is kept for compatibility with
  `StandardComplianceLocalCoreCertificate_MS`, whose docstring calls this
  "A1 MS-form"; that label conflates level with direction and should not
  be propagated. -/
  h_stage_sender_strictMono :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc (0 : ℝ) (max x (max xT xS)))
  /-- **The DIRECTION input — the manuscript's Assumption A1**: interval
  dominance of the Sender's dynamic objective in `(s, x)` after
  substituting the Target policy. -/
  hIDO_on :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s)
  /-- Carrier-local Sender value monotonicity. -/
  hV_S_mono_carrier :
    ∀ V_S ∈ D.carrier_S, Monotone V_S

/-! ## The MS core certificate projects onto it -/

/-- **Every MS core certificate is a persistence certificate.** Nothing
downstream of the persistence certificate is unavailable to a holder of
the full one; the projection just forgets the Target chord, the myopic
ceiling, and the pivot strictness. -/
def StandardComplianceLocalCoreCertificate_MS.toPersistence [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS) :
    p.StandardCompliancePersistenceCertificate where
  D := C.D
  h_inv := C.h_inv
  β_T := C.β_T
  β_S := C.β_S
  L_TS := C.L_TS
  L_ST := C.L_ST
  hβ_T_nn := C.hβ_T_nn
  hβ_S_nn := C.hβ_S_nn
  hL_TS_nn := C.hL_TS_nn
  hL_ST_nn := C.hL_ST_nn
  hT_T_op := C.hT_T_op
  hT_S_op := C.hT_S_op
  hsuff_T := C.hsuff_T
  hsuff_S := C.hsuff_S
  xT := C.xT
  xS := C.xS
  hxT_mem := C.hxT_mem
  hxS_mem := C.hxS_mem
  h_stage_sender_strictMono := C.h_stage_sender_strictMono
  hIDO_on := C.hIDO_on
  hV_S_mono_carrier := C.hV_S_mono_carrier

/-! ## Internal: pivot arithmetic -/

namespace StandardCompliancePersistenceCertificate

variable {p}

/-- The joint pivot is a feasible state. -/
theorem pivot_mem (C : p.StandardCompliancePersistenceCertificate) :
    max C.xT C.xS ∈ Sanctions.I :=
  ⟨le_trans C.hxT_mem.1 (le_max_left _ _), max_le C.hxT_mem.2 C.hxS_mem.2⟩

/-! ## The construction -/

/-- **Construct the equilibrium together with its persistence basin.**

The workhorse: builds the forward-looking feedback Stackelberg
equilibrium from the row-contraction margins, then assembles the
P4-free Sender persistence basin at the joint pivot. -/
theorem exists_equilibrium_with_persistence_basin
    (C : p.StandardCompliancePersistenceCertificate) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ p.SenderPersistenceBasinTop E.V_S E.α
          (max C.xT C.xS) (max C.xT C.xS) := by
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    C.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership
      C.h_inv C.hβ_T_nn C.hβ_S_nn C.hL_TS_nn C.hL_ST_nn
      C.hT_T_op C.hT_S_op C.hsuff_T C.hsuff_S
  let V_T_sub : C.D.CarrierT := ⟨E.V_T, hVT⟩
  let V_S_sub : C.D.CarrierS := ⟨E.V_S, hVS⟩
  change E.α = C.D.α_on V_T_sub V_S_sub at hα_eq
  refine ⟨E, hVT, hVS, ?_⟩
  refine SenderPersistenceBasinTop.of_stage_sender_margin p
    C.pivot_mem.1 C.pivot_mem
    (C.hV_S_mono_carrier E.V_S hVS) ?_ ?_
  · -- stage Sender margin at the equilibrium policy
    intro x hx
    rw [hα_eq]
    exact C.h_stage_sender_strictMono V_T_sub V_S_sub x
      ⟨le_trans (le_max_right C.xT C.xS) hx.1, hx.2⟩
  · -- interval dominance at the equilibrium policy
    have h := C.hIDO_on V_T_sub V_S_sub
    convert h using 2
    rw [hα_eq]

/-- **Primitive general-`F` persistence.**

There is a forward-looking feedback Stackelberg equilibrium, lying in the
certified carriers, such that from *every* start in the high basin the
realised political state never leaves the basin, the realised sanction
never falls below the pivot, and the realised sanction sequence is
non-decreasing.

No Target-side sanction-preference hypothesis, no myopic comparator, no
strict pivot, and no affine transition: the trajectory is evolved by the
general `p.F`. This is the theorem the manuscript's "conclusions
(i)–(iii) use P1–P3 and P5" sentence cites. -/
theorem exists_persistent_equilibrium_generalF
    (C : p.StandardCompliancePersistenceCertificate) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ ∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS
                  ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  obtain ⟨E, hVT, hVS, hBasin⟩ := C.exists_equilibrium_with_persistence_basin
  refine ⟨E, hVT, hVS, fun x₀ hx₀ => ?_⟩
  -- Equilibrium-anchored route (Rule 1): `E` was just CONSTRUCTED, so the
  -- kinematic free-policy theorem is never consumed here.
  obtain ⟨h1, _h2, h3, h4, _hα_opt⟩ :=
    p.equilibriumTop_senderPersistenceF_long_run_nonDecreasing E hBasin hx₀
  exact ⟨h1, h3, h4⟩

/-- **Primitive general-`F` persistence after a temporary shock.**

The strict pivot and the strict-above-diagonal transition condition are
consumed *here and nowhere else*. The transition condition and the upper
half of the pivot, `max xT xS < 1`, are what make the exogenous shock phase
reach the basin in finite time. The lower half, `hpivot_pos : 0 < max xT xS`,
feeds only the strict-positivity conjunct `0 < sanction` of the conclusion
(round BB, 2026-09-28: rows 1 and 2 discard that conjunct, and
`PersistenceThreeGoals.lean` does without it). During the shock the sanction path
is externally imposed (the Rule-1 transient-shock exception); once it
ends, the optimal dynamics resume and the persistence conclusions apply
unchanged. -/
theorem exists_persistent_equilibrium_after_shock_generalF
    (C : p.StandardCompliancePersistenceCertificate)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    (hpivot_pos : 0 < max C.xT C.xS)
    (hpivot_lt_one : max C.xT C.xS < 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ ∀ x₀ : ℝ, 0 ≤ x₀ → x₀ ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α (p.shockPathF x₀ N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀ N) n) ∧
            (∀ n, 0 < p.dynamicTopLockInSanctionsF E.V_S E.α
                        (p.shockPathF x₀ N) n) ∧
            Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α
                        (p.shockPathF x₀ N)) := by
  obtain ⟨E, hVT, hVS, hBasin⟩ := C.exists_equilibrium_with_persistence_basin
  refine ⟨E, hVT, hVS, fun x₀ hnn hle => ?_⟩
  -- Equilibrium-anchored route (Rule 1). Strict positivity of the realised
  -- sanction is re-derived from the strict pivot rather than taken from the
  -- kinematic theorem's own conjunct.
  obtain ⟨N, h1, h3, h5, _hα_opt⟩ :=
    p.equilibriumTop_senderPersistenceF_temporary_shock_permanent_high E
      hBasin hF_top hpivot_lt_one hpivot_pos hnn hle
  exact ⟨N, h1, h3, fun n => lt_of_lt_of_le hpivot_pos (h3 n), h5⟩

end StandardCompliancePersistenceCertificate

end Params
end AbstractGame

end

end Sanctions
