/-
Sanctions/Theory/Certificates/StandardComplianceMain.lean

**Paper-facing theorem names.**

This file is the public API surface for the paper-facing
literal-compliance route. It collects the canonical theorem names
that the manuscript cites; each is a one-line delegation to the
underlying certificate-level theorem.

## Preferred literal-compliance route

* `standardCompliance_three_goals_local_uniform_starts` (preferred
  BCF paper-facing theorem) — universal-start form: consumes the
  start-free `StandardComplianceLocalCoreCertificate` and quantifies
  the path-level conclusions `∀ x₀ ∈ basin, …` (Goal 1) and
  `∀ x₀shock ∈ [0, 1], ∃ N, …` (Goal 3). Matches the manuscript's
  Proposition 1 / Proposition 3 wording verbatim.

## Preferred regime-comparison route

* `standardCompliance_three_goals_local_regime_comparison_uniform_starts`
  (preferred regime-comparison theorem) — adds pathwise dominance of
  the fully forward-looking equilibrium rule
  `dynamicEquilibriumRule E` over the fully myopic equilibrium rule
  `myopicEquilibriumRule C.M` from every basin starting state.
  Requires the opt-in hypothesis `hMyoBasin` (myopic equilibrium
  rule preserves the basin); when that hypothesis is economically
  unavailable, fall back to the bare statewise
  `standardCompliance_three_goals_local_uniform_starts`.

## Fixed-start compatibility theorem

* `standardCompliance_three_goals_local` — fixed-start form: consumes
  the `StandardComplianceLocalCertificate` (which extends the core
  certificate with stored starting states `x₀` / `x₀shock`) and
  proves the path-level conclusions only at those specific states.
  Retained for back-compatibility with documentation that cites
  specific certificate starts; new paper-facing citations should
  prefer the universal-start form above.

## Preferred C¹ route

* `standardCompliance_three_goals_local_C1` — from
  `StandardComplianceLocalCertificateC1`. Carrier-local on the single
  `D_C1.carrier` of `C1BellmanSystem`, but **still single-carrier on
  the C¹ side**; an asymmetric `ValueClass2_C1` analogue is not yet
  available.

## Ordinary-equilibrium existence wrapper

* `standardCompliance_local_equilibriumTop` — returns an equilibrium
  with carrier membership and a `DynamicArgmaxUniqueOnI E.V_S` certificate
  (Sender uniqueness at physical compliance, since round BJ4.3; the
  `_of_senderUnique` sibling returns the full `DynamicArgmaxUnique` form).
  Existence-only (does not return the three goals); downstream
  callers compose with `standardCompliance_three_goals_local` and
  convert via `σ_dyn_eq_σ_dyn_top_of_unique` +
  `FeedbackStackelbergEquilibrium.toTop_of_unique`.

## Homogeneous compatibility routes

* `standardCompliance_three_goals` — homogeneous single-carrier BCF
  theorem, available as the `carrier_T = carrier_S` specialization.
* `standardCompliance_three_goals_C1` — homogeneous C¹ analog.
* `standardCompliance_three_goals_local_regime_comparison` — pathwise corollary;
  requires the additional `hMyo_basin` invariance field (the myopic
  endogenous sanction path stays in the high political basin). Its
  general-`F` form (round BH1.4, 2026-10-06) is
  `StandardComplianceLocalCoreCertificate.pathwise_dominance_generalF`
  (`GeneralFDischargers.lean`): core certificate and myopic basin
  preservation only, uniform over basin starts, no affine law.

Every existing `ValueClass` is realized as a `ValueClass2` via the
homogeneous bridge `ValueClass.toValueClass2`; the homogeneous
theorems are the single-carrier specialization of the preferred
asymmetric route.

## Rule compliance

Rule 1 ✓ (no strategy changes — every produced equilibrium's
strategies are from existing argmax / Bellman machinery). Rule 3 —
pure aliasing / wrapping; no new load-bearing assumptions.
Category-(0/1) scaffolding. Rule 5 ✓ (fully parametric over `p` and
the certificate / C¹ certificate).

**Round BJ5.1 (2026-10-07).** Every MS-route headline here takes the MS
certificate and states Goal 2 against `p.myopicFeedbackEquilibrium_canonical`,
so each takes `[p.StaticSelectorContinuous]`. That class is the
static-selector continuity condition, the joint continuity of the static
Sender selector `σ`, which was the `Params` field `σ_continuous`. The content
is unchanged; the condition moved from the economy to the binder.
-/

import Sanctions.Theory.Certificates.RegularEconomy
import Sanctions.Theory.Equilibrium.ArgmaxUniquenessFromConcavity
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.Certificates.StandardComplianceLocal
import Sanctions.Theory.Certificates.StandardComplianceLocalC1

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Explicit paper-facing general-`F` persistence package -/

/-- **Paper-facing persistence package for an already constructed
equilibrium.**

This is the paper's two-sided mechanism interface for the general-`F`
persistence proof.  It keeps the two Sender requirements separate:

* `sender_IDO_after_target_policy` is the ordinal interval-dominance
  (single-crossing) condition in `(s,x)` after substituting the
  carrier-parameterised Target policy.  It controls how the greatest
  Sender argmax moves with the state.
* `sender_subpivot_chord` is the cardinal, transition-adjusted chord on
  the sanction range below the desired floor.  Together with the
  Sender carrier's Lipschitz bound, it controls the level of the
  greatest Sender argmax.  Since round BJ1.3 (2026-10-07,
  author-approved re-pin of contract row 272) it is stated
  on the basin `[max xT xS, 1]` only, in pivot-star form: at each basin
  state, the stage gain of moving from any sub-pivot sanction up to the
  pivot exceeds the worst continuation loss the Lipschitz bound allows.

The Target side is the existing carrier-uniform combined chord.  It
records the Target's aligned preference on the certified basin; the
three kinematic path conclusions use the Sender direction and level
fields plus the transition law.  The
two carrier memberships and `target_policy_eq` specialize all three
carrier statements to the constructed equilibrium.  Since `E` has
type `FeedbackStackelbergEquilibriumTop`, its feasibility and Bellman
optimality are not separate assumptions.

`sender_carrier_lipschitz` records the defining regularity of the
paper's Sender carrier; it is not inferred from stage concavity. -/
structure GeneralFPersistencePackage
    (D : p.ValueClass2)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (xT xS K_S : ℝ) : Prop where
  xT_mem : xT ∈ Sanctions.I
  xS_mem : xS ∈ Sanctions.I
  target_value_mem : E.V_T ∈ D.carrier_T
  sender_value_mem : E.V_S ∈ D.carrier_S
  target_policy_eq :
    E.α =
      D.α_on ⟨E.V_T, target_value_mem⟩
        ⟨E.V_S, sender_value_mem⟩
  sender_carrier_lipschitz :
    ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S K_S
  sender_IDO_after_target_policy :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x =>
          p.senderDynObjective V_S.val x
            (D.α_on V_T V_S x) s)
  /-- **P5, on the basin, pivot-star form** (round BJ1.3, 2026-10-07). At
  every basin state `x ∈ [max xT xS, 1]` and every sanction `s₁` below the
  pivot `max x (max xT xS)`, the Sender's stage gain from raising `s₁` to the
  pivot strictly exceeds the worst continuation loss `β_S · K_S · dist` its
  carrier's Lipschitz bound allows.

  Weakened from the pairwise chord over every sanction pair below the pivot
  at every state of the Sender's own range `[xS, 1]`. No *conclusion* needs
  the comparison of two sub-pivot sanctions with each other, or a state below
  the joint basin. The old proofs did read both (through strict monotonicity
  below the pivot on `[xS, 1]`), so `toJointPreferenceBasinTop` was re-proved
  with its statement unchanged, while two projections of the slim package
  changed their statements: `SenderPersistencePackage.toLocal` now returns the
  star chord, and `SenderPersistencePackage.static_response_ge_pivot` now holds
  on the basin. When `xT > xS` this no longer constrains `[xS, xT)`. General in
  `F`: the transition enters only through the successor-state distance. -/
  sender_subpivot_chord :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        ∀ s₁ ∈ Set.Ico (0 : ℝ) (max x (max xT xS)),
          p.β_S * K_S *
              dist (Sanctions.clipS' (p.F x s₁))
                   (Sanctions.clipS' (p.F x (max x (max xT xS))))
            < p.U_S x (D.α_on V_T V_S x) (max x (max xT xS)) -
                p.U_S x (D.α_on V_T V_S x) s₁
  target_combined_chord :
    p.TargetCombinedChordOn D xT (max xT xS)

/-- Convert the paper-facing general-`F` package into the joint
preference-basin object used by the path theorems.  The conversion makes
the role of every package field explicit: the sub-pivot chord supplies
the Sender level, interval dominance supplies realized-rule
monotonicity, and the Target combined chord supplies the Target's
sanction-preference field.

Round BJ1.3 (2026-10-07): with P5 in pivot-star form on the basin, the
Sender level comes from the pivot beating every sub-pivot sanction
(`sender_high_argmax_exists_of_pivot_beats_subpivot`) rather than from
strict monotonicity below the pivot, so the joint basin is assembled
field by field instead of through the one-sided threshold constructor
(whose Sender field still asks for strict monotonicity on `[xS, 1]`).
Statement unchanged. General in `F`. -/
theorem GeneralFPersistencePackage.toJointPreferenceBasinTop
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.GeneralFPersistencePackage D E xT xS K_S) :
    p.JointPreferenceBasinTop E.V_T E.V_S E.α
      (max xT xS) (max xT xS) := by
  let V_T_sub : D.CarrierT := ⟨E.V_T, P.target_value_mem⟩
  let V_S_sub : D.CarrierS := ⟨E.V_S, P.sender_value_mem⟩
  have hV_S_lip : ValueLipschitzWith E.V_S K_S :=
    P.sender_carrier_lipschitz E.V_S P.sender_value_mem
  have hpivot_mem : max xT xS ∈ Sanctions.I :=
    ⟨le_trans P.xT_mem.1 (le_max_left xT xS), max_le P.xT_mem.2 P.xS_mem.2⟩
  -- Level: P5 (pivot-star, on the basin) against P2.
  have hStar :
      ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ), ∀ s ∈ Set.Ico (0 : ℝ) (max x (max xT xS)),
        p.senderDynObjective E.V_S x (E.α x) s
          < p.senderDynObjective E.V_S x (E.α x) (max x (max xT xS)) := by
    intro x hx
    refine p.senderDynObjective_lt_pivot_of_star_chord_and_V_lipschitz
      (V_S := E.V_S) (α := E.α) (x := x) (sbar := max xT xS) (K := K_S) ?_ hV_S_lip
    intro s₁ hs₁
    have hchord := P.sender_subpivot_chord V_T_sub V_S_sub x hx s₁ hs₁
    simpa [P.target_policy_eq] using hchord
  have hTarget :=
    TargetCombinedChordOn.at_equilibrium p P.target_combined_chord E
      P.target_value_mem P.sender_value_mem P.target_policy_eq
  have hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective E.V_S x (E.α x) s) := by
    have h := P.sender_IDO_after_target_policy V_T_sub V_S_sub
    convert h using 2
    rw [P.target_policy_eq]
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO
  have hα_feas :
      ∀ x ∈ Set.Icc (max xT xS) 1, E.α x ∈ Sanctions.I := by
    intro x hx
    exact E.α_mem x
      ⟨le_trans (le_max_of_le_left P.xT_mem.1) hx.1, hx.2⟩
  have hα_opt :
      ∀ x ∈ Set.Icc (max xT xS) 1,
        IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S x a)
          Sanctions.I (E.α x) := by
    intro x hx
    exact E.α_opt_top x
      ⟨le_trans (le_max_of_le_left P.xT_mem.1) hx.1, hx.2⟩
  exact
    { xbar_nonneg := hpivot_mem.1
      xbar_le_one := hpivot_mem.2
      sbar_mem := hpivot_mem
      target_policy_feasible := hα_feas
      sender_high_argmax_exists :=
        p.sender_high_argmax_exists_of_pivot_beats_subpivot hpivot_mem.1 hpivot_mem hStar
      top_rule_mono := hTopMono
      target_prefers_sanctions := fun x hx => by
        unfold targetSanctionObjective
        exact hTarget x ⟨le_trans (le_max_left xT xS) hx.1, hx.2⟩
      target_policy_optimal := hα_opt }

/-- **Paper-facing general-`F` persistence theorem.**

For every initial state in the high basin, the equilibrium path stays
in that basin, the realized sanction never falls below the basin
pivot, and realized sanctions are non-decreasing.  The proof consumes
only the fields displayed in `GeneralFPersistencePackage`; in
particular it does not use an affine transition, Sender-value
monotonicity, or stage concavity. -/
theorem standardCompliance_persistence_generalF_from_package
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.GeneralFPersistencePackage D E xT xS K_S) :
    ∀ x₀ ∈ Set.Icc (max xT xS) 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, max xT xS ≤
                p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  intro x₀ hx₀
  have h :=
    p.jointPreferenceBasinTopF_long_run_nonDecreasing
      P.toJointPreferenceBasinTop hx₀
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- **Paper-facing general-`F` persistence with both-player on-path equilibrium
evidence.**

This strengthens `standardCompliance_persistence_generalF_from_package`
without adding assumptions.  In addition to basin invariance, the
sanction floor, and sanction monotonicity, it records at every path
state that both policies are optimal and that the Target's complete
forward-looking sanction objective is non-decreasing above the
realized-state floor.  Consequently the package's Target combined chord
has an explicit conclusion rather than serving only as certificate
bookkeeping. -/
theorem standardCompliance_persistence_generalF_with_equilibrium_evidence_from_package
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.GeneralFPersistencePackage D E xT xS K_S) :
    ∀ x₀ ∈ Set.Icc (max xT xS) 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, max xT xS ≤
                p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) ∧
      (∀ n, E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n)
                ∈ Sanctions.I) ∧
      (∀ n, IsMaxOn
        (fun a => p.joint_T_top_integrand E.V_T E.V_S
          (p.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
        Sanctions.I
        (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n))) ∧
      (∀ n, IsMaxOn
        (fun s' => p.senderDynObjective E.V_S
          (p.dynamicTopLockInPathF E.V_S E.α x₀ n)
          (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n)) s')
        Sanctions.I
        (p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective E.V_T
          (p.dynamicTopLockInPathF E.V_S E.α x₀ n)
          (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n)) s)
        (Set.Icc
          (max (p.dynamicTopLockInPathF E.V_S E.α x₀ n) (max xT xS))
          1)) := by
  intro x₀ hx₀
  obtain ⟨hpath, -, hfloor, hmono, hfeas, htarget, hsender, hpref⟩ :=
    p.jointPreferenceBasinTopF_long_run_with_equilibrium_evidence
      P.toJointPreferenceBasinTop hx₀
  exact ⟨hpath, hfloor, hmono, hfeas, htarget, hsender, hpref⟩

/-- **Paper-facing quantitative general-`F` shock theorem.**

This wrapper takes the complete persistence package and adds exactly
the transition hypotheses needed for a uniform finite-duration shock:
F1--F4 are fields of `p`, F5 is `hAdj : p.StrictAdjustment`, and the
basin pivot lies below one.  The full-sanction drift therefore attains
a positive minimum `η` below the pivot.  At the canonical ceiling
horizon, every feasible shock start has entered the basin; from that
date onward the complete persistence conclusion applies. -/
theorem standardCompliance_min_drift_shock_generalF_from_package
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.GeneralFPersistencePackage D E xT xS K_S)
    (hAdj : p.StrictAdjustment)
    (hpivot_lt : max xT xS < 1) :
    ∃ η : ℝ, 0 < η
      ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (max xT xS),
          η = p.fullShockDrift xmin)
      ∧ (∀ x ∈ Set.Icc (0 : ℝ) (max xT xS),
          η ≤ p.fullShockDrift x)
      ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
        p.shockPathF x₀shock (Nat.ceil (max xT xS / η))
            ∈ Set.Icc (max xT xS) 1
        ∧ (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀shock
                    (Nat.ceil (max xT xS / η))) n
                  ∈ Set.Icc (max xT xS) 1)
        ∧ (∀ n, max xT xS ≤
                  p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock
                      (Nat.ceil (max xT xS / η))) n)
        ∧ Monotone
            (p.dynamicTopLockInSanctionsF E.V_S E.α
              (p.shockPathF x₀shock
                (Nat.ceil (max xT xS / η)))) := by
  have hpivot_nonneg : (0 : ℝ) ≤ max xT xS :=
    le_trans P.xT_mem.1 (le_max_left xT xS)
  have hpivot : max xT xS ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨hpivot_nonneg, hpivot_lt⟩
  obtain ⟨η, hη_pos, hη_attains, hη_floor, hentry⟩ :=
    p.shockPathF_exists_min_drift_uniform_natCeil_bound_of_strictAdjustment
      hAdj hpivot
  refine ⟨η, hη_pos, hη_attains, hη_floor, ?_⟩
  intro x₀shock hx₀shock
  let N := Nat.ceil (max xT xS / η)
  have hNentry := hentry x₀shock hx₀shock N (le_refl N)
  have hpersist :=
    p.standardCompliance_persistence_generalF_from_package
      P _ hNentry
  exact ⟨hNentry, hpersist.1, hpersist.2.1, hpersist.2.2⟩

/-- **General-`F` minimum-drift shock with both-player post-entry evidence.**

This is the evidence-preserving counterpart of
`standardCompliance_min_drift_shock_generalF_from_package`.  The same
minimum-drift argument constructs a uniform finite shock horizon.  At every
subsequent endogenous date it records basin invariance, the sanction floor,
sanction monotonicity, Target feasibility and Bellman optimality, Sender
Bellman optimality, and the Target's monotone sanction preference on the
realized upper interval.

No additional assumption is introduced.  This theorem displays both players'
on-path equilibrium conditions, but it does not by itself construct the
two-value coupled equilibrium consumed through `P`. -/
theorem standardCompliance_min_drift_shock_generalF_with_equilibrium_evidence_from_package
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.GeneralFPersistencePackage D E xT xS K_S)
    (hAdj : p.StrictAdjustment)
    (hpivot_lt : max xT xS < 1) :
    ∃ η : ℝ, 0 < η
      ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (max xT xS),
          η = p.fullShockDrift xmin)
      ∧ (∀ x ∈ Set.Icc (0 : ℝ) (max xT xS),
          η ≤ p.fullShockDrift x)
      ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
        p.shockPathF x₀shock (Nat.ceil (max xT xS / η))
            ∈ Set.Icc (max xT xS) 1
        ∧ ((∀ n, p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀shock
                    (Nat.ceil (max xT xS / η))) n
                  ∈ Set.Icc (max xT xS) 1)
          ∧ (∀ n, max xT xS ≤
                  p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock
                      (Nat.ceil (max xT xS / η))) n)
          ∧ Monotone
              (p.dynamicTopLockInSanctionsF E.V_S E.α
                (p.shockPathF x₀shock
                  (Nat.ceil (max xT xS / η))))
          ∧ (∀ n, E.α
                  (p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock
                      (Nat.ceil (max xT xS / η))) n)
                  ∈ Sanctions.I)
          ∧ (∀ n, IsMaxOn
              (fun a => p.joint_T_top_integrand E.V_T E.V_S
                (p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀shock
                    (Nat.ceil (max xT xS / η))) n) a)
              Sanctions.I
              (E.α
                (p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀shock
                    (Nat.ceil (max xT xS / η))) n)))
          ∧ (∀ n, IsMaxOn
              (fun s' => p.senderDynObjective E.V_S
                (p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀shock
                    (Nat.ceil (max xT xS / η))) n)
                (E.α
                  (p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock
                      (Nat.ceil (max xT xS / η))) n)) s')
              Sanctions.I
              (p.dynamicTopLockInSanctionsF E.V_S E.α
                (p.shockPathF x₀shock
                  (Nat.ceil (max xT xS / η))) n))
          ∧ (∀ n, MonotoneOn
              (fun s => p.targetSanctionObjective E.V_T
                (p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀shock
                    (Nat.ceil (max xT xS / η))) n)
                (E.α
                  (p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock
                      (Nat.ceil (max xT xS / η))) n)) s)
              (Set.Icc
                (max
                  (p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock
                      (Nat.ceil (max xT xS / η))) n)
                  (max xT xS))
                1))) := by
  have hpivot_nonneg : (0 : ℝ) ≤ max xT xS :=
    le_trans P.xT_mem.1 (le_max_left xT xS)
  have hpivot : max xT xS ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨hpivot_nonneg, hpivot_lt⟩
  obtain ⟨η, hη_pos, hη_attains, hη_floor, hentry⟩ :=
    p.shockPathF_exists_min_drift_uniform_natCeil_bound_of_strictAdjustment
      hAdj hpivot
  refine ⟨η, hη_pos, hη_attains, hη_floor, ?_⟩
  intro x₀shock hx₀shock
  let N := Nat.ceil (max xT xS / η)
  have hNentry := hentry x₀shock hx₀shock N (le_refl N)
  have hpersist :=
    p.standardCompliance_persistence_generalF_with_equilibrium_evidence_from_package
      P _ hNentry
  exact ⟨hNentry, hpersist⟩

/-! ## Preferred asymmetric carrier-local BCF theorem

The audit-49-follow-up preferred paper-facing route. Uses
`ValueClass2` with separate Target carrier `carrier_T` and Sender
carrier `carrier_S`, and carrier-local stage primitives quantified
over `∀ V_T : D.CarrierT, ∀ V_S : D.CarrierS, …`. The
single-carrier (homogeneous) `ValueClass` route is retained as
compatibility further down via the bridge
`ValueClass.toValueClass2`. -/


/-- **Paper-facing affine-trajectory headline (combined-chord / MS route).**

⚠ **Scope corrected 2026-08-18.** This docstring previously read "the three
persistence goals for an **arbitrary monotone transition `F`**" and called this
theorem "the canonical general-`F` form". That was wrong, and wrong in the exact
way CLAUDE.md Rule 22 exists to prevent: it inferred generality from the *absence
of an `hF` binder* (axis 1) while the **conclusion** is stated over
`p.dynamicTopLockInPath`, `p.dynamicTopLockInSanctions` and `p.shockPath` — the
hand-written `(1 − δ)·x + δ·rule` iterates, which are axis-2 affine with no
signature footprint at all. The paper never made this error: the formalization map
already lists this theorem among "the affine-transition headline siblings".

What is true. The *assumption surface* is general — there is no `hF`, A2 is taken
in its ordinal combined-chord form and A1 as Milgrom–Shannon single crossing, and
the basin invariance is carried by `F_diag` and `F_mono`. What is affine is the
*state evolution the conclusion quantifies over*. So this is the affine-trajectory
member of the pair, and it keeps the closed-form shock-entry horizon in exchange.

The canonical general-`F` form is `standardCompliance_three_goals_local_MS_generalF`
below, whose conclusion is stated over `dynamicTopLockInPathF` /
`dynamicTopLockInSanctionsF`; the price of that generality is the loss of the
closed-form horizon (Goal 3 asserts only `∃ N`). The affine loss-offset headlines
above remain a cardinal sufficient-condition fallback.

One-line delegation to the `hF`-free
`StandardComplianceLocalCoreCertificate_MS.three_goals_local_MS`. -/
theorem standardCompliance_three_goals_local_MS [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPath E.V_S E.α
                    (p.shockPath x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                    (p.shockPath x₀shock N) n)) :=
  StandardComplianceLocalCoreCertificate_MS.three_goals_local_MS p C

/-- **Paper-facing general-`F` trajectory headline (Option B, R-2026-06-22).**

The three persistence goals with the realized political-state
**trajectory** evolved by an arbitrary monotone transition `F`
(Goals 1 and 3 use `dynamicTopLockInPathF` / `shockPathF`), not only the
affine law. Strengthens `standardCompliance_three_goals_local_MS`
(whose trajectory is affine) by the single extra hypothesis `hF_top`
(`∀ x ∈ [0,1), x < F x 1`, strict-above-diagonal at full sanctions),
consumed only by the Goal-3 shock finite-entry step. The affine headline
is the `F := affineF δ` specialisation (`affineF_hF_top` discharges
`hF_top` from `0 < δ(1−x)`). This is the canonical general-`F` form
substantiating §4's "the proofs use only (F2)–(F4), never the affine
form" at the state-evolution level; the price of generality is the loss
of the closed-form shock horizon `N_*` (Goal 3 asserts only `∃ N`).

One-line delegation to
`StandardComplianceLocalCoreCertificate_MS.three_goals_local_MS_generalF`. -/
theorem standardCompliance_three_goals_local_MS_generalF [p.StaticSelectorContinuous]
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
  StandardComplianceLocalCoreCertificate_MS.three_goals_local_MS_generalF p C hF_top

/-- **General-`F` three-goal theorem with a uniform shock duration.**

The equilibrium and basin conclusions are those of
`standardCompliance_three_goals_local_MS_generalF`, while the exogenous
shock conclusion is strengthened to one worst-case duration `N` that
works from every initial state in `[0, 1]`. State monotonicity makes the
path from `0` worst-case, and the certificate's interior-pivot field
places the basin threshold strictly below `1`. -/
theorem standardCompliance_three_goals_local_MS_generalF_uniform_shock [p.StaticSelectorContinuous]
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
      ∧ ∃ N : ℕ, ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                  (p.shockPathF x₀shock N) n) := by
  obtain ⟨E, hVT, hVS, hpaths, hdom, _⟩ :=
    p.standardCompliance_three_goals_local_MS_generalF C hF_top
  obtain ⟨N, hN⟩ :=
    p.shockPathF_uniform_eventually_in_basin hF_top C.hpivot_mem.2
  refine ⟨E, hVT, hVS, hpaths, hdom, N, ?_⟩
  intro x₀shock hx₀shock
  obtain ⟨hinv, hfloor, _⟩ := hpaths _ (hN x₀shock hx₀shock N (le_refl N))
  exact ⟨hinv, hfloor⟩

/-- **General-`F` three-goal theorem with an explicit minimum-drift
shock bound.** Under the paper's maintained strict-adjustment condition,
the full-sanction drift attains a positive minimum `η` below the
certificate basin. Hence

`N = ⌈max C.xT C.xS / η⌉₊`

is one shock duration that works uniformly from every feasible initial
state. The theorem records the minimizer and the global drift-floor
property, so the quantitative constant is fully derived from `F`. -/
theorem standardCompliance_three_goals_local_MS_generalF_min_drift_shock
    [p.StaticSelectorContinuous]
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
                    (p.shockPathF x₀shock (Nat.ceil (max C.xT C.xS / η))) n) := by
  obtain ⟨E, hVT, hVS, hpaths, hdom, _⟩ :=
    p.standardCompliance_three_goals_local_MS_generalF C hAdj.hF_top
  have hxbar : max C.xT C.xS ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨le_of_lt C.hpivot_mem.1, C.hpivot_mem.2⟩
  obtain ⟨η, hη_pos, hη_attains, hη, hentry⟩ :=
    p.shockPathF_exists_min_drift_uniform_natCeil_bound_of_strictAdjustment
      hAdj hxbar
  refine ⟨E, hVT, hVS, hpaths, hdom, η, hη_pos, hη_attains, hη, ?_⟩
  intro x₀shock hx₀shock
  let N := Nat.ceil (max C.xT C.xS / η)
  have hNentry := hentry x₀shock hx₀shock N (le_refl N)
  obtain ⟨hinv, hfloor, _⟩ := hpaths _ hNentry
  exact ⟨hNentry, hinv, hfloor⟩

/-- **General-`F` three-goal theorem at the canonical minimum-drift
horizon.** This named-object version evaluates the shock conclusion at

`fullShockEntryHorizon p (max C.xT C.xS)
  = ⌈max C.xT C.xS / fullShockMinDrift p (max C.xT C.xS)⌉`.

Thus the manuscript can state the quantitative shock result without an
existentially chosen drift constant. -/
theorem standardCompliance_three_goals_local_MS_generalF_canonical_shock
    [p.StaticSelectorContinuous]
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
      ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
          p.shockPathF x₀shock
              (p.fullShockEntryHorizon (max C.xT C.xS))
              ∈ Set.Icc (max C.xT C.xS) 1
          ∧ (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock
                      (p.fullShockEntryHorizon (max C.xT C.xS))) n
                    ∈ Set.Icc (max C.xT C.xS) 1)
          ∧ (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀shock
                      (p.fullShockEntryHorizon (max C.xT C.xS))) n) := by
  obtain ⟨E, hVT, hVS, hpaths, hdom, _⟩ :=
    p.standardCompliance_three_goals_local_MS_generalF C hAdj.hF_top
  have hxbar : max C.xT C.xS ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨le_of_lt C.hpivot_mem.1, C.hpivot_mem.2⟩
  have hentry :=
    p.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment hAdj hxbar
  refine ⟨E, hVT, hVS, hpaths, hdom, ?_⟩
  intro x₀shock hx₀shock
  have hNentry := hentry x₀shock hx₀shock
    (p.fullShockEntryHorizon (max C.xT C.xS)) le_rfl
  obtain ⟨hinv, hfloor, _⟩ := hpaths _ hNentry
  exact ⟨hNentry, hinv, hfloor⟩


/-- **General-`F` trajectory headline with path optimality (R-2026-07-08).**

General-`F` sibling of
`standardCompliance_three_goals_local_with_path_optimality`: the
5-conjunct persistence form with the per-path `IsMaxOn`
Bellman-optimality conjunct restored, stated **along the general-`F`
realized path** `dynamicTopLockInPathF` — and, being built on the MS
combined-chord route, with the affine hypothesis `hF` deleted (the
only extra hypothesis is the general-`F` base-package shock input
`hF_top`, consumed by Goal 3). The restored conjunct is *not* a
substantive theorem conclusion — it is a definitional consequence of
the feedback Stackelberg equilibrium concept (E3), hence
transition-agnostic: every general-`F` path state stays in the basin
`⊆ Sanctions.S`, where `E.α_opt_top` applies verbatim. Goal-1
invariance comes from the general-`F` base package
(`standardCompliance_three_goals_local_MS_generalF`). -/
theorem standardCompliance_three_goals_local_with_path_optimality_generalF
    [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n))))
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
  obtain ⟨E, hVT, hVS, hG1, hG2, hG3⟩ :=
    p.standardCompliance_three_goals_local_MS_generalF C hF_top
  refine ⟨E, hVT, hVS, ?_, hG2, hG3⟩
  intro x₀ hx₀
  obtain ⟨h_basin, h_floor, h_mono⟩ := hG1 x₀ hx₀
  refine ⟨h_basin, h_floor, h_mono, ?_⟩
  -- Path optimality: every general-`F` path state lies in the basin
  -- ⊆ Sanctions.S, so the equilibrium Bellman optimality applies.
  intro n
  exact E.α_opt_top _
    ⟨le_trans (le_max_of_le_left C.hxT_mem.1) (h_basin n).1, (h_basin n).2⟩


/-- **General-`F` regime-comparison headline (R-2026-07-08).**

General-`F` sibling of
`standardCompliance_three_goals_local_regime_comparison_uniform_starts`,
with the affine hypothesis `hF` deleted: **both** compared regimes'
realized trajectories are evolved by the abstract monotone transition
`p.F` — the dynamic lock-in path by `dynamicTopLockInPathF` (Goals 1
and 3) and the two compared sanction sequences of Goal 2′ by the
general-`F` rule path `ruleSanctionsF` (one step is `x ↦ F(x, R x)`).
Built on the MS combined-chord route
(`StandardComplianceLocalCoreCertificate_MS`), which is the canonical
general-`F` base; the affine regime-comparison headline is the
`F := affineF δ` specialisation of the same comparison content.
Universal-start form (the MS base is start-free; a fixed start is the
instantiation at that `x₀`).

Hypotheses beyond the certificate are exactly the general-`F`
restatements of what the affine version carries: `hF_top` (the
existing general-`F` base-package shock input, Goal 3 only) and the
same myopic basin-preservation hypothesis `hMyoBasin` as the affine
form — the canonical myopic equilibrium's realized rule maps the
basin into itself; under the general-`F` step this yields path
confinement via `F_diag`/`F_mono_x`/`F_mono_s`. As in the affine
case, when `hMyoBasin` is not economically warranted, fall back to
the statewise `standardCompliance_three_goals_local_MS_generalF`.

One-line delegation to
`StandardComplianceLocalCoreCertificate_MS.three_goals_local_MS_regime_comparison_generalF`. -/
theorem standardCompliance_three_goals_local_MS_regime_comparison_generalF
    [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    (hMyoBasin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.myopicEquilibriumRule (p.myopicFeedbackEquilibrium_canonical) x
          ∈ Set.Icc (max C.xT C.xS) 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.myopicEquilibriumRule (p.myopicFeedbackEquilibrium_canonical) x
             ≤ p.dynamicEquilibriumRule E x)
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
           ∀ n, p.ruleSanctionsF
                  (p.myopicEquilibriumRule (p.myopicFeedbackEquilibrium_canonical))
                  x₀ n
                  ≤ p.ruleSanctionsF (p.dynamicEquilibriumRule E) x₀ n)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                    (p.shockPathF x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                                    (p.shockPathF x₀shock N) n)) :=
  StandardComplianceLocalCoreCertificate_MS.three_goals_local_MS_regime_comparison_generalF
    p C hF_top hMyoBasin


/-- **Audit-49 Phase A-F follow-up Fix-1: ordinary-equilibrium
existence wrapper.**

*Existence-only* wrapper (renamed in 2026-05-29 to make scope
explicit). Produces an *ordinary* `FeedbackStackelbergEquilibrium`
(Sender response via the classical-choice `σ_dyn`, not the upper
selector `σ_dyn_top`) with carrier membership AND a certificate of
Sender dynamic argmax uniqueness. **Does not return the three
goals** — downstream callers wanting the three goals at the
ordinary equilibrium should compose this wrapper with
`standardCompliance_three_goals_local` and convert any top-selector
conclusion to its ordinary-selector form via
`σ_dyn_eq_σ_dyn_top_of_unique` (in `SigmaDynComparison.lean`) and
`FeedbackStackelbergEquilibrium.toTop_of_unique` (in
`SelectionRobust.lean`). Those bridges need full `DynamicArgmaxUnique`, which
`standardCompliance_local_equilibriumTop_of_senderUnique` returns given full
uniqueness on the Sender carrier; the compliance-local certificate returned here
(since round BJ4.3) gives the `σ_dyn = σ_dyn_top` identity at physical compliance
levels, which covers the realized path.

Intended for JET-paper-facing presentation where the ordinary
equilibrium object is the natural reader expectation; the preferred
theorem `standardCompliance_three_goals_local_uniform_starts` remains
the canonical upper-selector form.

Consumes the **start-free core certificate**
`StandardComplianceLocalCoreCertificate` (this wrapper uses only
start-independent fields, so the fixed-start extension is not
required).

Round BJ4.3 (2026-10-08): the certificate's value class now carries
Sender uniqueness only at physical compliance levels
(`ValueClass2.sender_unique_on : … DynamicArgmaxUniqueOnI`), so the
returned uniqueness certificate is `DynamicArgmaxUniqueOnI E.V_S`
(formerly `DynamicArgmaxUnique E.V_S`, every real compliance level). That
is the form the selector bridges need along any equilibrium path, whose
compliance levels lie in `[0,1]`. With full uniqueness on the Sender
carrier as an extra input, the former conclusion is
`standardCompliance_local_equilibriumTop_of_senderUnique`. General in `F`. -/
theorem standardCompliance_local_equilibriumTop
    (C : p.StandardComplianceLocalCoreCertificate) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ p.DynamicArgmaxUniqueOnI E.V_S := by
  obtain ⟨E, hVT, hVS, _hα⟩ :=
    C.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership
      C.h_inv C.hβ_T_nn C.hβ_S_nn C.hL_TS_nn C.hL_ST_nn
      C.hT_T_op C.hT_S_op C.hsuff_T C.hsuff_S
  exact ⟨E, hVT, hVS, C.D.sender_unique_on E.V_S hVS⟩

/-- **Ordinary-equilibrium existence wrapper with full Sender uniqueness
(round BJ4.3, 2026-10-08).** The pre-BJ4.3 conclusion of
`standardCompliance_local_equilibriumTop`, Sender uniqueness at every real
compliance level, for a certificate whose Sender carrier also satisfies
`DynamicArgmaxUnique` (`hU`). Before round BJ4.3 the value class carried `hU`
itself; it now carries only the compliance-local part, so `hU` is an explicit
input here and nothing is lost. General in `F`. -/
theorem standardCompliance_local_equilibriumTop_of_senderUnique
    (C : p.StandardComplianceLocalCoreCertificate)
    (hU : ∀ V_S ∈ C.D.carrier_S, p.DynamicArgmaxUnique V_S) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ p.DynamicArgmaxUnique E.V_S := by
  obtain ⟨E, hVT, hVS, _⟩ := p.standardCompliance_local_equilibriumTop C
  exact ⟨E, hVT, hVS, hU E.V_S hVS⟩

/-! ## Audit-49 follow-up Round 3 Optional-4.3: three-goals wrapper with selector-equivalence bridge

⚠ **Audit-49 follow-up Round 4 rename note.** This theorem was
previously named `standardCompliance_three_goals_local_ordinary`,
which over-claimed: it returns the *top-selector* equilibrium
`E : FeedbackStackelbergEquilibriumTop` together with a pointwise
`σ_dyn = σ_dyn_top` bridge (NOT an ordinary
`FeedbackStackelbergEquilibrium` object directly). The current name
`standardCompliance_three_goals_local_with_selector_equivalence`
makes the scope explicit: top equilibrium + uniqueness + pointwise
selector equivalence + three goals at the top equilibrium. A genuine
ordinary-rule version of the three goals (using `dynamicLockInPath`
rather than `dynamicTopLockInPath`) would require new induction
lemmas not yet in the codebase.

The pointwise `σ_dyn = σ_dyn_top` bridge lets a downstream caller
convert any of the three-goal conclusions to the ordinary-rule form
by pointwise rewriting on the realized-sanction path. -/


/-- **General-`F` three-goals wrapper with selector-equivalence bridge
(R-2026-07-08).**

General-`F` sibling of
`standardCompliance_three_goals_local_with_selector_equivalence`, with
the affine hypothesis `hF` deleted: returns the top equilibrium `E`
with carrier membership, the Sender dynamic-argmax uniqueness
certificate `p.DynamicArgmaxUniqueOnI E.V_S` (from the certificate's
carrier-local `sender_unique_on` field), the pointwise
`σ_dyn = σ_dyn_top` selector bridge on `Sanctions.S × Sanctions.I`, and the
general-`F` trajectory three goals of
`standardCompliance_three_goals_local_MS_generalF` (Goals 1 and 3 on
`dynamicTopLockInPathF` / `shockPathF`). The selector bridge is
transition-agnostic — uniqueness of the Sender dynamic argmax is a
statement about the objective `U_S + β_S·V_S(F(x,·))` at the fixed
equilibrium `V_S`, independent of which trajectory the state follows —
so downstream callers can convert any of the three-goal conclusions to
the ordinary-selector form by pointwise rewriting, exactly as in the
affine case.

Round BJ4.3 (2026-10-08): the certificate's value class now carries Sender
uniqueness only at physical compliance levels, so the uniqueness certificate
is `DynamicArgmaxUniqueOnI E.V_S` and the selector bridge holds for `a ∈ I`
(formerly `DynamicArgmaxUnique E.V_S` and every real `a`). The realized path
evaluates the Sender's response only at the equilibrium compliance `E.α x`,
which lies in `I` on the state space, so the pointwise rewriting above is
unaffected. With full uniqueness on the Sender carrier as an extra input, the
former conclusion is
`standardCompliance_three_goals_local_with_selector_equivalence_generalF_of_senderUnique`. -/
theorem standardCompliance_three_goals_local_with_selector_equivalence_generalF
    [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ p.DynamicArgmaxUniqueOnI E.V_S
      ∧ (∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
          p.σ_dyn E.V_S x a = p.σ_dyn_top E.V_S x a)
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
  obtain ⟨E, hVT, hVS, hG1, hG2, hG3⟩ :=
    p.standardCompliance_three_goals_local_MS_generalF C hF_top
  -- Uniqueness at E.V_S from the certificate's carrier-local
  -- `sender_unique_on` field (compliance-local since round BJ4.3).
  have hUnique : p.DynamicArgmaxUniqueOnI E.V_S :=
    C.D.sender_unique_on E.V_S hVS
  -- σ_dyn = σ_dyn_top pointwise from uniqueness, at physical compliance.
  have hσ_eq : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
      p.σ_dyn E.V_S x a = p.σ_dyn_top E.V_S x a := by
    intro x hx a ha
    exact p.σ_dyn_eq_σ_dyn_top_of_unique E.V_S x a
      (fun s₁ s₂ hs₁_mem hs₂_mem hs₁_max hs₂_max =>
        hUnique x hx a ha s₁ s₂ hs₁_mem hs₂_mem hs₁_max hs₂_max)
  exact ⟨E, hVT, hVS, hUnique, hσ_eq, hG1, hG2, hG3⟩

/-- **General-`F` three-goals wrapper with selector-equivalence bridge and
full Sender uniqueness (round BJ4.3, 2026-10-08).** The pre-BJ4.3 conclusion
of `standardCompliance_three_goals_local_with_selector_equivalence_generalF`
(Sender uniqueness and the `σ_dyn = σ_dyn_top` bridge at every real compliance
level), for a certificate whose Sender carrier also satisfies
`DynamicArgmaxUnique` (`hU`). Before round BJ4.3 the value class carried `hU`
itself; it now carries only the compliance-local part, so `hU` is an explicit
input here and nothing is lost. General in `F`. -/
theorem standardCompliance_three_goals_local_with_selector_equivalence_generalF_of_senderUnique
    [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    (hU : ∀ V_S ∈ C.D.carrier_S, p.DynamicArgmaxUnique V_S) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ p.DynamicArgmaxUnique E.V_S
      ∧ (∀ x ∈ Sanctions.S, ∀ a, p.σ_dyn E.V_S x a = p.σ_dyn_top E.V_S x a)
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
  obtain ⟨E, hVT, hVS, _, _, hG1, hG2, hG3⟩ :=
    p.standardCompliance_three_goals_local_with_selector_equivalence_generalF C hF_top
  have hUnique : p.DynamicArgmaxUnique E.V_S := hU E.V_S hVS
  have hσ_eq : ∀ x ∈ Sanctions.S, ∀ a,
      p.σ_dyn E.V_S x a = p.σ_dyn_top E.V_S x a := fun x hx a =>
    p.σ_dyn_eq_σ_dyn_top_of_unique E.V_S x a (hUnique x hx a)
  exact ⟨E, hVT, hVS, hUnique, hσ_eq, hG1, hG2, hG3⟩

/-! ## Audit-49 follow-up Round 3 Optional-4.4: local weak-persistence wrapper

The preferred theorem `standardCompliance_three_goals_local` is a
*strong-ratchet* theorem: its Goal-1 conclusion includes both basin
invariance and a strong floor `sbar ≤ realized`, implying a
monotone non-decreasing sanction sequence and forcing the realized
sanction at `x = 1` to equal `1`. For applications where this
strong-corner conclusion is too narrow (e.g. long-run basin
membership without literal monotone sanctions), the weak-persistence
variant below delivers only basin invariance + statewise dominance +
post-shock basin invariance. -/


/-- **General-`F` weak-persistence theorem (R-2026-07-08).**

General-`F` sibling of
`standardCompliance_three_goals_local_weak_persistence`, with the
affine hypothesis `hF` deleted: drops the strong-ratchet sanction
floors and `Monotone` conjunct, keeping only basin invariance of the
**general-`F`** realized path (`dynamicTopLockInPathF`), the
statewise Goal-2 dominance, and post-shock general-`F` basin
invariance (`shockPathF`). Universal-start form (the MS base is
start-free; a fixed start is the instantiation at that `x₀`).
Projection of `standardCompliance_three_goals_local_MS_generalF`
onto the weaker conjunct subset, mirroring how the affine
weak-persistence form projects `three_goals_local`. -/
theorem standardCompliance_three_goals_local_weak_persistence_generalF [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificate_MS)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          ∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                ∈ Set.Icc (max C.xT C.xS) 1)
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x ((p.myopicFeedbackEquilibrium_canonical).α x)
              ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            ∀ n, p.dynamicTopLockInPathF E.V_S E.α (p.shockPathF x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) := by
  obtain ⟨E, hVT, hVS, hG1, hG2, hG3⟩ :=
    p.standardCompliance_three_goals_local_MS_generalF C hF_top
  refine ⟨E, hVT, hVS, fun x₀ hx₀ => (hG1 x₀ hx₀).1, hG2, ?_⟩
  intro x₀shock h_nn h_le
  obtain ⟨N, h1, _h2⟩ := hG3 x₀shock h_nn h_le
  exact ⟨N, h1⟩

/-! ## Homogeneous compatibility routes

The theorems below are the **homogeneous single-carrier
compatibility** specializations of the preferred carrier-local
theorems above. They remain correct and non-deprecated, but they
are the special case where `carrier_T = carrier_S` (via the bridge
`ValueClass.toValueClass2`). New paper-facing citations should
prefer the carrier-local forms above; these are retained for
back-compatibility with audit-46/47 documentation that targeted
`StandardComplianceCertificate` / `StandardComplianceCertificateC1`.

* `standardCompliance_three_goals` — homogeneous BCF route
  (audit-47 alias for `RegularEconomyCertificateComplianceCore.three_goals_statewise`).
* `standardCompliance_three_goals_C1` — homogeneous C¹ analog.
* `standardCompliance_three_goals_local_regime_comparison` — pathwise corollary
  requiring the additional `hMyo_basin` invariance (the myopic
  endogenous path stays in the high basin). Demoted under audit-46
  to a corollary because under literal compliance the myopic Target
  may comply more and push the path out of the basin. The general-`F`
  comparison is `StandardComplianceLocalCoreCertificate.pathwise_dominance_generalF`
  (round BH1.4).

Under the **literal-compliance** interpretation of `a` (`a = 1` is
full compliance, `a = 0` no compliance), these are correct
paper-facing theorems (homogeneous form). The older regular-economy
route was sign-correct only under the *resistance-action*
interpretation of `a`; it was quarantined for that reason and then
deleted outright on 2026-08-17, nothing having consumed it. -/


end Params
end AbstractGame

end -- noncomputable section

end Sanctions
