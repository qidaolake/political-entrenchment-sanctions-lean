/-
Sanctions/Theory/Certificates/StandardComplianceLocalised.lean

**The three-goals certificate theorems with full-sanction ascent needed only
below the basin pivot, and their Schur-margin forms** (round BB, 2026-09-28;
doc 110 items R7(a) and R8, "row 2 Schur").

## What the pinned theorems assume, and what their proofs read

Headline row 2, `standardCompliance_three_goals_local_MS_generalF_min_drift_shock`
(`StandardComplianceMain.lean`), and the paper's `thm:shock` anchor,
`standardCompliance_min_drift_shock_generalF_from_package`, take the two-sided
strict-adjustment condition F5 (`StrictAdjustment`: on the whole feasible
square the state moves strictly toward the current sanction), and the package
form also takes `max xT xS < 1`. Headline row 1,
`standardCompliance_three_goals_local_MS_generalF`, takes the global
full-sanction ascent `hF_top : ∀ x ∈ [0, 1), x < F(x, 1)`. In every case the
proof reads the transition condition only to get finite entry of the
exogenous full-sanction path into the basin `[x̄, 1]`, `x̄ = max xT xS`; and
that entry needs it only on the pre-basin interval `[0, x̄]`
(`LocalisedShockEntry.lean`). (Row 1's current Goal-3 proof goes through the
convergence of the shock path and reads `hF_top` above `x̄`; its sibling here
goes through the minimum-drift bound instead.) Goals 1 and 2 — persistence inside the basin
and dynamic-over-myopic dominance — read no transition condition beyond the
`Params` fields at all (`three_goals_local_MS_generalF` uses `hF_top` only at
its Goal-3 step).

## What this file proves

* `StandardComplianceLocalCoreCertificateSchur_MS.two_goals_local_MS_generalF`
  and its row-sum counterpart `StandardComplianceLocalCoreCertificate_MS.two_goals_local_MS_generalF`
  — the Goals-1–2 core: from the certificate alone (no transition hypothesis),
  a top-selector feedback Stackelberg equilibrium exists in the certificate's
  carriers, its path persists in the basin with a sanction floor and
  non-decreasing sanctions, and its sanction rule dominates the canonical
  myopic rule on the basin. The Schur proof re-uses exactly the lemmas
  `three_goals_local_MS_generalF` (Schur form, `StandardComplianceSchur.lean`)
  calls; the row-sum core is the Schur core at `ofRowSum_MS C`.
* Localised siblings — hypothesis `hF_top_pre : ∀ x ∈ [0, x̄], x < F(x, 1)`
  ("pre-basin ascent") in place of `StrictAdjustment` / `hF_top` /
  `max xT xS < 1` — of row 2, of its canonical-horizon form, of row 1, of the
  package anchor `_from_package` and of its evidence-preserving form.
* `standardCompliance_min_drift_shock_generalF_from_sender_package_of_preBasinAscent`
  (round BH-1, item BH1.3, 2026-10-06) — the localised `thm:shock` anchor from
  the Sender persistence package (P1–P3 and P5), without the Target combined
  chord P4. The shock proof reads its package only through the persistence
  conclusions (i)–(iii), which `standardCompliance_persistence_generalF_from_sender_package`
  already delivers without P4; the full-package anchor is now its corollary
  through `GeneralFPersistencePackage.toSenderPersistencePackage`. The
  evidence-preserving form keeps the full package, because its last conjunct is
  conclusion (vi), the one P4 pays for.
* The Schur-margin forms (doc 110 R8(b)): each certificate sibling is proved
  first for `StandardComplianceLocalCoreCertificateSchur_MS`, whose contraction
  input is the Schur margin `L_TS·L_ST < (1 − β_T)(1 − β_S)` with diagonal
  bounds, instead of the two row sums `β_T + L_TS < 1`, `β_S + L_ST < 1`; the
  row-sum forms are one-line corollaries through `ofRowSum_MS`. Row 2 had no
  Schur sibling anywhere in the tree before this file.

## Direction (Rule 13)

Every sibling is weaker in hypotheses than the pinned theorem it sits beside,
with the conclusion verbatim (strictly weaker at the level of the transition
hypothesis; unwitnessed for the full hypothesis set, see Scope):

* `StrictAdjustment` implies pre-basin ascent below any `x̄ < 1`
  (`preBasinAscent_of_strictAdjustment`), and the certificate supplies
  `x̄ = max xT xS ∈ (0, 1)`;
* `hF_top` implies pre-basin ascent below any `x̄ < 1`
  (`preBasinAscent_of_hF_top`);
* for the package anchor, `max xT xS < 1` is dropped — it is derivable from
  pre-basin ascent and `0 ≤ max xT xS` (`lt_one_of_preBasinAscent`);
* the Schur certificate is implied by the row-sum one (`ofRowSum_MS`).

The recovery `example`s at the end of the file check each implication against
the pinned statement. The pinned rows are untouched (no headline-set change).

## Scope

Rule 9: the certificate theorems are existence statements ("there is an
equilibrium in the carriers such that …") about the equilibrium the
certificate constructs, not about every equilibrium of the economy; the
package theorems are about the equilibrium `E` the package is given. Rule 9B:
the Schur certificate class generalises the row-sum class, but every Schur
certificate in the tree is built through `ofRowSum_MS`; its extra generality
is, as yet, **unwitnessed**. The pre-basin weakening is proper at the level of
the transition hypotheses: `Examples/PreBasinAscentStrictness.lean`
(`exists_preBasinAscent_not_strictAdjustment`) exhibits an economy whose
transition satisfies pre-basin ascent below `1/2` but fails both global
ascent and F5. No certificate or persistence package is exhibited at such an
economy, so that the siblings here apply to an economy the pinned rows miss is
likewise **unwitnessed** at the level of the full theorems.

Rule 1: the equilibrium is constructed (Perov/Schur existence for the
certificate forms) or given as a `FeedbackStackelbergEquilibriumTop`; the only
fixed action path is the exogenous full-sanction shock, the project's sole
exogenous-phase exception.

Rule 22: general in `F`. Nothing here reads the affine law or `δ`.

Rule 3: no new assumption, no new field, no new `Prop` definition.

**Round BJ5.1 (2026-10-07).** Every theorem here that takes an MS or Schur MS
certificate, or names the canonical myopic equilibrium, takes
`[p.StaticSelectorContinuous]`. That class is the static-selector continuity
condition, the joint continuity of the static Sender selector `σ`, which was
the `Params` field `σ_continuous`. The content is unchanged; the condition
moved from the economy to the binder. The package-route theorems, which take a
`GeneralFPersistencePackage` and no certificate, do not take it. General in
`F`.
-/

import Sanctions.Theory.Certificates.StandardComplianceSchur
import Sanctions.Theory.Certificates.SenderPersistencePackage
import Sanctions.Theory.LockIn.LocalisedShockEntry

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The package anchor of `thm:shock`, localised -/

/-- **Quantitative general-`F` shock theorem from the Sender persistence
package, localised (round BH-1, item BH1.3).** For an already constructed
equilibrium `E` with the P4-free package `P` (P1–P3 and P5 on the basin
`[max xT xS, 1]`) and ascent at full sanction on `[0, max xT xS]`: there is an
attained minimum full-sanction drift `η > 0` on `[0, max xT xS]`, and after
`⌈max xT xS / η⌉₊` periods of imposed full sanction every feasible initial
state is in the basin; from there the equilibrium path stays in the basin, the
realised sanction is at least the pivot, and realised sanctions never fall.

Sibling of `standardCompliance_min_drift_shock_generalF_from_package_of_preBasinAscent`
with the conclusion verbatim. The dropped hypothesis is the Target combined
chord P4 (the field `target_combined_chord` of `GeneralFPersistencePackage`):
the Target's ranking over sanction levels. The shock proof reads its package
only through persistence conclusions (i)–(iii), and those follow from the
Sender's level input (P5 against P2) and direction input (P3) alone
(`standardCompliance_persistence_generalF_from_sender_package`). In economic
terms: once a temporary full sanction has pushed the state into the basin,
sanctions stay high because of the Sender's own incentives; whether the Target
incumbent prefers harsher sanctions there plays no role in this conclusion.
The Target is still present through its equilibrium policy, which enters the
Sender's objective in P3 and P5. Weaker in hypotheses (Rule 13): every full
package projects onto a Sender package (`toSenderPersistencePackage`), and the
full-package anchor is now proved as this theorem's corollary. General in
`F`. -/
theorem standardCompliance_min_drift_shock_generalF_from_sender_package_of_preBasinAscent
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.SenderPersistencePackage D E xT xS K_S)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) (max xT xS), x < p.F x 1) :
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
  obtain ⟨η, hη_pos, hη_attains, hη_floor, hentry⟩ :=
    p.shockPathF_exists_min_drift_uniform_natCeil_bound_of_preBasinAscent
      hpivot_nonneg hF_top_pre
  refine ⟨η, hη_pos, hη_attains, hη_floor, ?_⟩
  intro x₀shock hx₀shock
  have hNentry := hentry x₀shock hx₀shock (Nat.ceil (max xT xS / η)) le_rfl
  have hpersist :=
    p.standardCompliance_persistence_generalF_from_sender_package P _ hNentry
  exact ⟨hNentry, hpersist.1, hpersist.2.1, hpersist.2.2⟩

/-- **Paper-facing quantitative general-`F` shock theorem, localised (doc 110
R7(iii) of the verifier: the main `thm:shock` anchor).** For an already
constructed equilibrium `E` with the general-`F` persistence package `P` on
the basin `[max xT xS, 1]`: there is an attained minimum full-sanction drift
`η > 0` on `[0, max xT xS]`, and after `⌈max xT xS / η⌉₊` periods of imposed
full sanction every feasible initial state is in the basin; from there the
equilibrium path stays in the basin, the realised sanction is at least the
pivot, and realised sanctions never fall.

Sibling of `standardCompliance_min_drift_shock_generalF_from_package`, whose
two transition hypotheses — strict adjustment `hAdj` (two-sided, whole
square) and the pivot bound `max xT xS < 1` — are replaced by the single
hypothesis that full sanction strictly raises every state in
`[0, max xT xS]`. Weaker in hypotheses (Rule 13): the old pair implies the
new hypothesis, and the pivot bound is derivable from it. Strictly so at the
level of the transition hypothesis (`Examples/PreBasinAscentStrictness.lean`);
unwitnessed for the full hypothesis set.

Round BH-1 (item BH1.3): proved as a corollary of
`standardCompliance_min_drift_shock_generalF_from_sender_package_of_preBasinAscent`
through `toSenderPersistencePackage`. The package's Target combined chord (P4)
is not read by this conclusion. The statement is unchanged. General in `F`. -/
theorem standardCompliance_min_drift_shock_generalF_from_package_of_preBasinAscent
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.GeneralFPersistencePackage D E xT xS K_S)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) (max xT xS), x < p.F x 1) :
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
                (Nat.ceil (max xT xS / η)))) :=
  p.standardCompliance_min_drift_shock_generalF_from_sender_package_of_preBasinAscent
    (GeneralFPersistencePackage.toSenderPersistencePackage p P) hF_top_pre

-- The `_of_preBasinAscent` name keeps the sibling pattern of the pinned row it
-- sits beside, and it passes the 100-character limit; accepted for this declaration.
set_option linter.style.longLine false in
/-- **The package anchor with both-player post-entry evidence, localised.**
Sibling of
`standardCompliance_min_drift_shock_generalF_with_equilibrium_evidence_from_package`
with `hAdj` and `max xT xS < 1` replaced by ascent at full sanction on
`[0, max xT xS]`. The conclusion is verbatim: after the minimum-drift horizon
every feasible start is in the basin, and at every later endogenous date the
path records basin invariance, the sanction floor, sanction monotonicity,
Target feasibility and Bellman optimality, Sender Bellman optimality, and
the Target's monotone sanction preference above the realised-state floor.
Weaker in hypotheses (Rule 13); strictly so at the level of the transition
hypothesis (`Examples/PreBasinAscentStrictness.lean`), unwitnessed for the
full hypothesis set. General in `F`. -/
theorem standardCompliance_min_drift_shock_generalF_with_equilibrium_evidence_from_package_of_preBasinAscent
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.GeneralFPersistencePackage D E xT xS K_S)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) (max xT xS), x < p.F x 1) :
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
  obtain ⟨η, hη_pos, hη_attains, hη_floor, hentry⟩ :=
    p.shockPathF_exists_min_drift_uniform_natCeil_bound_of_preBasinAscent
      hpivot_nonneg hF_top_pre
  refine ⟨η, hη_pos, hη_attains, hη_floor, ?_⟩
  intro x₀shock hx₀shock
  have hNentry := hentry x₀shock hx₀shock (Nat.ceil (max xT xS / η)) le_rfl
  have hpersist :=
    p.standardCompliance_persistence_generalF_with_equilibrium_evidence_from_package
      P _ hNentry
  exact ⟨hNentry, hpersist⟩

/-! ## Schur-form certificate: the Goals-1–2 core and the localised shock -/

namespace StandardComplianceLocalCoreCertificateSchur_MS

/-- **Goals 1 and 2 from the Schur-form certificate, with no transition
hypothesis.** From the certificate alone there is a top-selector feedback
Stackelberg equilibrium whose value functions lie in the certificate's
carriers, such that (Goal 1) from every basin state `x₀ ∈ [max xT xS, 1]` the
general-`F` equilibrium path stays in the basin, the realised sanction is at
least the pivot, and realised sanctions never fall; and (Goal 2) on the basin
the forward-looking equilibrium sanction is at least the canonical myopic
equilibrium sanction.

This is `three_goals_local_MS_generalF` (Schur form) with its Goal-3 shock
step removed — the only step that read `hF_top`. Its proof calls the same
lemmas: Perov/Schur existence, the carrier-to-equilibrium lift, the one-sided
threshold constructor, interval-dominance rule monotonicity, the joint basin,
the long-run path theorem, and floor-plus-myopic-ceiling dominance.
General in `F`. -/
theorem two_goals_local_MS_generalF [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificateSchur_MS) :
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
  -- Step 1 (Schur form): produce equilibrium via the Perov existence.
  obtain ⟨E, hVT, hVS, hα_eq⟩ :=
    C.D.exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur
      C.h_inv C.hT_T_op C.hT_S_op C.hβ_T_lt C.hβ_S_lt C.hSchur
  let V_T_sub : C.D.CarrierT := ⟨E.V_T, hVT⟩
  let V_S_sub : C.D.CarrierS := ⟨E.V_S, hVS⟩
  change E.α = C.D.α_on V_T_sub V_S_sub at hα_eq
  -- Step 2: lift MS-form primitives at the equilibrium.
  have hV_S_mono : Monotone E.V_S := C.hV_S_mono_carrier E.V_S hVS
  have h_stage_sender :
      ∀ x ∈ Set.Icc C.xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x (max C.xT C.xS))) := by
    intro x hx
    rw [hα_eq]
    exact C.h_stage_sender_strictMono V_T_sub V_S_sub x hx
  have h_target_combined :=
    TargetCombinedChordOn.at_equilibrium p C.h_target_combined E hVT hVS hα_eq
  have hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max C.xT C.xS) 1)
        (fun s x => p.senderDynObjective E.V_S x (E.α x) s) := by
    have h := C.hIDO_on V_T_sub V_S_sub
    convert h using 2
    rw [hα_eq]
  -- Step 3: the joint-preference basin at the equilibrium.
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α C.xT C.xS (max C.xT C.xS) :=
    OneSidedSanctionPreferenceThresholds.of_stage_sender_and_target_combined_chord
      p hV_S_mono C.hxT_mem C.hxS_mem
      ⟨le_of_lt C.hpivot_mem.1, le_of_lt C.hpivot_mem.2⟩
      h_stage_sender h_target_combined
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max C.xT C.xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO
  have hα_feas : ∀ x ∈ Set.Icc (max C.xT C.xS) 1, E.α x ∈ Sanctions.I := by
    intro x hx
    exact E.α_mem x ⟨le_trans (le_max_of_le_left C.hxT_mem.1) hx.1, hx.2⟩
  have hα_opt : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
      IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S x a)
        Sanctions.I (E.α x) := by
    intro x hx
    exact E.α_opt_top x ⟨le_trans (le_max_of_le_left C.hxT_mem.1) hx.1, hx.2⟩
  have hB := JointPreferenceBasinTop.of_oneSidedThresholds p hOne hα_feas hTopMono hα_opt
  -- Goal 1: general-`F` persistence, universally over basin starts.
  have hGoal1 : ∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
              ∈ Set.Icc (max C.xT C.xS) 1) ∧
      (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
    intro x₀ hx₀
    have h := p.jointPreferenceBasinTopF_long_run_nonDecreasing hB hx₀
    exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  -- Goal 2: dynamic-over-myopic dominance (transition-independent).
  have hFloor : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
      max x (max C.xT C.xS) ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
    JointPreferenceBasinTop.level_dyn_top p hB
  have hGoal2 :=
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling
  exact ⟨E, hVT, hVS, hGoal1, hGoal2⟩

/-- **Row 2 in Schur form, localised (doc 110 R8(b) and R7(a)).** From the
Schur-form certificate and ascent at full sanction on the pre-basin interval
`[0, max xT xS]`: the Goals-1–2 conclusion of `two_goals_local_MS_generalF`,
together with an attained minimum full-sanction drift `η > 0` on
`[0, max xT xS]` and one explicit shock duration `⌈max xT xS / η⌉₊` that
moves every feasible initial state into the basin, after which the
equilibrium path stays in the basin with the realised sanction at least the
pivot.

The conclusion is verbatim that of headline row 2
(`standardCompliance_three_goals_local_MS_generalF_min_drift_shock`). Against
it, the certificate's row sums are replaced by the Schur margin, and strict
adjustment by pre-basin ascent. Rule 9B: the Schur certificate class is
inhabited in the tree only through `ofRowSum_MS`, so its extra generality over
the row-sum class is as yet unwitnessed. General in `F`. -/
theorem three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificateSchur_MS)
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
  obtain ⟨E, hVT, hVS, hpaths, hdom⟩ := two_goals_local_MS_generalF p C
  obtain ⟨η, hη_pos, hη_attains, hη, hentry⟩ :=
    p.shockPathF_exists_min_drift_uniform_natCeil_bound_of_preBasinAscent
      (le_of_lt C.hpivot_mem.1) hF_top_pre
  refine ⟨E, hVT, hVS, hpaths, hdom, η, hη_pos, hη_attains, hη, ?_⟩
  intro x₀shock hx₀shock
  have hNentry := hentry x₀shock hx₀shock (Nat.ceil (max C.xT C.xS / η)) le_rfl
  obtain ⟨hinv, hfloor, _⟩ := hpaths _ hNentry
  exact ⟨hNentry, hinv, hfloor⟩

/-- **Canonical-horizon form in Schur form, localised.** As
`three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent`, with the
shock conclusion evaluated at the named horizon
`fullShockEntryHorizon (max xT xS) = ⌈max xT xS / η_F(max xT xS)⌉` instead of
an existentially chosen drift constant. Conclusion verbatim that of
`standardCompliance_three_goals_local_MS_generalF_canonical_shock`; Schur
margin for row sums and pre-basin ascent for strict adjustment. Rule 9B: the
Schur certificate class is inhabited in the tree only through `ofRowSum_MS`,
so its extra generality over the row-sum class is as yet unwitnessed.
General in `F`. -/
theorem three_goals_local_MS_generalF_canonical_shock_of_preBasinAscent [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificateSchur_MS)
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
  obtain ⟨E, hVT, hVS, hpaths, hdom⟩ := two_goals_local_MS_generalF p C
  have hentry :=
    p.shockPathF_uniform_fullShockEntryHorizon_of_preBasinAscent
      (le_of_lt C.hpivot_mem.1) hF_top_pre
  refine ⟨E, hVT, hVS, hpaths, hdom, ?_⟩
  intro x₀shock hx₀shock
  have hNentry := hentry x₀shock hx₀shock
    (p.fullShockEntryHorizon (max C.xT C.xS)) le_rfl
  obtain ⟨hinv, hfloor, _⟩ := hpaths _ hNentry
  exact ⟨hNentry, hinv, hfloor⟩

/-- **Row 1 in Schur form, localised.** The conclusion of
`three_goals_local_MS_generalF` (Schur form) — Goals 1 and 2, and for every
feasible shock start some finite full-sanction duration after which the
equilibrium path stays in the basin with the sanction at least the pivot —
with the global ascent `hF_top` on `[0, 1)` replaced by ascent on
`[0, max xT xS]`. Weaker in hypotheses (`preBasinAscent_of_hF_top` and the
certificate's `max xT xS < 1`); strictly so at the level of the transition
hypothesis (`Examples/PreBasinAscentStrictness.lean`), unwitnessed for the
full hypothesis set. Rule 9B: the Schur certificate class is inhabited in the
tree only through `ofRowSum_MS`, so its extra generality over the row-sum
class is as yet unwitnessed. General in `F`. -/
theorem three_goals_local_MS_generalF_of_preBasinAscent [p.StaticSelectorContinuous]
    (C : p.StandardComplianceLocalCoreCertificateSchur_MS)
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
    three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent p C hF_top_pre
  refine ⟨E, hVT, hVS, hpaths, hdom, ?_⟩
  intro x₀shock h_nn h_le
  obtain ⟨-, h1, h2⟩ := hshock x₀shock ⟨h_nn, h_le⟩
  exact ⟨_, h1, h2⟩

end StandardComplianceLocalCoreCertificateSchur_MS

/-! ## Row-sum certificate: the Goals-1–2 core -/

namespace StandardComplianceLocalCoreCertificate_MS

/-- **Goals 1 and 2 from the row-sum MS certificate, with no transition
hypothesis.** The conclusion of
`StandardComplianceLocalCoreCertificateSchur_MS.two_goals_local_MS_generalF`
for the row-sum certificate: every row-sum certificate is a Schur-form
certificate with the same carriers, pivots and stage fields (`ofRowSum_MS`),
so this is that theorem at `ofRowSum_MS C`. It is
`three_goals_local_MS_generalF` without the Goal-3 step that read `hF_top`.
General in `F`. -/
theorem two_goals_local_MS_generalF [p.StaticSelectorContinuous]
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
  StandardComplianceLocalCoreCertificateSchur_MS.two_goals_local_MS_generalF p
    (StandardComplianceLocalCoreCertificateSchur_MS.ofRowSum_MS p C)

end StandardComplianceLocalCoreCertificate_MS

/-! ## Paper-facing row-sum siblings of rows 1 and 2 -/

-- The `_of_preBasinAscent` name keeps the sibling pattern of the pinned row it
-- sits beside, and it passes the 100-character limit; accepted for this declaration.
set_option linter.style.longLine false in
/-- **Sibling of headline row 2 with pre-basin ascent (doc 110 R7(a)).** From
the row-sum MS certificate `C` and ascent at full sanction on the pre-basin
interval `[0, max xT xS]`: there is an equilibrium in the certificate's
carriers such that its path persists in the basin from every basin start
(state stays in `[max xT xS, 1]`, sanction at least the pivot and
non-decreasing), its sanction rule dominates the canonical myopic rule on the
basin, and there is an attained minimum full-sanction drift `η > 0` on
`[0, max xT xS]` for which one shock of `⌈max xT xS / η⌉₊` periods moves every
feasible initial state into the basin, after which the equilibrium path stays
there with the sanction at least the pivot.

Conclusion verbatim that of
`standardCompliance_three_goals_local_MS_generalF_min_drift_shock`.
Hypotheses: `StrictAdjustment` (two-sided, whole square) is replaced by
ascent at full sanction on `[0, max xT xS]` only. Weaker in hypotheses
(Rule 13; see the recovery `example` below); strictly so at the level of the
transition hypothesis (`Examples/PreBasinAscentStrictness.lean`), unwitnessed
for the full hypothesis set. Proved as the Schur-form sibling at
`ofRowSum_MS C`. General in `F`. -/
theorem standardCompliance_three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent
    [p.StaticSelectorContinuous]
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
  StandardComplianceLocalCoreCertificateSchur_MS.three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent
    p (StandardComplianceLocalCoreCertificateSchur_MS.ofRowSum_MS p C) hF_top_pre

-- The `_of_preBasinAscent` name keeps the sibling pattern of the pinned row it
-- sits beside, and it passes the 100-character limit; accepted for this declaration.
set_option linter.style.longLine false in
/-- **Sibling of the canonical-horizon row-2 form with pre-basin ascent.**
Conclusion verbatim that of
`standardCompliance_three_goals_local_MS_generalF_canonical_shock`, with
`StrictAdjustment` replaced by ascent at full sanction on `[0, max xT xS]`
(weaker in hypotheses; strictly so at the level of the transition hypothesis,
`Examples/PreBasinAscentStrictness.lean`; unwitnessed for the full hypothesis
set). The shock conclusion is at the named horizon
`fullShockEntryHorizon (max xT xS)`. General in `F`. -/
theorem standardCompliance_three_goals_local_MS_generalF_canonical_shock_of_preBasinAscent
    [p.StaticSelectorContinuous]
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
                      (p.fullShockEntryHorizon (max C.xT C.xS))) n) :=
  StandardComplianceLocalCoreCertificateSchur_MS.three_goals_local_MS_generalF_canonical_shock_of_preBasinAscent
    p (StandardComplianceLocalCoreCertificateSchur_MS.ofRowSum_MS p C) hF_top_pre

-- The `_of_preBasinAscent` name keeps the sibling pattern of the pinned row it
-- sits beside, and it passes the 100-character limit; accepted for this declaration.
set_option linter.style.longLine false in
/-- **Sibling of headline row 1 with pre-basin ascent.** Conclusion verbatim
that of `standardCompliance_three_goals_local_MS_generalF` (Goals 1 and 2,
and for every feasible shock start some finite full-sanction duration after
which the equilibrium path stays in the basin with the sanction at least the
pivot); the global ascent `hF_top` on `[0, 1)` is replaced by ascent on
`[0, max xT xS]` (weaker in hypotheses, via the certificate's
`max xT xS < 1`; strictly so at the level of the transition hypothesis,
`Examples/PreBasinAscentStrictness.lean`; unwitnessed for the full hypothesis
set).
With this theorem row 1 is a corollary of the row-2 sibling above.
General in `F`. -/
theorem standardCompliance_three_goals_local_MS_generalF_of_preBasinAscent
    [p.StaticSelectorContinuous]
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
  StandardComplianceLocalCoreCertificateSchur_MS.three_goals_local_MS_generalF_of_preBasinAscent
    p (StandardComplianceLocalCoreCertificateSchur_MS.ofRowSum_MS p C) hF_top_pre

/-! ## Rule-13 recovery checks

Each pinned statement follows from its localised sibling, with its own
premises, through the implications of `LocalisedShockEntry.lean`. -/

/-- Headline row 2 from its localised sibling. -/
example [p.StaticSelectorContinuous] (C : p.StandardComplianceLocalCoreCertificate_MS)
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
  p.standardCompliance_three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent C
    (p.preBasinAscent_of_strictAdjustment hAdj C.hpivot_mem.2)

/-- Headline row 1 from its localised sibling. -/
example [p.StaticSelectorContinuous] (C : p.StandardComplianceLocalCoreCertificate_MS)
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
  p.standardCompliance_three_goals_local_MS_generalF_of_preBasinAscent C
    (p.preBasinAscent_of_hF_top hF_top C.hpivot_mem.2)

/-- The package anchor of `thm:shock` from its localised sibling. -/
example {D : p.ValueClass2} {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ} (P : p.GeneralFPersistencePackage D E xT xS K_S)
    (hAdj : p.StrictAdjustment) (hpivot_lt : max xT xS < 1) :
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
                (Nat.ceil (max xT xS / η)))) :=
  p.standardCompliance_min_drift_shock_generalF_from_package_of_preBasinAscent P
    (p.preBasinAscent_of_strictAdjustment hAdj hpivot_lt)

-- The `_of_preBasinAscent` name keeps the sibling pattern of the pinned row it
-- sits beside, and it passes the 100-character limit; accepted for this declaration.
set_option linter.style.longLine false in
/-- The Schur form of row 2 with the pinned row's own transition hypothesis
(strict adjustment): the direct Schur analogue of row 2. -/
example [p.StaticSelectorContinuous] (C : p.StandardComplianceLocalCoreCertificateSchur_MS)
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
  StandardComplianceLocalCoreCertificateSchur_MS.three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent
    p C (p.preBasinAscent_of_strictAdjustment hAdj C.hpivot_mem.2)

end Params
end AbstractGame

end

-- The axiom report below names declarations in full; several names pass the
-- 100-character line limit, which is accepted for these report lines only.
set_option linter.style.longLine false

#print axioms Sanctions.AbstractGame.Params.standardCompliance_min_drift_shock_generalF_from_sender_package_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.standardCompliance_min_drift_shock_generalF_from_package_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.standardCompliance_min_drift_shock_generalF_with_equilibrium_evidence_from_package_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur_MS.two_goals_local_MS_generalF
#print axioms Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur_MS.three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur_MS.three_goals_local_MS_generalF_canonical_shock_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur_MS.three_goals_local_MS_generalF_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.StandardComplianceLocalCoreCertificate_MS.two_goals_local_MS_generalF
#print axioms Sanctions.AbstractGame.Params.standardCompliance_three_goals_local_MS_generalF_min_drift_shock_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.standardCompliance_three_goals_local_MS_generalF_canonical_shock_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.standardCompliance_three_goals_local_MS_generalF_of_preBasinAscent

end Sanctions
