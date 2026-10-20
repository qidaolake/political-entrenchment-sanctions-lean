/-
Sanctions/Examples/AffineInstance/ComplianceTower.lean

**The affine transition as a worked instance: the standard-compliance
certificate tower.**

Thirty-nine declarations moved out of `Sanctions/Theory/` on 2026-08-22 --- the
upper half of the affine tower, and the largest single block of it.

What is here, in English.

* **The affine margin recovery.** `hS_margin_delta` (in both the plain and the
  Schur-complement certificate namespaces) takes a certificate stated over a
  general chord rate and reads off the affine-rate margin
  `beta_S * K_S * delta < m_S`. It is a bridge *down* to the instance: it
  consumes the general certificate and the affine law, and it is the reason the
  affine results are corollaries of the general ones rather than the other way
  round. (The Target recovery `hT_loss_margin_delta`,
  `c_T <= beta_T * g_T * delta`, was deleted in round BJ1.4, 2026-10-07, together
  with the certificates' loss-offset fields it read.)
* **The three-goals theorems in every affine variant** --- fixed-start,
  uniform-start, regime-comparison, weak-persistence, C1, path-optimality, and
  selector-equivalence. Each states that a persistence, a shock-response and a
  dominance goal hold together at the certificate's equilibrium.
* **The certificate smart constructors** (`with_KS_closed_form`,
  `with_hSC_on_derived`, the three `with_strict_slope_wedge` variants), which
  build a certificate by discharging its harder fields from primitives rather
  than demanding them.
* **The stage-flip route**, the weak-floor ratchet counterexample, the Sender
  lower-slope cone results, and the convex-value single-crossing dischargers.

The general-`F` siblings that remain in `Theory/` are what the headline results
actually use; none of them reaches anything in this file.

**Why these are in `Examples/` and not `Theory/`.** Every declaration below
carries `hF : p.F = affineF p.delta` in its statement --- the hypothesis that
one unit of sanction moves next period's political state by exactly `delta`, the
same amount at every state and every sanction level. Under Rule 22 that makes
each one affine-restricted by construction, so each is an *instance*, not part
of the general theory.

Nothing is deleted and nothing is weakened: each still type-checks exactly as it
did in `Theory/`, and each still earns its keep as an exhibit of what the affine
law discharges for free. What changed is only where they live, and therefore
what the general theory is allowed to lean on.

Checked before the move (Rule 23, three gates): the citation graph reported no
consumer outside the affine set itself; a textual sweep of `paper/`, `*.md` and
`*.lean` recorded every prose citation, and the paper was synced in the same
round for those it found (Rule 2); and `lake build` is the gate that settles it.

**Round BH1.7 (2026-10-06): the tower as instances.** The five affine
three-goals bodies that re-proved the certificate route through the affine
persistence and shock bridges (`three_goals_local`, the core
`three_goals_local_uniform_starts`, `three_goals_local_regime_comparison`, the
core `three_goals_local_regime_comparison_uniform_starts` and the Schur
`three_goals_local_uniform_starts`) are now instances of their general-`F`
siblings in `Theory/Certificates/GeneralFDischargers.lean`. Each keeps its
statement and its `hF`: `hF` gives `hAdj` (`strictAdjustment_of_F_eq_affineF`)
and turns every affine trajectory object into its general-`F` counterpart
(`pathFamilies_eq_pathFamiliesF_of_affine`). The two misnamespaced
`StandardComplianceLocalCertificate` copies that take a core certificate are
now one-line aliases of the core names. The affine persistence and shock
bridges stay: `three_goals_local_C1` still uses them.
-/

import Sanctions.Examples.AffineInstance.Bridges
import Sanctions.Examples.AffineInstance.TransitionChords
import Sanctions.Examples.AffineInstance.Kinematics

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame

namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Affine → general bridge for rule paths (round BH1.7, 2026-10-06).** Under
`hF : p.F = affineF p.δ` the hard-coded affine sanction sequence under a realised
rule `R` (`ruleSanctions`, whose step is `(1 − δ)·x + δ·R x`) equals the
general-`F` one (`ruleSanctionsF`, whose step is `F(x, R x)`) at every horizon.
The two definitions differ only in that step, so the content is that the two
state paths agree. Affine-restricted by its `hF` binder: a bridge is the one
place the affine law belongs in a signature. -/
theorem ruleSanctions_eq_ruleSanctionsF_of_affine
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) (R : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.ruleSanctions R x₀ n = p.ruleSanctionsF R x₀ n := by
  have hstep : (fun x => p.ruleStep R x) = (fun x => p.ruleStepF R x) := by
    funext x
    unfold ruleStep ruleStepF
    rw [hF]
    simp only [Sanctions.AbstractGame.affineF]
  unfold ruleSanctions ruleSanctionsF rulePath rulePathF
  rw [hstep]

/-- **The affine trajectory families are the general-`F` ones, as functions
(round BH1.7, 2026-10-06).** Under `hF : p.F = affineF p.δ`, the hard-coded
affine state path, sanction sequence, shock path and rule-sanction sequence are
equal to their general-`F` counterparts as whole functions. Stated without any
free argument, each equation rewrites a goal under its binders (`∀ x₀`, `∃ E`,
`Monotone …`), which is how the affine three-goals theorems below become
instances of the general-`F` ones. Affine-restricted by its `hF` binder; built
from the `Kinematics.lean` bridges and `ruleSanctions_eq_ruleSanctionsF_of_affine`. -/
theorem pathFamilies_eq_pathFamiliesF_of_affine
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    p.dynamicTopLockInPath = p.dynamicTopLockInPathF
      ∧ p.dynamicTopLockInSanctions = p.dynamicTopLockInSanctionsF
      ∧ p.shockPath = p.shockPathF
      ∧ p.ruleSanctions = p.ruleSanctionsF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext V_S α x₀ n
    exact p.dynamicTopLockInPath_eq_pathF_of_affine hF V_S α x₀ n
  · funext V_S α x₀ n
    exact p.dynamicTopLockInSanctions_eq_sanctionsF_of_affine hF V_S α x₀ n
  · funext x₀ n
    exact p.shockPath_eq_shockPathF_of_affine hF x₀ n
  · funext R x₀ n
    exact p.ruleSanctions_eq_ruleSanctionsF_of_affine hF R x₀ n

/-- **Anchored finite shock entry along the affine path, without the Target's
sanction ranking and without a positive floor (round BH1.5, 2026-10-06).**

The affine-path sibling of
`equilibriumTop_senderPersistenceF_temporary_shock_permanent_high`: from any
feasible start, a temporary full-sanction shock brings the hard-coded affine
shock path into the basin `[x̄, 1]` after finitely many periods, and from there
the equilibrium state path never leaves the basin, the realised sanction stays
above both floors `s̄` and `x̄` and never falls, and the Target's action is a
maximiser of its joint objective at every date. Compared with the joint-basin
form `jointPreferenceBasinTop_temporary_shock_permanent_high` it drops the
Target sanction-preference conclusion (so it needs only the Sender persistence
basin, not P4) and it drops the positivity conjunct `0 < s_n` together with its
hypothesis `0 < s̄`.

Affine-restricted on axis 2: `dynamicTopLockInPath`, `dynamicTopLockInSanctions`
and `shockPath` hard-code the affine law. No `hF` binder; under `hF` the
objects coincide with the general-`F` ones (`pathFamilies_eq_pathFamiliesF_of_affine`).
It prepared the removal of the certificates' `hsbar_pos` field, done in round BJ1.4
(2026-10-07). -/
theorem equilibriumTop_senderPersistence_temporary_shock_permanent_high
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar sbar x₀ : ℝ}
    (hB : p.SenderPersistenceBasinTop E.V_S E.α xbar sbar)
    (hxbar_lt_one : xbar < 1)
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      (∀ n, xbar ≤ p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α (p.shockPath x₀ N)) ∧
      (∀ n, IsMaxOn
        (fun a => p.joint_T_top_integrand E.V_T E.V_S
                    (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n) a)
        Sanctions.I
        (E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n))) := by
  have hlevel := SenderPersistenceBasinTop.level_dyn_top p hB
  obtain ⟨N, hN⟩ := p.shockPath_eventually_in_basin hx₀_nn hx₀_le hxbar_lt_one
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  have hpath := p.dynamicTopLockInPath_mem_basin E.V_S E.α hlevel h_N_in
  refine ⟨N, hpath, p.dynamicTopLockInSanctions_floor E.V_S E.α hlevel h_N_in,
    p.dynamicTopLockInSanctions_ge_xbar E.V_S E.α hlevel h_N_in,
    p.dynamicTopLockInSanctions_mono E.V_S E.α hlevel hB.top_rule_mono h_N_in, ?_⟩
  intro n
  exact E.α_opt_top _ ⟨le_trans hB.xbar_nonneg (hpath n).1, (hpath n).2⟩

namespace StandardComplianceLocalCoreCertificate

/-- **The Sender margin at the affine rate.** From `β_S·K_S·d < m_S` and
`δ ≤ d`, forced by the certificate's own upper chord at an affine economy. -/
theorem hS_margin_delta (C : p.StandardComplianceLocalCoreCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    p.β_S * C.KS * p.δ < C.mS := by
  have hδ_le_d : p.δ ≤ C.d := by
    have hxS1 : (1 : ℝ) ∈ Set.Icc C.xS (1 : ℝ) := ⟨C.hxS_mem.2, le_refl _⟩
    have hsbar_pos : 0 < max (1 : ℝ) C.sbar := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (max (1 : ℝ) C.sbar) :=
      ⟨le_refl _, le_of_lt hsbar_pos⟩
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) (max (1 : ℝ) C.sbar) :=
      ⟨zero_le_one, le_max_left _ _⟩
    have h := C.hF_chord 1 hxS1 0 h0 1 h1 zero_le_one
    have hval : p.F 1 1 - p.F 1 0 = p.δ := by
      rw [hF]; unfold Sanctions.AbstractGame.affineF; ring
    rw [hval] at h
    have : p.δ ≤ C.d * (1 - 0) := le_trans (le_abs_self _) h
    linarith
  have hKS_nn : 0 ≤ p.β_S * C.KS :=
    mul_nonneg p.β_S_mem.1 C.hKS_nonneg
  calc p.β_S * C.KS * p.δ ≤ p.β_S * C.KS * C.d :=
        mul_le_mul_of_nonneg_left hδ_le_d hKS_nn
    _ < C.mS := C.hS_margin

-- Round BJ1.4 (2026-10-07): `hT_loss_margin_delta` (the Target loss-offset margin
-- at the affine rate) stood here. It read the certificate fields `cT`, `gT`, `dlo`,
-- `hchord_lo`, `hgT_nn` and `hT_loss_margin`, which the round deleted; it had no
-- consumer. The Sender analogue `hS_margin_delta` above is unaffected.

/-- **Uniform-starts three goals at the affine law (instance, round BH1.7).**

Consumes the start-free core certificate, and the path-level conclusions are
quantified universally over starting states, which matches the manuscript's
"for every starting state `x₀ ∈ B`" (Proposition 1) and "for every initial state
`x₀ ∈ [0, 1]`" (Proposition 3) wording. Since round BH1.7 (2026-10-06) it is
an instance of `three_goals_local_uniform_starts_generalF`: `hF`
gives `hAdj` through `strictAdjustment_of_F_eq_affineF` and turns the affine
trajectory objects into the general-`F` ones
(`pathFamilies_eq_pathFamiliesF_of_affine`). Affine-restricted by its `hF`
binder; the general statement is the `_generalF` sibling. -/
theorem three_goals_local_uniform_starts
    (C : p.StandardComplianceLocalCoreCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPath E.V_S E.α
                    (p.shockPath x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                            (p.shockPath x₀shock N) n) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                    (p.shockPath x₀shock N) n)) := by
  obtain ⟨ePath, eSanc, eShock, -⟩ := p.pathFamilies_eq_pathFamiliesF_of_affine hF
  rw [ePath, eSanc, eShock]
  exact C.three_goals_local_uniform_starts_generalF p
    (Sanctions.AbstractGame.strictAdjustment_of_F_eq_affineF p p.δ_mem hF)

/-- **Uniform-starts regime comparison at the affine law (instance, round
BH1.7).** The three goals plus the statewise and the pathwise (every basin start,
every date) comparison of the myopic and forward-looking equilibrium sanction
paths, under myopic basin preservation `hMyoBasin`. Since round BH1.7
(2026-10-06) an instance of
`three_goals_local_regime_comparison_uniform_starts_generalF`, with `hAdj`
derived from `hF` and the affine trajectory objects, `ruleSanctions` included,
rewritten into the general-`F` ones. Affine-restricted by its `hF` binder. The
comparison alone, with neither `hF` nor `hAdj`, is
`pathwise_dominance_generalF`. -/
theorem three_goals_local_regime_comparison_uniform_starts
    (C : p.StandardComplianceLocalCoreCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (hMyoBasin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.myopicEquilibriumRule C.M x ∈ Set.Icc (max C.xT C.xS) 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.myopicEquilibriumRule C.M x ≤ p.dynamicEquilibriumRule E x)
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
           ∀ n, p.ruleSanctions (p.myopicEquilibriumRule C.M) x₀ n
                  ≤ p.ruleSanctions (p.dynamicEquilibriumRule E) x₀ n)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPath E.V_S E.α
                    (p.shockPath x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                            (p.shockPath x₀shock N) n) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                    (p.shockPath x₀shock N) n)) := by
  obtain ⟨ePath, eSanc, eShock, eRule⟩ := p.pathFamilies_eq_pathFamiliesF_of_affine hF
  rw [ePath, eSanc, eShock, eRule]
  exact C.three_goals_local_regime_comparison_uniform_starts_generalF p
    (Sanctions.AbstractGame.strictAdjustment_of_F_eq_affineF p p.δ_mem hF) hMyoBasin

end StandardComplianceLocalCoreCertificate

namespace StandardComplianceLocalCertificate

/-- **Audit-49 Item 2 (carrier-local statewise three-goals theorem).**

Carrier-local analog of
`RegularEconomyCertificateComplianceCore.three_goals_statewise`, at the
certificate's stored starts `C.x₀` and `C.x₀shock`. Since round BH1.7
(2026-10-06) an instance of the general-`F`
`StandardComplianceLocalCoreCertificate.three_goals_local_generalF`: `hF` gives
`hAdj` (`strictAdjustment_of_F_eq_affineF`) and turns the affine trajectory
objects into the general-`F` ones (`pathFamilies_eq_pathFamiliesF_of_affine`).
Affine-restricted by its `hF` binder. -/
theorem three_goals_local (C : p.StandardComplianceLocalCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
         (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
         (∀ n, IsMaxOn
           (fun a => p.joint_T_top_integrand E.V_T E.V_S
                       (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
           Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) := by
  obtain ⟨ePath, eSanc, eShock, -⟩ := p.pathFamilies_eq_pathFamiliesF_of_affine hF
  rw [ePath, eSanc, eShock]
  exact StandardComplianceLocalCoreCertificate.three_goals_local_generalF p C
    (Sanctions.AbstractGame.strictAdjustment_of_F_eq_affineF p p.δ_mem hF)

/-- **Uniform-starts variant of `three_goals_local` (2026-06-01).**

Consumes the start-free `StandardComplianceLocalCoreCertificate`
(NOT the fixed-start extension), and the path-level conclusions
are quantified **universally** over starting states rather than at
stored `x₀` / `x₀shock` fields. This makes the Lean
theorem literally match the manuscript's "for every starting state
`x₀ ∈ B`" (Proposition 1) and "for every initial state
`x₀ ∈ [0, 1]`" (Proposition 3) wording.

Since round BH1.7 (2026-10-06) a one-line alias of
`StandardComplianceLocalCoreCertificate.three_goals_local_uniform_starts`,
which carries the proof: an instance of the general-`F`
`three_goals_local_uniform_starts_generalF`, with `hAdj` derived from `hF` and
the affine trajectory objects rewritten into the general-`F` ones. The name sits
in the `StandardComplianceLocalCertificate` namespace but takes a core
certificate; it is kept for its existing citations. Affine-restricted by its
`hF` binder.

Because the core certificate is start-free, there are no stored
`x₀` / `x₀shock` fields here at all; the fixed-start
`StandardComplianceLocalCertificate` extension exists separately for
the `three_goals_local` compatibility route. -/
theorem three_goals_local_uniform_starts
    (C : p.StandardComplianceLocalCoreCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPath E.V_S E.α
                    (p.shockPath x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                            (p.shockPath x₀shock N) n) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                    (p.shockPath x₀shock N) n)) :=
  StandardComplianceLocalCoreCertificate.three_goals_local_uniform_starts p C hF

/-- **Audit-49 follow-up Round 3 Optional-4.4: weak-persistence
local theorem.**

Carrier-local analog of
`RegularEconomyCertificateComplianceCore.three_goals_weak_persistence`.
Returns Goal 1 *basin invariance only* (no `sbar ≤ realized` floor,
no `Monotone realized` field), Goal 2 statewise dominance (same as
Core), Goal 3 post-shock *basin invariance only*. One-line corollary
of `three_goals_local` by extracting the weaker subset of conjuncts.

The strong-ratchet `three_goals_local` is the canonical preferred
theorem; this weak variant is for applications where the
strong-corner monotone conclusion is too narrow (e.g. discussions
of *long-run basin membership* without imposing literal monotone
sanctions at `x = 1`). -/
theorem three_goals_local_weak_persistence
    (C : p.StandardComplianceLocalCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                ∈ Set.Icc (max C.xT C.xS) 1)
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          ∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                ∈ Set.Icc (max C.xT C.xS) 1 := by
  obtain ⟨E, hVT, hVS, ⟨h_basin, _h_sbar, _h_maxXTXS, _h_mono, _h_argmax⟩,
          hGoal2, N, h_shock_basin, _h_shock_sbar, _h_shock_maxXTXS⟩ :=
    StandardComplianceLocalCertificate.three_goals_local p C hF
  exact ⟨E, hVT, hVS, h_basin, hGoal2, N, h_shock_basin⟩

/-- **Regime-comparison three-goals theorem (2026-06-01).**

Pathwise comparison between the fully forward-looking feedback
Stackelberg equilibrium and the fully myopic feedback equilibrium.
Returns the three goals of `three_goals_local` PLUS a stronger
Goal-2 conclusion: *from the certificate's stored starting state
`C.x₀`, the sanction path under the fully forward-looking
equilibrium rule `dynamicEquilibriumRule E` pointwise dominates the
sanction path under the fully myopic equilibrium rule
`myopicEquilibriumRule C.M`*. For the universal-start version (the
pathwise comparison from every basin start `x₀ ∈ B`), use
`three_goals_local_regime_comparison_uniform_starts`.

The pathwise comparison requires one new hypothesis beyond the
standard-compliance certificate: **myopic basin preservation**

  `hMyoBasin : ∀ x ∈ B, p.σ x (C.M.α x) ∈ B`.

Without it, the myopic-regime path can leave the basin and the
basin-local rule-comparison theorem
`ruleSanctions_le_of_rule_le_and_upper_monoOn_basin` (in
`DifferentPolicyComparator.lean`) does not apply forever. The
verdict's framing accepts that `hMyoBasin` may not hold in all
economically meaningful instantiations (sometimes the myopic
regime is expected to exit the basin) — in that case the user
should fall back to the statewise `three_goals_local` instead.

Since round BH1.7 (2026-10-06) an instance of the general-`F` fixed-start
`StandardComplianceLocalCertificate.three_goals_local_regime_comparison_generalF`:
`hF` gives `hAdj` and turns the affine trajectory objects, `ruleSanctions`
included, into the general-`F` ones. Affine-restricted by its `hF` binder. The
comparison alone, uniform over basin starts and with neither `hF` nor `hAdj`,
is `StandardComplianceLocalCoreCertificate.pathwise_dominance_generalF`. -/
theorem three_goals_local_regime_comparison
    (C : p.StandardComplianceLocalCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (hMyoBasin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.myopicEquilibriumRule C.M x ∈ Set.Icc (max C.xT C.xS) 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
         (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
         (∀ n, IsMaxOn
           (fun a => p.joint_T_top_integrand E.V_T E.V_S
                       (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
           Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      -- Goal 2 (statewise: same as three_goals_local):
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.myopicEquilibriumRule C.M x ≤ p.dynamicEquilibriumRule E x)
      -- New regime-comparison Goal 2' (pathwise):
      ∧ (∀ n, p.ruleSanctions (p.myopicEquilibriumRule C.M) C.x₀ n
                ≤ p.ruleSanctions (p.dynamicEquilibriumRule E) C.x₀ n)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) := by
  obtain ⟨ePath, eSanc, eShock, eRule⟩ := p.pathFamilies_eq_pathFamiliesF_of_affine hF
  rw [ePath, eSanc, eShock, eRule]
  exact three_goals_local_regime_comparison_generalF p C
    (Sanctions.AbstractGame.strictAdjustment_of_F_eq_affineF p p.δ_mem hF) hMyoBasin

/-- **Uniform-starts regime-comparison three-goals theorem (2026-06-01).**

Universal-start strengthening of `three_goals_local_regime_comparison`.
The equilibrium `E` is constructed once from the start-independent
value-class machinery of `C.D`; then

* **Goal 1 (persistence)** is quantified over every basin start
  `∀ x₀ ∈ Set.Icc (max xT xS) 1, ...`;
* **Goal 2 (statewise dominance)** is start-independent;
* **Goal 2′ (pathwise dynamic-over-myopic comparison)** is quantified
  over every basin start `∀ x₀ ∈ Set.Icc (max xT xS) 1, ∀ n, ...`;
* **Goal 3 (shock hysteresis)** is quantified over every shock start
  `∀ x₀shock ∈ Set.Icc 0 1, ∃ N, ...`.

The certificate's stored `C.x₀` / `C.x₀shock` are not consumed. The
pathwise Goal 2′ still requires the myopic basin-preservation
hypothesis `hMyoBasin` (the basin-local rule-comparison theorem
`ruleSanctions_le_of_rule_le_and_upper_monoOn_basin` needs the myopic
path to stay in `B`); when `hMyoBasin` is not economically warranted,
the statewise Goal 2 is the recommended comparison.

Since round BH1.7 (2026-10-06) a one-line alias of
`StandardComplianceLocalCoreCertificate.three_goals_local_regime_comparison_uniform_starts`,
which carries the proof (an instance of the general-`F`
`three_goals_local_regime_comparison_uniform_starts_generalF`). The name sits in
the `StandardComplianceLocalCertificate` namespace but takes a core certificate;
it is kept for its existing citations. -/
theorem three_goals_local_regime_comparison_uniform_starts
    (C : p.StandardComplianceLocalCoreCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (hMyoBasin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.myopicEquilibriumRule C.M x ∈ Set.Icc (max C.xT C.xS) 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      -- Goal 1 (persistence, uniform over basin starts):
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))))
      -- Goal 2 (statewise regime comparison):
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.myopicEquilibriumRule C.M x ≤ p.dynamicEquilibriumRule E x)
      -- Goal 2′ (pathwise regime comparison, uniform over basin starts):
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
           ∀ n, p.ruleSanctions (p.myopicEquilibriumRule C.M) x₀ n
                  ≤ p.ruleSanctions (p.dynamicEquilibriumRule E) x₀ n)
      -- Goal 3 (shock hysteresis, uniform over shock starts):
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPath E.V_S E.α
                    (p.shockPath x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                            (p.shockPath x₀shock N) n) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                    (p.shockPath x₀shock N) n)) :=
  StandardComplianceLocalCoreCertificate.three_goals_local_regime_comparison_uniform_starts
    p C hF hMyoBasin

end StandardComplianceLocalCertificate

namespace StandardComplianceLocalCertificateC1

variable {K_d : ℝ}

/-- **Audit-49 Item 5: carrier-local C¹ statewise three-goals theorem.**

Proof: produce the C¹ fixed point `z : D_C1.carrier` via
`exists_c1distPair_fixedPoint`; lift to the BCF equilibrium `E` via
`feedbackStackelbergEquilibriumTop_of_c1distPair_fixedPoint`; the
produced `E` satisfies `E.V_T = z.val.1.V`, `E.V_S = z.val.2.V`,
`E.α = D_C1.α_on_C1 z.val.1 z.val.2`. Instantiate the carrier-local
primitives at this `z` to get the per-E primitives at `E`, then
apply the same JET-style chain as the existing Core theorem. -/
theorem three_goals_local_C1
    (C : p.StandardComplianceLocalCertificateC1 K_d)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                ∈ Set.Icc (max C.xT C.xS) 1) ∧
       (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
       (∀ n, IsMaxOn
         (fun a => p.joint_T_top_integrand E.V_T E.V_S
                     (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
         Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) := by
  -- Step 1: produce the C¹ fixed point z.
  obtain ⟨z, hfix⟩ :=
    C.D_C1.toValueClass_C1.exists_c1distPair_fixedPoint C.hK_d_nn C.hComplete
  -- Step 2: construct E inline (replicating C1BellmanSystem.lean lines 153-196
  -- so that the E.V_T, E.V_S, E.α field equalities are literal rfl-equalities).
  obtain ⟨hVT_eq, hVS_eq⟩ :=
    C1BellmanSystem.bcf_eq_of_c1distPair_zero C.hK_d_nn hfix
  let V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ := z.val.1.V
  let V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ := z.val.2.V
  let α : ℝ → ℝ := C.D_C1.α_on_C1 z.val.1 z.val.2
  let E : p.FeedbackStackelbergEquilibriumTop :=
    { V_T := V_T
      V_S := V_S
      α := α
      hα := C.D_C1.α_cont z
      α_mem := fun x hx => C.D_C1.α_mem z x hx
      V_S_fix := by
        show V_S = p.bellmanS_BCF α (C.D_C1.α_cont z) V_S
        have h_T_sender :
            (C.D_C1.T z).val.2.V =
              p.bellmanS_BCF α (C.D_C1.α_cont z) V_S :=
          C.D_C1.T_value_eq_sender z
        rw [← h_T_sender, hVS_eq]
      V_T_fix_top := by
        intro x
        have h_T_target := C.D_C1.T_value_eq_target z x
        have h_apply : (C.D_C1.T z).val.1.V x = V_T x := by rw [hVT_eq]
        rw [← h_apply]; exact h_T_target
      α_opt_top := fun x hx => C.D_C1.α_isMaxOn z x hx }
  -- E's fields reduce by rfl since E is a structure literal.
  have hE_VT : E.V_T = z.val.1.V := rfl
  have hE_VS : E.V_S = z.val.2.V := rfl
  have hE_α : E.α = C.D_C1.α_on_C1 z.val.1 z.val.2 := rfl
  -- Step 2: derive per-E primitives at E by rewriting carrier-local primitives
  -- with the rfl-equalities above.
  have h_stage_target_loss :
      ∀ x ∈ Set.Icc C.xT (1 : ℝ),
        LowerLossSlopeOn (fun s => p.U_T x (E.α x) s)
          (Set.Icc (max x C.sbar) 1) C.cT := by
    intro x hx
    rw [hE_α]
    exact C.h_stage_target_loss_carrier z x hx
  have hV_T_gain : LowerSlopeOnValueOn E.V_T (Set.Icc C.xT 1) C.gT := by
    rw [hE_VT]
    exact C.hV_T_gain_on_carrier z
  have hV_S_lip : ValueLipschitzWith E.V_S C.KS := by
    rw [hE_VS]
    exact C.hV_S_lip_carrier z
  have h_stage_sender :
      ∀ x ∈ Set.Icc C.xS (1 : ℝ),
        LowerSlopeOn
          (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x C.sbar)) C.mS := by
    intro x hx
    rw [hE_α]
    exact C.h_stage_sender_carrier z x hx
  have hSC :
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc (max C.xT C.xS) 1)
        (fun s x => p.senderDynObjective E.V_S x (E.α x) s) := by
    -- E.V_S and E.α reduce by rfl to z.val.2.V and D_C1.α_on_C1 z.val.1 z.val.2,
    -- so the SC predicate at E.V_S, E.α equals the carrier-local SC at z.
    exact C.hSC_carrier z
  -- Step 3: apply per-E bridges.
  have hGoal1 :=
    p.persistence_at_equilibriumTop_from_lossOffset_on E hF
      C.hxT_mem C.hxS_mem C.hsbar_mem C.hKS_nonneg C.hS_margin
      hV_S_lip h_stage_target_loss hV_T_gain
      C.hT_loss_margin h_stage_sender
      (Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn hSC)
      C.hx₀
  have hFloor : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
      max x C.sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x := by
    have hOne : p.OneSidedSanctionPreferenceThresholds
                  E.V_T E.V_S E.α C.xT C.xS C.sbar :=
      OneSidedSanctionPreferenceThresholds.of_stage_lowerSlopes_compliance_target_on
        p hF C.hxT_mem C.hxS_mem C.hsbar_mem C.hKS_nonneg C.hS_margin
        hV_S_lip h_stage_target_loss hV_T_gain
        C.hT_loss_margin h_stage_sender
    have hTopMono :
        MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
          (Set.Icc (max C.xT C.xS) 1) :=
      p.dynamicTopRealizedRule_mono_of_singleCrossingOn hSC
    have hα_feas : ∀ x ∈ Set.Icc (max C.xT C.xS) 1, E.α x ∈ Sanctions.I := by
      intro x hx
      apply E.α_mem
      refine ⟨?_, hx.2⟩
      exact le_trans (le_max_of_le_left C.hxT_mem.1) hx.1
    have hα_opt : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        IsMaxOn (fun a => p.joint_T_top_integrand E.V_T E.V_S x a)
          Sanctions.I (E.α x) := by
      intro x hx
      apply E.α_opt_top
      refine ⟨?_, hx.2⟩
      exact le_trans (le_max_of_le_left C.hxT_mem.1) hx.1
    have hB := JointPreferenceBasinTop.of_oneSidedThresholds p hOne hα_feas hTopMono hα_opt
    exact JointPreferenceBasinTop.level_dyn_top p hB
  have hGoal2 :=
    p.ruleDom_of_dynamic_floor_and_myopic_ceiling hFloor C.hMyoCeiling
  have hGoal3 :=
    p.shock_at_equilibriumTop_from_lossOffset_on E hF
      C.hxT_mem C.hxS_mem C.hsbar_mem C.hsbar_pos C.hjoint_lt
      C.hKS_nonneg C.hS_margin hV_S_lip
      h_stage_target_loss hV_T_gain C.hT_loss_margin
      h_stage_sender
      (Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn hSC)
      C.hx₀shock_nn C.hx₀shock_le
  obtain ⟨N, h1, h2, h3, _h4, _h5, _h6⟩ := hGoal3
  exact ⟨E, hGoal1, hGoal2, N, h1, h2, h3⟩

end StandardComplianceLocalCertificateC1

/-- **Preferred BCF theorem (audit-49 follow-up).** Asymmetric
carrier-local route using `StandardComplianceLocalCertificate`
(built on `ValueClass2` with separate `carrier_T` / `carrier_S`).
One-line delegation to
`StandardComplianceLocalCertificate.three_goals_local`. -/
theorem standardCompliance_three_goals_local
    (C : p.StandardComplianceLocalCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
         (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) := by
  -- Project the per-path Bellman-optimality conjunct out of the
  -- 5-conjunct certificate output. Issue 9 of the 2026-06-07 JET
  -- referee response: clause (iv) is a definitional consequence of
  -- (E3) (the feedback Stackelberg equilibrium concept), not a
  -- substantive theorem conclusion. The fat 5-conjunct form remains
  -- available as `standardCompliance_three_goals_local_with_path_optimality`.
  obtain ⟨E, hVT, hVS, ⟨hInv, hSbar, hxBar, hMono, _hIsMax⟩, hG2, hG3⟩ :=
    StandardComplianceLocalCertificate.three_goals_local p C hF
  exact ⟨E, hVT, hVS, ⟨hInv, hSbar, hxBar, hMono⟩, hG2, hG3⟩

/-- **Backward-compatibility alias retaining clause (iv).** Reverts to
the 5-conjunct persistence form (i.e.\ the pre-Round-1 shape), with
the per-path `IsMaxOn` Bellman-optimality conjunct restored. The
restored conjunct is *not* a substantive theorem conclusion — it is a
definitional consequence of the feedback Stackelberg equilibrium
concept (E3) — but the alias is provided for backward-compatibility
with code written against the pre-Round-1 paper draft. -/
theorem standardCompliance_three_goals_local_with_path_optimality
    (C : p.StandardComplianceLocalCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
         (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
         (∀ n, IsMaxOn
           (fun a => p.joint_T_top_integrand E.V_T E.V_S
                       (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
           Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) :=
  StandardComplianceLocalCertificate.three_goals_local p C hF

/-- **Uniform-starts preferred BCF theorem (2026-06-01).**
Same as `standardCompliance_three_goals_local`, but the path-level
conclusions are quantified **universally** over starting states:

* Goal 1 (persistence) is quantified
  `∀ x₀ ∈ Set.Icc (max xT xS) 1, ...`.
* Goal 2 (statewise dominance) is already start-independent.
* Goal 3 (shock hysteresis) is quantified
  `∀ x₀shock ∈ Set.Icc 0 1, ∃ N, ...`.

This matches the manuscript's "for every starting state `x₀ ∈ B`"
(Proposition 1) and "for every initial state `x₀ ∈ [0, 1]`"
(Proposition 3) wording. The equilibrium `E` is constructed once
from the certificate's value-class / contraction / uniqueness
machinery (which is start-independent); the user supplies any
valid starting state at the consumption site.

One-line delegation to
`StandardComplianceLocalCoreCertificate.three_goals_local_uniform_starts`. -/
theorem standardCompliance_three_goals_local_uniform_starts
    (C : p.StandardComplianceLocalCoreCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPath E.V_S E.α
                    (p.shockPath x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                            (p.shockPath x₀shock N) n) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                    (p.shockPath x₀shock N) n)) :=
  StandardComplianceLocalCoreCertificate.three_goals_local_uniform_starts p C hF

/-- **Regime-comparison preferred BCF theorem (2026-06-01).**

Pathwise comparison between the fully forward-looking feedback
Stackelberg equilibrium and the fully myopic feedback equilibrium.
Returns the standard three goals PLUS, in place of the bare
statewise Goal-2, a pair of conclusions:

* **Goal 2 (statewise regime comparison):** on the high basin,
  `p.myopicEquilibriumRule C.M x ≤ p.dynamicEquilibriumRule E x`.
* **Goal 2' (pathwise regime comparison):** starting from `C.x₀`,
  the sanction sequence under the fully myopic equilibrium rule is
  pointwise dominated by the sanction sequence under the fully
  forward-looking equilibrium rule:
  `p.ruleSanctions (p.myopicEquilibriumRule C.M) C.x₀ n
     ≤ p.ruleSanctions (p.dynamicEquilibriumRule E) C.x₀ n` for every `n`.

The pathwise comparison requires one new hypothesis beyond the
standard-compliance certificate: **myopic basin preservation**

  `hMyoBasin : ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
                p.myopicEquilibriumRule C.M x ∈ Set.Icc (max C.xT C.xS) 1`.

This says the fully myopic regime's realized sanction stays in the
high basin from any basin state. Without it, the myopic path can
exit the basin and the basin-local comparison theorem
`ruleSanctions_le_of_rule_le_and_upper_monoOn_basin` does not apply
forever; callers should then fall back to the bare statewise
`standardCompliance_three_goals_local_uniform_starts` (or, if a
fixed start is what is wanted, `standardCompliance_three_goals_local`).

One-line delegation to
`StandardComplianceLocalCertificate.three_goals_local_regime_comparison`, itself
an instance of the general-`F` fixed-start
`StandardComplianceLocalCertificate.three_goals_local_regime_comparison_generalF`
since round BH1.7. Affine-restricted by its `hF` binder. The general-`F`
statement of the comparison alone (round BH1.4, 2026-10-06), from the core
certificate and `hMyoBasin` only, uniform over basin starts and with neither
`hF` nor `hAdj`, is
`StandardComplianceLocalCoreCertificate.pathwise_dominance_generalF`. -/
theorem standardCompliance_three_goals_local_regime_comparison
    (C : p.StandardComplianceLocalCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (hMyoBasin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.myopicEquilibriumRule C.M x ∈ Set.Icc (max C.xT C.xS) 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
         (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
         (∀ n, IsMaxOn
           (fun a => p.joint_T_top_integrand E.V_T E.V_S
                       (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
           Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.myopicEquilibriumRule C.M x ≤ p.dynamicEquilibriumRule E x)
      ∧ (∀ n, p.ruleSanctions (p.myopicEquilibriumRule C.M) C.x₀ n
                ≤ p.ruleSanctions (p.dynamicEquilibriumRule E) C.x₀ n)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) :=
  StandardComplianceLocalCertificate.three_goals_local_regime_comparison p C hF hMyoBasin

/-- **Uniform-starts regime-comparison preferred BCF theorem (2026-06-01).**

Universal-start version of
`standardCompliance_three_goals_local_regime_comparison`: Goal 1
(persistence) and Goal 3 (shock hysteresis) are quantified over every
basin start `x₀ ∈ Set.Icc (max xT xS) 1` and every shock start
`x₀shock ∈ Set.Icc 0 1`, and the pathwise Goal 2′ dynamic-over-myopic
comparison is quantified over every basin start. Requires the same
myopic basin-preservation hypothesis `hMyoBasin` as the fixed-start
form; the unconditional statewise Goal 2 remains the recommended
comparison when `hMyoBasin` is not economically warranted.

One-line delegation to
`StandardComplianceLocalCoreCertificate.three_goals_local_regime_comparison_uniform_starts`. -/
theorem standardCompliance_three_goals_local_regime_comparison_uniform_starts
    (C : p.StandardComplianceLocalCoreCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (hMyoBasin :
      ∀ x ∈ Set.Icc (max C.xT C.xS) 1,
        p.myopicEquilibriumRule C.M x ∈ Set.Icc (max C.xT C.xS) 1) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.myopicEquilibriumRule C.M x ≤ p.dynamicEquilibriumRule E x)
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
           ∀ n, p.ruleSanctions (p.myopicEquilibriumRule C.M) x₀ n
                  ≤ p.ruleSanctions (p.dynamicEquilibriumRule E) x₀ n)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPath E.V_S E.α
                    (p.shockPath x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                            (p.shockPath x₀shock N) n) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                    (p.shockPath x₀shock N) n)) :=
  StandardComplianceLocalCoreCertificate.three_goals_local_regime_comparison_uniform_starts
    p C hF hMyoBasin

/-- **Preferred C¹ theorem (audit-49 follow-up).** Carrier-local
C¹ route using `StandardComplianceLocalCertificateC1`. The C¹ track
localizes assumptions to `D_C1.carrier` (the single carrier of the
underlying `C1BellmanSystem`), but it remains single-carrier on the
C¹ side; an asymmetric `ValueClass2_C1` analogue is not yet
available (the C¹ Banach pipeline iter-15..21 would need to be
duplicated to support heterogeneous C¹ carriers). The BCF preferred
route `standardCompliance_three_goals_local_uniform_starts` above
is fully asymmetric. One-line delegation to
`StandardComplianceLocalCertificateC1.three_goals_local_C1`. -/
theorem standardCompliance_three_goals_local_C1
    {K_d : ℝ} (C : p.StandardComplianceLocalCertificateC1 K_d)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                ∈ Set.Icc (max C.xT C.xS) 1) ∧
       (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
       (∀ n, IsMaxOn
         (fun a => p.joint_T_top_integrand E.V_T E.V_S
                     (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
         Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) :=
  StandardComplianceLocalCertificateC1.three_goals_local_C1 p C hF

/-! ## Audit-49 Phase A-F Item-12: ordinary-equilibrium-facing wrapper

The two preferred theorems above return an upper-selector equilibrium
`E : p.FeedbackStackelbergEquilibriumTop`. The ordinary-equilibrium
object `p.FeedbackStackelbergEquilibrium` (using `σ_dyn` instead of
`σ_dyn_top`) is the natural JET-reader expectation; the bridge
`FeedbackStackelbergEquilibrium.toTop_of_unique` proves these
coincide on the regular value class (where `DynamicArgmaxUnique V_S`
holds). The wrapper below foregrounds the ordinary form by returning
the ordinary `E` plus its Sender-uniqueness certificate, compliance-local
(`DynamicArgmaxUniqueOnI E.V_S`) since round BJ4.3; the `_of_senderUnique`
sibling returns the full `DynamicArgmaxUnique E.V_S` form. -/

/-- **Audit-49 follow-up Round 3 Optional-4.3: three-goals wrapper
with selector-equivalence bridge.**

Pragmatic wrapper for JET-paper-facing presentation:

1. Extracts the produced top equilibrium `E_top` and the three goals
   from `standardCompliance_three_goals_local` (the fixed-start
   compatibility theorem; the universal-start preferred form is
   `standardCompliance_three_goals_local_uniform_starts`).
2. Witnesses `p.DynamicArgmaxUnique E_top.V_S` via the certificate's
   `sender_unique_on` field at the carrier-local `E_top.V_S`. Under
   uniqueness, the upper selector `σ_dyn_top E_top.V_S` coincides
   pointwise with the ordinary classical-choice-based dynamic Sender
   response `σ_dyn E_top.V_S` (the equality lemma is
   `σ_dyn_eq_σ_dyn_top_of_unique`).
3. Returns the three goals at `E_top` (stated in top-rule form
   because the monotone-comparative-statics argument naturally
   lives there), bundled with the pointwise `σ_dyn = σ_dyn_top`
   bridge — downstream callers can convert any of the three-goal
   conclusions to the ordinary-rule form by pointwise rewriting.

Renamed from `standardCompliance_three_goals_local_ordinary` in
audit-49 follow-up Round 4 because the previous name suggested the
returned equilibrium was an *ordinary*
`FeedbackStackelbergEquilibrium` object, when in fact it is a
top-selector `FeedbackStackelbergEquilibriumTop` bundled with the
pointwise equivalence. A pure-ordinary-rule version of the three
goals would require new induction lemmas
(`dynamicLockInPath = dynamicTopLockInPath` under uniqueness etc.);
those are not yet in the codebase and are deferred.

**Weakened conclusion (plan item BJ4.3, 2026-10-08).** The certificate's value
class now carries Sender uniqueness only at physical compliance levels
(`ValueClass2.sender_unique_on : … DynamicArgmaxUniqueOnI`), so the returned
uniqueness certificate is `DynamicArgmaxUniqueOnI E.V_S` and the selector bridge
holds for `a ∈ I` (formerly `DynamicArgmaxUnique E.V_S` and every real `a`).
The realized path evaluates the Sender's response only at the equilibrium
compliance `E.α x ∈ I`, so the pointwise rewriting above is unaffected. With
full uniqueness on the Sender carrier as an extra input the former conclusion
is `standardCompliance_three_goals_local_with_selector_equivalence_of_senderUnique`.
Affine-restricted (`hF`). -/
theorem standardCompliance_three_goals_local_with_selector_equivalence
    (C : p.StandardComplianceLocalCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ p.DynamicArgmaxUniqueOnI E.V_S
      ∧ (∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
          p.σ_dyn E.V_S x a = p.σ_dyn_top E.V_S x a)
      ∧ ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
         (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
         (∀ n, IsMaxOn
           (fun a => p.joint_T_top_integrand E.V_T E.V_S
                       (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
           Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) := by
  -- Extract E_top + the three goals from the backward-compatibility
  -- 5-conjunct form (this consumer's return type still publishes the
  -- per-path Bellman-optimality clause for back-compat with the
  -- pre-Round-1 paper draft; the slim 4-conjunct version is in
  -- `standardCompliance_three_goals_local`).
  obtain ⟨E, hVT, hVS, hG1, hG2, N, h1, h2, h3⟩ :=
    p.standardCompliance_three_goals_local_with_path_optimality C hF
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
  exact ⟨E, hVT, hVS, hUnique, hσ_eq, hG1, hG2, N, h1, h2, h3⟩

/-- **Three-goals wrapper with selector-equivalence bridge and full Sender
uniqueness (plan item BJ4.3, 2026-10-08).** The pre-BJ4.3 conclusion of
`standardCompliance_three_goals_local_with_selector_equivalence` (Sender
uniqueness and the `σ_dyn = σ_dyn_top` bridge at every real compliance level),
for a certificate whose Sender carrier also satisfies `DynamicArgmaxUnique`
(`hU`). Before round BJ4.3 the value class carried `hU` itself; it now carries
only the compliance-local part, so `hU` is an explicit input here and nothing
is lost. Affine-restricted (`hF`). -/
theorem standardCompliance_three_goals_local_with_selector_equivalence_of_senderUnique
    (C : p.StandardComplianceLocalCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (hU : ∀ V_S ∈ C.D.carrier_S, p.DynamicArgmaxUnique V_S) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ p.DynamicArgmaxUnique E.V_S
      ∧ (∀ x ∈ Sanctions.S, ∀ a, p.σ_dyn E.V_S x a = p.σ_dyn_top E.V_S x a)
      ∧ ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
         (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
         Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
         (∀ n, IsMaxOn
           (fun a => p.joint_T_top_integrand E.V_T E.V_S
                       (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
           Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) := by
  obtain ⟨E, hVT, hVS, _, _, hG1, hG2, N, h1, h2, h3⟩ :=
    p.standardCompliance_three_goals_local_with_selector_equivalence C hF
  have hUnique : p.DynamicArgmaxUnique E.V_S := hU E.V_S hVS
  have hσ_eq : ∀ x ∈ Sanctions.S, ∀ a,
      p.σ_dyn E.V_S x a = p.σ_dyn_top E.V_S x a := fun x hx a =>
    p.σ_dyn_eq_σ_dyn_top_of_unique E.V_S x a (hUnique x hx a)
  exact ⟨E, hVT, hVS, hUnique, hσ_eq, hG1, hG2, N, h1, h2, h3⟩

/-- **Audit-49 follow-up Round 3 Optional-4.4: weak-persistence
local theorem (paper-facing wrapper).** Weaker-conclusion sibling of
`standardCompliance_three_goals_local` — drops the strong-ratchet
sanction floors and `Monotone` conjunct, keeping only basin
invariance, statewise Goal-2 dominance, and post-shock basin
invariance. One-line delegation to
`StandardComplianceLocalCertificate.three_goals_local_weak_persistence`. -/
theorem standardCompliance_three_goals_local_weak_persistence
    (C : p.StandardComplianceLocalCertificate)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                ∈ Set.Icc (max C.xT C.xS) 1)
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          ∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                ∈ Set.Icc (max C.xT C.xS) 1 :=
  StandardComplianceLocalCertificate.three_goals_local_weak_persistence p C hF

/-- **Audit-47 homogeneous main theorem (C¹ route).** From a
`StandardComplianceCertificateC1` under literal compliance, produce
a top-selector feedback Stackelberg equilibrium satisfying the
three goals (statewise form). Homogeneous compatibility theorem;
**preferred** form is `standardCompliance_three_goals_local_C1`
(carrier-local, defined above). One-line delegation to
`StandardComplianceCertificateC1.three_goals` (= audit-46
C¹ `three_goals_statewise`). -/
theorem standardCompliance_three_goals_C1
    {K_d : ℝ} (C : p.StandardComplianceCertificateC1 K_d)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ((∀ n, p.dynamicTopLockInPath E.V_S E.α C.x₀ n
                ∈ Set.Icc (max C.xT C.xS) 1) ∧
       (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α C.x₀ n) ∧
       Monotone (p.dynamicTopLockInSanctions E.V_S E.α C.x₀) ∧
       (∀ n, IsMaxOn
         (fun a => p.joint_T_top_integrand E.V_T E.V_S
                     (p.dynamicTopLockInPath E.V_S E.α C.x₀ n) a)
         Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α C.x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ ∃ N : ℕ,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath C.x₀shock N) n
                  ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                          (p.shockPath C.x₀shock N) n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                  (p.shockPath C.x₀shock N) n) :=
  StandardComplianceCertificateC1.three_goals p C hF

/-! ## Retired 2026-08-21: the homogeneous-certificate aliases

`standardCompliance_three_goals` and `standardCompliance_three_goals_pathwise`
stood here as the paper-facing wrappers of the `RegularEconomyCertificateCompliance`
tower, retired the same day as strictly dominated by the carrier-local route
(see the note in `Theory/Certificates/RegularEconomy.lean`).

The paper's pathwise-dominance corollary cited both this wrapper and
`standardCompliance_three_goals_local_regime_comparison`. The latter delivers the
same comparison — `ruleSanctions (myopicEquilibriumRule M)` is definitionally the
sequence the retired one compared — over **all** basin starts rather than one
stored initial state, and unlike the retired route it has five witnesses. The
formalization map now cites it alone. -/

/-- **Stage-flip alternative constructor for the carrier-local
compliance certificate.** Derives the basin geometry from the Round-A
primitives:

* `xT := targetFlipPivot s̄`, `xS := senderFlipPivot s̄ m_S` — the
  certificate locations are the derived tipping thresholds;
* the Sender stage-slope field is derived from the floor flip set
  (uniform in the action, evaluated at the Bellman-derived
  `D.α_on`) glued with the above-floor diagonal residual.

Affine-restricted (it carries `hF`). Round BJ1.4 (2026-10-07): the certificate
no longer has a Target loss-offset block, so the constructor no longer derives
one (`c_T := 0`, `g_T := 0` from the Target flip and carrier monotonicity) and
drops the two inputs that only fed it, `0 < s̄` and the monotonicity of the
Target carrier on the basin range.

Retained verbatim (not consequences of stage supermodularity): the
heterogeneous row-contraction block, the carrier Sender-Lipschitz
field, the carrier-local single-crossing field `hSC_on`, and the
myopic comparator + ceiling. -/
noncomputable def StandardComplianceLocalCoreCertificate.of_stage_flip
    (D : p.ValueClass2) (h_inv : D.IsInvariant)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1) (hsuff_S : β_S + L_ST < 1)
    {sbar mS KS : ℝ}
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS) (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip_carrier : ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S KS)
    (hID_T : p.TargetStageID) (hID_S : p.SenderStageID)
    (h1_T : (1 : ℝ) ∈ p.targetFlipSet sbar)
    (h1_S : (1 : ℝ) ∈ p.senderFloorFlipSet sbar mS)
    (hjoint_lt :
      max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS) < 1)
    (h_diag : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc (p.senderFlipPivot sbar mS) (1 : ℝ), sbar < x →
        LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc sbar x) mS)
    (hSC_on : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I
        (Set.Icc
          (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s))
    (M : p.MyopicFeedbackEquilibrium)
    (hMyoCeiling : ∀ x ∈ Set.Icc
        (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
      p.σ x (M.α x) ≤ max x sbar) :
    p.StandardComplianceLocalCoreCertificate where
  D := D
  h_inv := h_inv
  β_T := β_T
  β_S := β_S
  L_TS := L_TS
  L_ST := L_ST
  hβ_T_nn := hβ_T_nn
  hβ_S_nn := hβ_S_nn
  hL_TS_nn := hL_TS_nn
  hL_ST_nn := hL_ST_nn
  hT_T_op := hT_T_op
  hT_S_op := hT_S_op
  hsuff_T := hsuff_T
  hsuff_S := hsuff_S
  xT := p.targetFlipPivot sbar
  xS := p.senderFlipPivot sbar mS
  sbar := sbar
  mS := mS
  KS := KS
  hxT_mem := p.targetFlipPivot_mem_I hID_T hsbar_mem h1_T
  hxS_mem := p.senderFlipPivot_mem_I hID_S hsbar_mem h1_S
  hsbar_mem := hsbar_mem
  d := p.δ
  hF_chord := by
    intro x _ s₁ _ s₂ _ hs
    have hval : p.F x s₂ - p.F x s₁ = p.δ * (s₂ - s₁) := by
      rw [hF]; unfold Sanctions.AbstractGame.affineF; ring
    rw [hval]
    exact le_of_eq (abs_of_nonneg
      (mul_nonneg (le_of_lt p.δ_mem.1) (by linarith)))
  hS_margin := hS_margin
  hjoint_lt := hjoint_lt
  hV_S_lip_carrier := hV_S_lip_carrier
  h_stage_sender_on := by
    intro V_T V_S x hx
    have hxmem : x ∈ p.senderFloorFlipSet sbar mS := by
      rw [p.senderFloorFlipSet_eq_Icc hID_S hsbar_mem h1_S]
      exact hx
    have hfloor : LowerSlopeOn
        (fun s => p.U_S x (D.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) sbar) mS :=
      fun s₁ hs₁ s₂ hs₂ hs =>
        hxmem.2 (D.α_on V_T V_S x) (D.α_on_mem V_T V_S x)
          s₁ hs₁ s₂ hs₂ hs
    rcases le_or_gt x sbar with hxs | hxs
    · rw [max_eq_right hxs]
      exact hfloor
    · rw [max_eq_left (le_of_lt hxs)]
      exact lowerSlopeOn_glue_Icc hsbar_mem.1 (le_of_lt hxs) hfloor
        (h_diag V_T V_S x hx hxs)
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (hSC_on V_T V_S)
  M := M
  hMyoCeiling := hMyoCeiling

/-! ## 3. Headline wrapper: three goals from the stage flip -/

/-- **Three goals from stage supermodularity (headline wrapper).**
Composes the stage-flip certificate constructor with the existing
universal-starts headline
`standardCompliance_three_goals_local_uniform_starts`. The conclusion
is the standard three-goals package at the **derived** basin
`[max(x̄_T, x̂_S), 1]`, where `x̄_T := targetFlipPivot s̄` and
`x̂_S := senderFlipPivot s̄ m_S` are the tipping thresholds extracted
from the two stage-complementarity primitives:

* **Goal 1** — from any start in the derived basin, the equilibrium
  state path stays in the basin, realized sanctions are bounded below
  by `s̄` and by the basin pivot, the sanction sequence is
  non-decreasing, and the Target policy is Bellman-optimal along the
  path;
* **Goal 2** — on the derived basin, the myopic equilibrium sanction
  is dominated by the dynamic equilibrium sanction;
* **Goal 3** — from any feasible start, a finite high-sanction shock
  drives the state into the derived basin, after which Goal-1
  conclusions apply.

Affine-restricted (it carries `hF`). Round BJ1.4 (2026-10-07): the inputs
`0 < s̄` and the monotonicity of the Target carrier on the basin range are
dropped with the certificate's Target loss-offset block, which was all they
fed. -/
theorem standardCompliance_three_goals_from_stage_flip
    (D : p.ValueClass2) (h_inv : D.IsInvariant)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1) (hsuff_S : β_S + L_ST < 1)
    {sbar mS KS : ℝ}
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS) (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip_carrier : ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S KS)
    (hID_T : p.TargetStageID) (hID_S : p.SenderStageID)
    (h1_T : (1 : ℝ) ∈ p.targetFlipSet sbar)
    (h1_S : (1 : ℝ) ∈ p.senderFloorFlipSet sbar mS)
    (hjoint_lt :
      max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS) < 1)
    (h_diag : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc (p.senderFlipPivot sbar mS) (1 : ℝ), sbar < x →
        LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc sbar x) mS)
    (hSC_on : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I
        (Set.Icc
          (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s))
    (M : p.MyopicFeedbackEquilibrium)
    (hMyoCeiling : ∀ x ∈ Set.Icc
        (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
      p.σ x (M.α x) ≤ max x sbar) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ D.carrier_T
      ∧ E.V_S ∈ D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc
            (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                  ∈ Set.Icc (max (p.targetFlipPivot sbar)
                              (p.senderFlipPivot sbar mS)) 1) ∧
          (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          (∀ n, max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)
                  ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc
            (max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)) 1,
           p.σ x (M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPath E.V_S E.α
                    (p.shockPath x₀shock N) n
                    ∈ Set.Icc (max (p.targetFlipPivot sbar)
                                (p.senderFlipPivot sbar mS)) 1) ∧
            (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                            (p.shockPath x₀shock N) n) ∧
            (∀ n, max (p.targetFlipPivot sbar) (p.senderFlipPivot sbar mS)
                    ≤ p.dynamicTopLockInSanctions E.V_S E.α
                        (p.shockPath x₀shock N) n)) :=
  standardCompliance_three_goals_local_uniform_starts p
    (StandardComplianceLocalCoreCertificate.of_stage_flip p D h_inv hF
      hβ_T_nn hβ_S_nn hL_TS_nn hL_ST_nn hT_T_op hT_S_op hsuff_T hsuff_S
      hsbar_mem hKS_nonneg hS_margin hV_S_lip_carrier
      hID_T hID_S h1_T h1_S hjoint_lt h_diag
      hSC_on M hMyoCeiling) hF

/-! ## 3b. General-`F` route: MS certificate and headline from the
stage flip (Round R-GF)

The constructor above feeds the **affine** headline (its wrapper takes
`hF : p.F = affineF p.δ`). The general-`F` headline
`standardCompliance_three_goals_local_MS_generalF` consumes the
**MS-form** certificate instead, whose Target block is the ordinal
combined chord `TargetCombinedChordOn` rather than the affine
loss-offset decomposition. The key observation — the paper's "on the
derived basin, the Target assumption is a *theorem*" — is that the
combined chord is dischargeable from the stage flip for **any**
monotone transition: above the Target flip pivot the stage chord is
non-negative by flip-set membership, and the continuation chord is
non-negative because `s ≥ x` keeps `F(x,s) ≥ F(x,x) = x` in the basin
range (`F_diag` + `F_mono_s`) where carrier `V_T` is monotone. No
affine structure is used anywhere. -/

/-- **The greatest next-state selector is monotone per fixed action
(Round B3).** In next-state coordinates `y = (1−δ)x + δs` the
continuation cancels from every chord comparison; `SenderStageID`
plus weak chord concavity of `U_S` in `s` then give increasing
differences of the transformed stage term on the ascending feasible
intervals, and the constrained Topkis selection applies.

⚠ AFFINE-SCOPED ORPHAN (2026-07-07 audit): both the hypothesis `hF`
and the conclusion (stated in affine next-state coordinates) are
specific to the affine law, and the lemma has no consumer — the
general-F stage-flip headline route does not need it. Retained as an
affine-instance convenience; a parametric restatement on
`fun x => p.F x (p.σ_dyn_top V_S x a)` would need the chord-
cancellation trick redone for concave sections of a general `F`. -/
theorem nextStateTop_mono_of_stageID_chordConcave
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hID : p.SenderStageID) (hcc : p.SenderChordConcaveInS) :
    MonotoneOn (fun x => (1 - p.δ) * x + p.δ * p.σ_dyn_top V_S x a)
      Sanctions.I := by
  intro x hx x' hx' hxx'
  have hδ : (0 : ℝ) < p.δ := p.δ_mem.1
  have hδ' : p.δ ≠ 0 := ne_of_gt hδ
  have h1δ : (0 : ℝ) ≤ 1 - p.δ := by linarith [p.δ_mem.2]
  -- The next-state objective: continuation depends on the choice alone.
  set F : ℝ → ℝ → ℝ := fun y t =>
    p.U_S t a ((y - (1 - p.δ) * t) / p.δ)
      + p.β_S * V_S (Sanctions.clipS' y) with hF_def
  -- Feasibility of the candidate points.
  have hyσ : ∀ t : ℝ,
      (1 - p.δ) * t + p.δ * p.σ_dyn_top V_S t a
        ∈ Set.Icc ((1 - p.δ) * t) ((1 - p.δ) * t + p.δ) := by
    intro t
    have hσ := p.σ_dyn_top_mem_I V_S t a
    constructor
    · nlinarith [hσ.1]
    · nlinarith [hσ.2]
  -- The s-coordinate of a feasible y at parameter t lies in [0, 1].
  have hs_mem : ∀ t z : ℝ,
      z ∈ Set.Icc ((1 - p.δ) * t) ((1 - p.δ) * t + p.δ) →
      (z - (1 - p.δ) * t) / p.δ ∈ Sanctions.I := by
    intro t z hz
    constructor
    · apply div_nonneg _ hδ.le
      linarith [hz.1]
    · rw [div_le_one hδ]
      linarith [hz.2]
  -- y-maximality of the σ_top image, at any parameter t.
  have hmax_t : ∀ t : ℝ,
      ∀ z ∈ Set.Icc ((1 - p.δ) * t) ((1 - p.δ) * t + p.δ),
        F z t ≤ F ((1 - p.δ) * t + p.δ * p.σ_dyn_top V_S t a) t := by
    intro t z hz
    have hs := hs_mem t z hz
    have hmax := p.σ_dyn_top_isMaxOn V_S t a hs
    simp only [hF, Sanctions.AbstractGame.affineF] at hmax
    -- rewrite both sides into s-coordinates
    have hz_eq : (1 - p.δ) * t + p.δ * ((z - (1 - p.δ) * t) / p.δ) = z := by
      field_simp
      ring
    have hσ_eq : ((1 - p.δ) * t + p.δ * p.σ_dyn_top V_S t a
        - (1 - p.δ) * t) / p.δ = p.σ_dyn_top V_S t a := by
      field_simp
      ring
    simp only [hF_def, hσ_eq]
    calc p.U_S t a ((z - (1 - p.δ) * t) / p.δ)
          + p.β_S * V_S (Sanctions.clipS' z)
        = p.U_S t a ((z - (1 - p.δ) * t) / p.δ)
          + p.β_S * V_S (Sanctions.clipS'
              ((1 - p.δ) * t + p.δ * ((z - (1 - p.δ) * t) / p.δ))) := by
          rw [hz_eq]
      _ ≤ p.U_S t a (p.σ_dyn_top V_S t a)
          + p.β_S * V_S (Sanctions.clipS'
              ((1 - p.δ) * t + p.δ * p.σ_dyn_top V_S t a)) := hmax
  -- Greatest property at x': any y-maximizer at x' is ≤ the σ_top image.
  have hgreatest : ∀ z ∈ Set.Icc ((1 - p.δ) * x') ((1 - p.δ) * x' + p.δ),
      (∀ w ∈ Set.Icc ((1 - p.δ) * x') ((1 - p.δ) * x' + p.δ),
        F w x' ≤ F z x') →
      z ≤ (1 - p.δ) * x' + p.δ * p.σ_dyn_top V_S x' a := by
    intro z hz hzmax
    set sz := (z - (1 - p.δ) * x') / p.δ with hsz_def
    have hszI := hs_mem x' z hz
    have hz_eq : (1 - p.δ) * x' + p.δ * sz = z := by
      simp only [hsz_def]
      field_simp
      ring
    -- sz is an s-maximizer at x'.
    have hsz_max : sz ∈ p.dynamicArgmaxSet V_S x' a := by
      refine ⟨hszI, ?_⟩
      simp only [hF, Sanctions.AbstractGame.affineF]
      intro w hw
      have hwz : (1 - p.δ) * x' + p.δ * w
          ∈ Set.Icc ((1 - p.δ) * x') ((1 - p.δ) * x' + p.δ) := by
        constructor
        · nlinarith [hw.1]
        · nlinarith [hw.2]
      have h := hzmax _ hwz
      have hw_eq : ((1 - p.δ) * x' + p.δ * w - (1 - p.δ) * x') / p.δ = w := by
        field_simp
        ring
      simp only [hF_def, hw_eq] at h
      calc p.U_S x' a w + p.β_S * V_S (Sanctions.clipS'
              ((1 - p.δ) * x' + p.δ * w))
          ≤ p.U_S x' a sz + p.β_S * V_S (Sanctions.clipS' z) := h
        _ = p.U_S x' a sz + p.β_S * V_S (Sanctions.clipS'
              ((1 - p.δ) * x' + p.δ * sz)) := by rw [hz_eq]
    have hle : sz ≤ p.σ_dyn_top V_S x' a :=
      le_csSup (p.dynamicArgmaxSet_bddAbove V_S x' a) hsz_max
    calc z = (1 - p.δ) * x' + p.δ * sz := hz_eq.symm
      _ ≤ (1 - p.δ) * x' + p.δ * p.σ_dyn_top V_S x' a := by nlinarith
  -- ID of F on the overlap: the V_S terms cancel.
  have hIDF : ∀ y₁ y₂ : ℝ,
      y₁ ∈ Set.Icc ((1 - p.δ) * x) ((1 - p.δ) * x + p.δ) →
      y₁ ∈ Set.Icc ((1 - p.δ) * x') ((1 - p.δ) * x' + p.δ) →
      y₂ ∈ Set.Icc ((1 - p.δ) * x) ((1 - p.δ) * x + p.δ) →
      y₂ ∈ Set.Icc ((1 - p.δ) * x') ((1 - p.δ) * x' + p.δ) →
      y₁ ≤ y₂ →
      F y₂ x - F y₁ x ≤ F y₂ x' - F y₁ x' := by
    intro y₁ y₂ h₁x h₁x' h₂x h₂x' h12
    set s₁ := (y₁ - (1 - p.δ) * x) / p.δ with hs₁_def
    set s₂ := (y₂ - (1 - p.δ) * x) / p.δ with hs₂_def
    set c := ((1 - p.δ) / p.δ) * (x' - x) with hc_def
    have hs₁I := hs_mem x y₁ h₁x
    have hs₂I := hs_mem x y₂ h₂x
    have hs12 : s₁ ≤ s₂ := by
      simp only [hs₁_def, hs₂_def, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hδ.le)
      linarith
    have hc_nn : 0 ≤ c := by
      apply mul_nonneg (div_nonneg h1δ hδ.le)
      linarith
    have hs₁c : s₁ - c = (y₁ - (1 - p.δ) * x') / p.δ := by
      simp only [hs₁_def, hc_def]
      field_simp
      ring
    have hs₂c : s₂ - c = (y₂ - (1 - p.δ) * x') / p.δ := by
      simp only [hs₂_def, hc_def]
      field_simp
      ring
    have hs₁c_nn : 0 ≤ s₁ - c := by
      rw [hs₁c]
      apply div_nonneg _ hδ.le
      linarith [h₁x'.1]
    -- F-chords reduce to U_S-chords (V_S cancels).
    have hstage : p.U_S x a s₂ - p.U_S x a s₁
        ≤ p.U_S x' a (s₂ - c) - p.U_S x' a (s₁ - c) := by
      have hIDstep := hID a ha hs₁I hs₂I hs12 hx hx' hxx'
      have hccstep := hcc x' hx' a ha s₁ s₂ c hc_nn hs₁c_nn hs12 hs₂I.2
      linarith
    simp only [hF_def]
    have e₁ : (y₁ - (1 - p.δ) * x) / p.δ = s₁ := rfl
    have e₂ : (y₂ - (1 - p.δ) * x) / p.δ = s₂ := rfl
    have e₁' : (y₁ - (1 - p.δ) * x') / p.δ = s₁ - c := hs₁c.symm
    have e₂' : (y₂ - (1 - p.δ) * x') / p.δ = s₂ - c := hs₂c.symm
    rw [e₁, e₂, e₁', e₂']
    linarith
  -- Assemble via the constrained Topkis selection.
  exact Sanctions.MonotoneThreshold.le_greatestMaxOn_of_ID_ascendingIcc
    (f := F) (u := fun t => (1 - p.δ) * t)
    (v := fun t => (1 - p.δ) * t + p.δ)
    hxx'
    (by nlinarith)
    (by nlinarith)
    (hyσ x) (hyσ x')
    (hmax_t x) hgreatest (hmax_t x')
    hIDF

/-! ## B4 — diagonal residual from the pivot-action frontier -/

/-- **COUNTEREXAMPLE 3 — the corner condition is NOT implied by the strong
basin at an arbitrary `sbar`.** With `sbar = 0` the strong ratchet floor
`max x sbar ≤ s` degenerates to `x ≤ s`, which is satisfiable, while for the
affine transition `F xbar 0 = (1-δ)·xbar < xbar`.

**Scope of this declaration — read the statement, not the name.**  What is
proved below is only the *arithmetic ingredient* of that argument: that `0` is
a feasible floor, that a rule pinned at `1` clears `max x 0` on the interval,
and that the affine corner condition fails at `(1/2, 0)`.  It says nothing
about `JointPreferenceBasinTop`, `IsMaxOn`, or `senderDynObjective`, and it is
therefore **not** by itself a refutation of the containment.

The genuine `Params`-level non-implication — an actual economy carrying a full
`JointPreferenceBasinTop` instance at floor `0` together with the failure of
the corner condition — is
`Sanctions.Examples.weakFloor_corner_not_implied_by_strong_basin`
(`Sanctions/Examples/WeakFloorContainmentCounterexample.lean`).  It lives under
`Examples/` because it needs a witness economy, which this layer may not
import.  Cite that one when the claim being made is the non-implication.

Either way the *hypothesis-free* containment reindexes the floor to
`max xbar sbar` (`WeakFloorBasinTop.of_jointPreferenceBasinTop_reindexed`), so
nothing downstream depends on this declaration. -/
theorem corner_arith_ingredients_at_zero_floor :
    (0:ℝ) ∈ Sanctions.I
    ∧ (∀ x ∈ Set.Icc ((1:ℝ)/2) 1, max x (0:ℝ) ≤ (1:ℝ))
    ∧ ¬ ((1:ℝ)/2 ≤ AbstractGame.affineF (1/5) (1/2) 0) := by
  refine ⟨⟨le_rfl, zero_le_one⟩, ?_, by norm_num [AbstractGame.affineF]⟩
  intro x hx
  have hx0 : (0:ℝ) ≤ x := le_trans (by norm_num) hx.1
  rw [max_eq_left hx0]
  exact hx.2

/-- **The Sender Bellman operator maps the lower-slope cone into itself.**

If the Sender's *stage* payoff along the Target policy `α` has state chord at
least `m` (uniformly in the sanction), the transition is the affine law, and
the cone constant `g` satisfies the sub-solution inequality
`g ≤ m + β_S·g·(1 − δ)`, then `bellmanS_BCF` carries
`{V | V's state chord is at least g}` into itself.

The argument is pointwise-in-`s` and then passes to the `sSup` over feasible
sanctions through `sSup_image_sub_sSup_image_lowerBound_of_pointwise`
(`Foundations/StokeyLucas.lean`): the stage chord contributes `m`, the
continuation chord contributes `β_S·g·(1−δ)` because the affine transition
carries a `(1−δ)` fraction of the state forward, and the sub-solution
inequality says their sum covers `g`. -/
theorem bellmanS_BCF_preserves_lowerSlopeCone
    {α : ℝ → ℝ} (hα : Continuous α)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {m g : ℝ}
    (h_stage_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
    (h_cone : g ≤ m + p.β_S * g * (1 - p.δ))
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV : LowerSlopeOnValueOn V (Set.Icc (0:ℝ) 1) g) :
    LowerSlopeOnValueOn (p.bellmanS_BCF α hα V) (Set.Icc (0:ℝ) 1) g := by
  intro y₁ y₂ _ _ hle
  have hβ : (0:ℝ) ≤ p.β_S := p.β_S_mem.1
  have hδ1 : p.δ < 1 := p.δ_mem.2
  have hd : dist y₁ y₂ = y₂.val - y₁.val := dist_eq_sub_of_le hle
  have hdiff_nn : (0:ℝ) ≤ y₂.val - y₁.val := by rw [← hd]; exact dist_nonneg
  have h_point : ∀ s ∈ Sanctions.I,
      g * dist y₁ y₂ ≤ p.integrandS α (fun z => V z) (y₂.val, s)
                        - p.integrandS α (fun z => V z) (y₁.val, s) := by
    intro s hs
    have hy₁ : y₁.val ∈ Sanctions.I := y₁.property
    have hy₂ : y₂.val ∈ Sanctions.I := y₂.property
    have hU := h_stage_state_slope s hs y₁.val y₁.property y₂.val y₂.property hle
    have hF₁ : p.F y₁.val s ∈ Set.Icc (0:ℝ) 1 := p.F_mem _ _ hy₁ hs
    have hF₂ : p.F y₂.val s ∈ Set.Icc (0:ℝ) 1 := p.F_mem _ _ hy₂ hs
    have hFle : p.F y₁.val s ≤ p.F y₂.val s := p.F_mono_x s hle
    have hord : Sanctions.clipS' (p.F y₁.val s) ≤ Sanctions.clipS' (p.F y₂.val s) :=
      Sanctions.clipS'_mono hFle
    have hVslope := hV (Sanctions.clipS' (p.F y₁.val s))
      (Sanctions.clipS' (p.F y₂.val s))
      (by rw [Sanctions.clipS'_val_eq_of_mem hF₁]; exact hF₁)
      (by rw [Sanctions.clipS'_val_eq_of_mem hF₂]; exact hF₂) hord
    have hdF : dist (Sanctions.clipS' (p.F y₁.val s))
        (Sanctions.clipS' (p.F y₂.val s)) = (1 - p.δ) * (y₂.val - y₁.val) := by
      rw [Sanctions.AbstractGame.Params.clipS'_dist_eq_of_mem hF₁ hF₂, hF]
      unfold Sanctions.AbstractGame.affineF
      rw [show (1 - p.δ) * y₁.val + p.δ * s - ((1 - p.δ) * y₂.val + p.δ * s)
            = -((1 - p.δ) * (y₂.val - y₁.val)) from by ring, abs_neg]
      exact abs_of_nonneg (mul_nonneg (by linarith) hdiff_nn)
    rw [hdF] at hVslope
    have hVscaled : p.β_S * (g * ((1 - p.δ) * (y₂.val - y₁.val)))
        ≤ p.β_S * (V (Sanctions.clipS' (p.F y₂.val s))
            - V (Sanctions.clipS' (p.F y₁.val s))) :=
      mul_le_mul_of_nonneg_left hVslope hβ
    have hcone_scaled : g * (y₂.val - y₁.val)
        ≤ (m + p.β_S * g * (1 - p.δ)) * (y₂.val - y₁.val) :=
      mul_le_mul_of_nonneg_right h_cone hdiff_nn
    show g * dist y₁ y₂
      ≤ (p.U_S y₂.val (α y₂.val) s + p.β_S * V (Sanctions.clipS' (p.F y₂.val s)))
        - (p.U_S y₁.val (α y₁.val) s + p.β_S * V (Sanctions.clipS' (p.F y₁.val s)))
    rw [hd]
    nlinarith [hU, hVscaled, hcone_scaled]
  have hbdd := p.integrandS_image_bddAbove hα V.continuous y₂.val
  have hIne : (Sanctions.I : Set ℝ).Nonempty := ⟨0, by simp [Sanctions.I]⟩
  show g * dist y₁ y₂
      ≤ sSup ((fun s => p.integrandS α (fun z => V z) (y₂.val, s)) '' Sanctions.I)
        - sSup ((fun s => p.integrandS α (fun z => V z) (y₁.val, s)) '' Sanctions.I)
  exact Sanctions.StokeyLucas.sSup_image_sub_sSup_image_lowerBound_of_pointwise
    hIne h_point hbdd

/-! ## General-`F` cone preservation: one joint chord, no condition on `F` alone

The affine restriction above is not intrinsic. It enters at exactly one step —
computing `dist (F y₁ s) (F y₂ s) = (1 − δ)·(y₂ − y₁)` — and the obvious repair,
a linear state-side chord `d·(y₂ − y₁) ≤ F y₂ s − F y₁ s` mirroring
`SanctionLowerChordWith`, is *not* the right generalisation. The literature says
so, and the reason is worth recording.

**Why the naive repair is the wrong shape.** Smith and McCardle (2002),
*Structural Properties of Stochastic Dynamic Programs*, Operations Research
50(5), 796–809 — local copy at
`PaperRefer/MathTheory/StructuralPropertiesStochasticDynamicPrograms-SmithMcCardle-2002.md`
— give the governing metatheorem: for a **closed convex cone (C³) property** `P`,
the value function has `P` whenever the reward has `P` and the transition has the
stochastic version of `P` (their §6; the monotonicity case is classical, and they
attribute it to Stokey and Lucas 1989, pp. 267–268).

`LowerSlopeOnValueOn V B g` with `g > 0` is **not** a C³ property: scaling `V` by
`a < 1` drops the floor to `a·g`, so the set is a translated cone rather than a
cone, and the metatheorem does not apply to it directly. That is precisely why
the proof above had to reach for a linear chord on `F`.

**The standard device dissolves it.** `V` has lower slope `g` iff `V − g·id` is
increasing, and *monotonicity is* the canonical C³ property. Writing
`W := V − g·id` and translating the Bellman equation gives

```text
W(x) = sup_s { U(x,s) + β·g·F(x,s) − g·x  +  β·W(F(x,s)) }
```

so `W` is increasing as soon as the **modified reward** `U(x,s) + β·g·F(x,s) − g·x`
is increasing in `x` and `F(·,s)` is monotone — and monotonicity of `F` in the
state is `F_mono_x`, already a `Params` field. No condition on `F` alone is
needed at any point.

**What this buys, concretely.** The hypothesis below is a single joint chord in
existing primitives. It is *strictly weaker* than the affine trio: the m-chord,
the cone inequality `g ≤ m + β_S·g·(1−δ)`, and `hF` together imply it (see
`joint_state_chord_of_stage_chord_and_affine`), while the converse fails, because
the joint form lets the stage payoff compensate wherever the transition is flat
and vice versa — a trade-off the separated form forbids. It also deletes two
named scalars rather than adding one, which is what Rule 3's symbol-economy
clause asks for.

Economically: *raising the inherited political state by `Δ` raises the Sender's
stage payoff plus the discounted value of the extra entrenchment it buys by at
least `g·Δ`.* The state pays for itself at rate `g` counting both channels
together, instead of each channel having to clear a bar separately. -/

/-- **The Sender Bellman fixed point inherits the primitive state chord.**

`bellmanLowerSlopeConstant β_S (1−δ) m = m / (1 − β_S·(1−δ))` is the
Benveniste–Scheinkman closed form.  Existence is *constructed*, never
hypothesised: `p.V_S α hα` is by definition the Banach fixed point of
`bellmanS_BCF`, and cone membership is obtained by trapping the iteration —
the cone is closed, the linear seed is in it, and the operator preserves it —
via the in-repo `Sanctions.StokeyLucas.fixedPoint_mem_of_mapsTo`. -/
theorem V_S_mem_lowerSlopeCone
    {α : ℝ → ℝ} (hα : Continuous α)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {m : ℝ}
    (h_stage_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s) :
    LowerSlopeOnValueOn (p.V_S α hα) (Set.Icc (0:ℝ) 1)
      (Sanctions.StokeyLucas.bellmanLowerSlopeConstant p.β_S (1 - p.δ) m) := by
  set g : ℝ := Sanctions.StokeyLucas.bellmanLowerSlopeConstant p.β_S (1 - p.δ) m
    with hgdef
  have hid : m + p.β_S * g * (1 - p.δ) = g := p.lowerSlopeConstant_cone_identity m
  have hcontr : ContractingWith p.β_S_nnreal (p.bellmanS_BCF α hα) :=
    p.bellmanS_BCF_contracting hα
  have h_eq : p.V_S α hα = hcontr.fixedPoint := by
    unfold V_S; congr
  obtain ⟨W, hW_fix, hW_mem⟩ :=
    Sanctions.StokeyLucas.fixedPoint_mem_of_mapsTo p.β_S_nnreal_lt_one
      (p.bellmanS_BCF α hα) hcontr.2
      {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ | LowerSlopeOnValueOn V (Set.Icc (0:ℝ) 1) g}
      (lowerSlopeCone_isClosed g) ⟨linSeed g, linSeed_mem_lowerSlopeCone g⟩
      (fun _ hW => p.bellmanS_BCF_preserves_lowerSlopeCone hα hF
        h_stage_state_slope (by linarith) hW)
  rw [h_eq, ← hcontr.fixedPoint_unique hW_fix]
  exact hW_mem

/-- **The constructed equilibrium value is not the zero function.**  With a
strictly positive primitive state chord `m > 0`, `V_S` sits in a cone that
excludes `0`.

Scope: this says the economy's *own* equilibrium continuation value is nonzero.
It does **not** remove the zero function from the monotone carrier over which
`uniform_floor_iff_stage_floor` (`Theory/LockIn/PersistenceMargin.lean`)
quantifies — `0` is monotone and stays in that carrier here as everywhere, so
that barrier is untouched.  The cone route avoids the barrier by changing what
is quantified over, not by shrinking the monotone carrier. -/
theorem V_S_ne_zero_of_pos_state_slope
    {α : ℝ → ℝ} (hα : Continuous α)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {m : ℝ} (hm_pos : 0 < m)
    (h_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s) :
    p.V_S α hα ≠ 0 := by
  intro hzero
  have hpos := p.oneMinus_betaS_oneMinusDelta_pos
  have hcone := p.V_S_mem_lowerSlopeCone hα hF h_state_slope
  rw [hzero] at hcone
  refine zero_not_mem_lowerSlopeCone ?_ hcone
  rw [Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def]
  exact div_pos hm_pos hpos

/-! ## Axiom hygiene (Rule 10) -/

/-- **Route (b): `hSC_on` derived from the range-local convexity cone
(Round C7-b).** If every Sender value in the carrier is convex along
the basin transition range `[lo, 1]` (`lo ≤ (1−δ)·x̄`), then —
combined with stage complementarity (`SenderStageID`), the R28
compliance-placates sign (`SenderActionDD`), and α-antitonicity on
the basin (E4) — the Sender's dynamic objective at the equilibrium
policy has increasing differences, hence single crossing, in
(sanction; state) on the basin: exactly the certificate field
`hSC_on`. -/
theorem hSC_on_of_carrier_convexOn_range
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (D : p.ValueClass2) {xbar lo : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlo_le : lo ≤ (1 - p.δ) * xbar)
    (hID_S : p.SenderStageID) (hDD_a : p.SenderActionDD)
    (hanti : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      AntitoneOn (D.α_on V_T V_S) (Set.Icc xbar 1))
    (hconv : ∀ V_S ∈ D.carrier_S, ValueConvexOnRange V_S lo) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc xbar 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s) := by
  intro V_T V_S s₁ s₂ x x' hs₁ hs₂ hss hx hx' hxx'
  have hδ0 : (0 : ℝ) < p.δ := p.δ_mem.1
  have hδ1 : p.δ < 1 := p.δ_mem.2
  have h1δ : (0 : ℝ) ≤ 1 - p.δ := by linarith
  have hxI : x ∈ Sanctions.I := ⟨le_trans hxbar_mem.1 hx.1, hx.2⟩
  have hx'I : x' ∈ Sanctions.I := ⟨le_trans hxbar_mem.1 hx'.1, hx'.2⟩
  have hαx := D.α_on_mem V_T V_S x
  have hαx' := D.α_on_mem V_T V_S x'
  -- α antitone on the basin: deeper state, weakly less compliance.
  have hα_le : D.α_on V_T V_S x' ≤ D.α_on V_T V_S x :=
    hanti V_T V_S hx hx' hxx'
  -- Stage part, action propagation: chord grows as the action falls.
  have h_action := hDD_a x' hx'I hs₁ hs₂ hss hαx' hαx hα_le
  -- Stage part, state propagation at the fixed action α(x).
  have h_state := hID_S (D.α_on V_T V_S x) hαx hs₁ hs₂ hss hxI hx'I hxx'
  -- Continuation part: equal-width value chords shift up along the range.
  have hVconv := hconv V_S.val V_S.2
  have hy₁lo : lo ≤ (1 - p.δ) * x + p.δ * s₁ := by
    have h1 : (1 - p.δ) * xbar ≤ (1 - p.δ) * x :=
      mul_le_mul_of_nonneg_left hx.1 h1δ
    have h2 : 0 ≤ p.δ * s₁ := mul_nonneg hδ0.le hs₁.1
    linarith
  have hy12 : (1 - p.δ) * x + p.δ * s₁ ≤ (1 - p.δ) * x + p.δ * s₂ := by
    have := mul_le_mul_of_nonneg_left hss hδ0.le
    linarith
  have ht_nn : 0 ≤ (1 - p.δ) * (x' - x) := mul_nonneg h1δ (by linarith)
  have htop : ((1 - p.δ) * x + p.δ * s₂) + (1 - p.δ) * (x' - x) ≤ 1 := by
    nlinarith [hx'.2, hs₂.2]
  have hcont := hVconv.chord_shift hy₁lo hy12 ht_nn htop
  have e₁ : ((1 - p.δ) * x + p.δ * s₁) + (1 - p.δ) * (x' - x)
      = (1 - p.δ) * x' + p.δ * s₁ := by ring
  have e₂ : ((1 - p.δ) * x + p.δ * s₂) + (1 - p.δ) * (x' - x)
      = (1 - p.δ) * x' + p.δ * s₂ := by ring
  rw [e₁, e₂] at hcont
  have hβS : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hcont' := mul_le_mul_of_nonneg_left hcont hβS
  -- Increasing differences of the dynamic objective.
  have hID_total :
      p.senderDynObjective V_S.val x' (D.α_on V_T V_S x') s₂
        - p.senderDynObjective V_S.val x' (D.α_on V_T V_S x') s₁
      ≥ p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s₂
        - p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s₁ := by
    simp only [senderDynObjective, hF, Sanctions.AbstractGame.affineF]
    linarith
  -- Increasing differences imply both single-crossing components.
  constructor
  · intro h
    simp only at h ⊢
    linarith
  · intro h
    simp only at h ⊢
    linarith

/-! ### Route (b) off the affine law

The affine hypothesis in `hSC_on_of_carrier_convexOn_range` does exactly one
thing: it makes the state displacement `F(x',s) − F(x,s) = (1−δ)·(x'−x)`
*independent of the sanction*, so the two continuation chords have equal width
and a common rightward shift — which is what `chord_shift` consumes.

An affine transition is **modular**: its cross-difference in `(state, sanction)`
is identically zero. The general condition is therefore not a functional form but
an order condition — the transition has *increasing differences*, so a higher
inherited state weakly widens the sanction's effect on next period's state. The
extra width a genuinely supermodular transition creates is absorbed by
monotonicity of the value along the range, via the Topkis composition rule
`Sanctions.Topkis.chord_le_chord_of_convexOn_monotoneOn`
(Topkis 1998, *Supermodularity and Complementarity*, §2.6).

Both replacements are things the certificate stack already carries or can state
without a new predicate: increasing differences of `F` is
`MilgromShannon.IncreasingDifferencesOn` applied to existing data, and Sender
value monotonicity is already the `hV_S_mono_carrier` field of the MS
certificate. No new `Prop` and no new `Params` field is introduced. -/

/-- **Route (b), fully composed form.** Same conclusion with the
α-antitonicity input discharged from the E4 `SubstitutedTargetDD`
chord condition, so the user-facing inputs are: stage
complementarity, the R28 sign, the Target substituted chord
condition, and carrier membership in the convexity cone. -/
theorem hSC_on_of_carrier_convexOn_range_of_substitutedDD
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (D : p.ValueClass2) {xbar lo : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlo_le : lo ≤ (1 - p.δ) * xbar)
    (hID_S : p.SenderStageID) (hDD_a : p.SenderActionDD)
    (hDD_T : p.SubstitutedTargetDD D xbar)
    (hconv : ∀ V_S ∈ D.carrier_S, ValueConvexOnRange V_S lo) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc xbar 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s) :=
  p.hSC_on_of_carrier_convexOn_range hF D hxbar_mem hlo_le hID_S hDD_a
    (fun V_T V_S => p.α_on_antitoneOn_of_substitutedDD D hDD_T hxbar_mem.1 V_T V_S)
    hconv

/-- **Discharging `SenderCombinedMonotoneOn` at the constructed equilibrium
(strong-rally high basin).** The basin combined-monotonicity — hence
`hSC_on` — is *derived*, not assumed, on the regime where the Sender's
stage payoff is increasing in `s` strongly enough to dominate the
discounted continuation's Lipschitz variation:

* `hV_S_lip` — every carrier value `V_S` is `KS`-Lipschitz. The carrier
  is the closed Lipschitz ball `valLipBall` (`InvariantLipBall.lean`),
  Bellman-invariant under `bellmanS_BCF_preserves_lipschitz_cone`, so the
  constructed equilibrium `V_S` inherits `KS`-Lipschitzness *by
  construction* (Stokey-Lucas Corollary 1 = `fixedPoint_mem_of_mapsTo` /
  `V_S_valueLipschitzWith_of_primitive_margin`) — Rule 15, existence
  constructed not assumed.
* `h_stage_sender` — the stage Sender payoff `U_S(x, α(x), ·)` has a
  positive lower slope `mS` on `[0,1]` at the equilibrium compliance
  `α = D.α_on V_T V_S` (the strong-rally regime).
* `hS_margin` — the strict margin `β_S · KS · δ < mS`: the stage rise
  `mS·Δs` strictly exceeds the worst-case continuation fall
  `β_S·KS·δ·Δs`, so the realised objective rises in `s` *even though
  `V_S` may be non-monotone* (only Lipschitzness is used — exactly the
  numerically-observed non-monotone `V_S`).

The proof is the carrier specialisation of
`senderDynObjective_strictMono_of_stage_lowerSlope_and_V_lipschitz`
(`PrimitiveHighBasin`) at `sbar := 1`, so the engine's choice interval
`[0, max x 1]` equals `Sanctions.I = [0,1]`. Rule 1: `V_S` is the Banach
fixed point and `α = D.α_on` the carrier argmax — no fixed strategy.
Rule 3: no new `Params` field; `mS, KS` are existing/closed-form scalars
and the margin is a strict inequality among existing primitives.

**Scope (honest, Rule 11/12).** This covers the *strong-rally* regime
where the Sender's stage already favours high sanctions on the basin
(numerically: the EE witness with basin lower edge `xT ≥ 0.65`, closed-form
`KS = L_U_S/(1−β_S(1−δ)) = 2.5`, margin `β_S·KS·δ = 0.25 < mS`). It does
**not** cover the genuine *dynamic-dominance* sub-regime where the stage
*falls* in `s` and only the forward-looking continuation carries the
corner: there the Lipschitz cone is too pessimistic (the continuation
gain is real but not capturable by `±KS`, since the equilibrium `V_S` is
non-monotone), and a sharper basin-local value-gain argument would be
needed. -/
theorem senderCombinedMonotoneOn_of_stage_lowerSlope_and_carrier_lipschitz
    (D : p.ValueClass2)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS mS KS : ℝ}
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip : ∀ V_S : D.CarrierS, ValueLipschitzWith V_S.val KS)
    (h_stage_sender :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
          LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
            (Set.Icc (0 : ℝ) 1) mS) :
    p.SenderCombinedMonotoneOn D xT xS := by
  intro V_T V_S x hx
  have hmax : max x (1 : ℝ) = 1 := max_eq_right hx.2
  have h_stage' :
      LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x 1)) mS := by
    rw [hmax]; exact h_stage_sender V_T V_S x hx
  have hmono :=
    p.senderDynObjective_strictMono_of_stage_lowerSlope_and_V_lipschitz
      (V_S := V_S.val) (α := D.α_on V_T V_S) (x := x) (sbar := 1)
      (m := mS) (K := KS) hF hKS_nonneg hS_margin h_stage' (hV_S_lip V_S)
  rw [hmax] at hmono
  exact hmono

/-- **Drop-in derivation of the `hSC_on` certificate field from strong-rally
primitives.** Produces exactly the `hSC_on` field type of
`StandardComplianceLocalCoreCertificate` directly from the certificate's own
margin primitives — `hKS_nonneg`, `hS_margin`, `hV_S_lip_carrier` — plus the
stage Sender lower-slope *strengthened to the full choice axis* `[0,1]` (the
strong-rally regime), composing `senderCombinedMonotoneOn_of_stage_lowerSlope_and_carrier_lipschitz`
with `hSC_on_of_senderCombinedMonotone`. A certificate smart constructor can
call this to make `hSC_on` *derived* rather than a separate assumed field.

Note the strengthening: the legacy certificate field `h_stage_sender_on` holds
only on the floor `[0, max x sbar]`; deriving single crossing over the whole
choice axis `Sanctions.I = [0,1]` requires the lower slope on all of `[0,1]`,
which is exactly the regime where the Sender's stage already favours high
sanctions on the basin (numerically the EE witness for basin `xT ≥ 0.65`). -/
theorem hSC_on_of_strong_rally_primitives
    (D : p.ValueClass2)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {xT xS mS KS : ℝ}
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hV_S_lip_carrier : ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S KS)
    (h_stage_sender_full :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
          LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
            (Set.Icc (0 : ℝ) 1) mS) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s) :=
  p.hSC_on_of_senderCombinedMonotone D
    (p.senderCombinedMonotoneOn_of_stage_lowerSlope_and_carrier_lipschitz D hF
      hKS_nonneg hS_margin
      (fun V_S => hV_S_lip_carrier V_S.val V_S.property)
      h_stage_sender_full)

/-! ## B2 route: the certificate IDO field in the non-monotone-`V_S` regime

Where Milgrom–Shannon single crossing provably fails (non-monotone
Sender continuation value — the dynamic-dominance sub-regime), the
`hIDO_on` field is dischargeable from two Rule-3 primitives
(user-approved 2026-07-02): per-state **quasiconcavity in the
sanction** of the Sender dynamic objective (single-peaked sanction
preference; witness-dischargeable via the existing strict-concavity
pattern) and **`MonotoneTransferOn`** (ordinal escalation-consistency:
sanction ranges favoured at a lower political state remain favoured at
higher states — an OPEN regime primitive at carrier generality, owned
in the paper's limitations). No differentiability and no value
monotonicity is consumed; the engine is the derivative-free
`IDOFamilyOn.of_quasiconcave_monotoneTransfer`
(`Foundations/IntervalDominanceOrder.lean`). -/

/-- **Round-25 smart constructor: closed-form Sender carrier Lipschitz
constant via Hinderer 4.2(c).** Builds a
`StandardComplianceLocalCoreCertificate` from underlying Hinderer 4.2(c)
inputs `(L_U_S, γ_F)` in place of the raw primitive `KS`.

The closed-form Sender Lipschitz constant is
`K_S := L_U_S / (1 − β_S · γ_F)`, computed from
`bellmanLipConstant p.β_S γ_F L_U_S`.

Affine-restricted (it carries `hF`). Round BJ1.4 (2026-10-07): the Target
loss-offset inputs (`cT`, `gT`, `0 ≤ gT`, the margin, the stage loss and value
gain conditions) and `0 < s̄` are gone with the certificate fields they filled. -/
def StandardComplianceLocalCoreCertificate.with_KS_closed_form
    (D : p.ValueClass2) (h_inv : D.IsInvariant)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (β_T β_S L_TS L_ST : ℝ)
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1) (hsuff_S : β_S + L_ST < 1)
    (xT xS sbar mS : ℝ)
    (L_U_S γ_F : ℝ) (hL_U_S_nn : 0 ≤ L_U_S)
    (h_denom_pos : 0 < 1 - p.β_S * γ_F)
    (h_wedge_closed : p.β_S * L_U_S * p.δ < mS * (1 - p.β_S * γ_F))
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hjoint_lt : max xT xS < 1)
    (hV_S_lip_carrier :
      ∀ V_S ∈ D.carrier_S,
        ValueLipschitzWith V_S
          (Sanctions.StokeyLucas.bellmanLipConstant p.β_S γ_F L_U_S))
    (h_stage_sender_on :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc xS (1 : ℝ),
          LowerSlopeOn
            (fun s => p.U_S x (D.α_on V_T V_S x) s)
            (Set.Icc (0 : ℝ) (max x sbar)) mS)
    (hSC_on :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        Sanctions.MilgromShannon.SingleCrossingOn
          Sanctions.I (Set.Icc (max xT xS) 1)
          (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s))
    (M : p.MyopicFeedbackEquilibrium)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max xT xS) 1, p.σ x (M.α x) ≤ max x sbar) :
    p.StandardComplianceLocalCoreCertificate where
  D := D
  h_inv := h_inv
  d := p.δ
  hF_chord := by
    intro x _ s₁ _ s₂ _ hs
    have hval : p.F x s₂ - p.F x s₁ = p.δ * (s₂ - s₁) := by
      rw [hF]; unfold Sanctions.AbstractGame.affineF; ring
    rw [hval]
    exact le_of_eq (abs_of_nonneg
      (mul_nonneg (le_of_lt p.δ_mem.1) (by linarith)))
  β_T := β_T
  β_S := β_S
  L_TS := L_TS
  L_ST := L_ST
  hβ_T_nn := hβ_T_nn
  hβ_S_nn := hβ_S_nn
  hL_TS_nn := hL_TS_nn
  hL_ST_nn := hL_ST_nn
  hT_T_op := hT_T_op
  hT_S_op := hT_S_op
  hsuff_T := hsuff_T
  hsuff_S := hsuff_S
  xT := xT
  xS := xS
  sbar := sbar
  mS := mS
  KS := Sanctions.StokeyLucas.bellmanLipConstant p.β_S γ_F L_U_S
  hxT_mem := hxT_mem
  hxS_mem := hxS_mem
  hsbar_mem := hsbar_mem
  hS_margin := p.hS_margin_of_closed_form h_denom_pos h_wedge_closed
  hjoint_lt := hjoint_lt
  hV_S_lip_carrier := hV_S_lip_carrier
  h_stage_sender_on := h_stage_sender_on
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (hSC_on V_T V_S)
  M := M
  hMyoCeiling := hMyoCeiling

/-- **Smart constructor: `hSC_on` derived from the strong-rally regime.**

Builds a `StandardComplianceLocalCoreCertificate` whose single-crossing
field `hSC_on` is *derived* — not separately assumed — from the
certificate's own margin primitives (`hKS_nonneg`, `hS_margin`,
`hV_S_lip_carrier`) plus the affine transition `hF` and the Sender stage
lower-slope `h_stage_sender_full` on the *full* choice axis `[0,1]` (the
strong-rally regime, where the Sender already favours high sanctions on the
basin). The `hSC_on` field is filled by `hSC_on_of_strong_rally_primitives`
(which composes the equilibrium-side discharge of `SenderCombinedMonotoneOn`
with the Interval-Dominance-Order single-crossing route). Every other field
is passed through unchanged.

This is the issue-1 referee answer at the certificate level: a user
constructing the persistence certificate no longer supplies the
endogenous-looking single-crossing-at-the-equilibrium-action as a black-box
hypothesis; they supply the strong-rally stage condition, and single
crossing — hence every headline `three_goals_local*` consuming this
certificate — is *derived*. Rule 1: the strategy is the Banach/Tarski-
constructed equilibrium; Rule 3: no new `Params` field, the margin is a
strict inequality among existing primitives; Rule 13: additive (the
`hSC_on`-taking constructors are untouched).

Scope: the strong-rally regime, numerically the EE witness for basin
`xT ≥ 0.65`. The dynamic-dominance sub-regime (Sender stage falling in `s`)
remains outside the Lipschitz-cone reach (see
`senderCombinedMonotoneOn_of_stage_lowerSlope_and_carrier_lipschitz`).

Affine-restricted (it carries `hF`). Round BJ1.4 (2026-10-07): the Target
loss-offset inputs and `0 < s̄` are gone with the certificate fields they
filled. -/
def StandardComplianceLocalCoreCertificate.with_hSC_on_derived
    (D : p.ValueClass2) (h_inv : D.IsInvariant)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (β_T β_S L_TS L_ST : ℝ)
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1) (hsuff_S : β_S + L_ST < 1)
    (xT xS sbar mS KS : ℝ)
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hKS_nonneg : 0 ≤ KS)
    (hS_margin : p.β_S * KS * p.δ < mS)
    (hjoint_lt : max xT xS < 1)
    (hV_S_lip_carrier : ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S KS)
    (h_stage_sender_on :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc xS (1 : ℝ),
          LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
            (Set.Icc (0 : ℝ) (max x sbar)) mS)
    (h_stage_sender_full :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
          LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
            (Set.Icc (0 : ℝ) 1) mS)
    (M : p.MyopicFeedbackEquilibrium)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max xT xS) 1, p.σ x (M.α x) ≤ max x sbar) :
    p.StandardComplianceLocalCoreCertificate where
  D := D
  h_inv := h_inv
  d := p.δ
  hF_chord := by
    intro x _ s₁ _ s₂ _ hs
    have hval : p.F x s₂ - p.F x s₁ = p.δ * (s₂ - s₁) := by
      rw [hF]; unfold Sanctions.AbstractGame.affineF; ring
    rw [hval]
    exact le_of_eq (abs_of_nonneg
      (mul_nonneg (le_of_lt p.δ_mem.1) (by linarith)))
  β_T := β_T
  β_S := β_S
  L_TS := L_TS
  L_ST := L_ST
  hβ_T_nn := hβ_T_nn
  hβ_S_nn := hβ_S_nn
  hL_TS_nn := hL_TS_nn
  hL_ST_nn := hL_ST_nn
  hT_T_op := hT_T_op
  hT_S_op := hT_S_op
  hsuff_T := hsuff_T
  hsuff_S := hsuff_S
  xT := xT
  xS := xS
  sbar := sbar
  mS := mS
  KS := KS
  hxT_mem := hxT_mem
  hxS_mem := hxS_mem
  hsbar_mem := hsbar_mem
  hS_margin := hS_margin
  hjoint_lt := hjoint_lt
  hV_S_lip_carrier := hV_S_lip_carrier
  h_stage_sender_on := h_stage_sender_on
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (p.hSC_on_of_strong_rally_primitives D hF hKS_nonneg hS_margin
        hV_S_lip_carrier h_stage_sender_full V_T V_S)
  M := M
  hMyoCeiling := hMyoCeiling

/-! ## Round-37: symbol-elimination of the Sender stage-slope wedge

The Round-37 audit (2026-06-05) eliminates the named scalar `mS`
and the margin Prop `β_S · KS · δ < mS` from the paper-facing
surface of Assumption 1 (`\Cref{ass:sender_pref}`). In place of
the named pair, the canonical paper statement becomes the **single
strict chord inequality**

  U_S(x, α_on V_T V_S x, s₂) − U_S(x, α_on V_T V_S x, s₁)
    >  β_S · KS · δ · (s₂ − s₁)

for every carrier pair, every basin state `x ∈ [xS, 1]`, and every
chord `0 ≤ s₁ ≤ s₂ ≤ max x sbar`. The substantive content — the
Sender's marginal benefit of sanctions, evaluated at the equilibrium
Target response, strictly exceeds the worst-case discounted
continuation-value loss rate — is identical to the named-scalar
form, but no new "slope" scalar `mS` and no separate "margin" Prop
appear on the paper-facing assumption surface.

On the Lean side, the strict inequality is encoded with a witnessed
positive uniform gap `gap > 0`. The derived scalar
`mS := β_S · KS · δ + gap` and the margin
`hS_margin := β_S · KS · δ < mS` are then both automatic. The
smart constructor `with_strict_slope_wedge` performs this internal
synthesis so the user supplies only the strict chord inequality and
the gap witness, never the named `mS`.

## Rule compliance
* Rule 1: no strategy changes; chord evaluated at the equilibrium
  Target selector `D.α_on V_T V_S`.
* Rule 3 symbol-economy clause: the named pair `(mS, hS_margin)` is
  replaced by the single strict chord inequality plus an
  existentially-witnessed positive gap. No new economic primitive
  appears on the paper-facing assumption surface — `KS`, `β_S`, `δ`,
  `U_S`, `α_on` are all already-existing parameters; `gap` is a
  Lean-internal derived handle hidden under the smart constructor.
* Rule 5: fully parametric, no witness numerics.
* Rule 8: human-language paraphrase in this docstring and in the
  smart constructor's docstring. -/

/-- **Round-37 smart constructor: strict-slope-form Assumption 1.**

    Builds a `StandardComplianceLocalCoreCertificate` from the
    canonical strict-slope form of Assumption 1 in place of the
    named scalar `mS` and the explicit margin
    `β_S · KS · δ < mS`. The strict chord inequality is encoded
    with a witnessed positive uniform gap `gap > 0`; the derived
    `mS := β_S · KS · δ + gap` and `hS_margin` follow automatically.

    See the section comment above for the paper-facing reading
    and the Rule 3 symbol-economy justification.

    Affine-restricted (it carries `hF`). Round BJ1.4 (2026-10-07): the
    Target loss-offset inputs and `0 < s̄` are gone with the certificate
    fields they filled. -/
def StandardComplianceLocalCoreCertificate.with_strict_slope_wedge
    (D : p.ValueClass2) (h_inv : D.IsInvariant)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (β_T β_S L_TS L_ST : ℝ)
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1) (hsuff_S : β_S + L_ST < 1)
    (xT xS sbar : ℝ)
    (KS : ℝ) (hKS_nn : 0 ≤ KS)
    (gap : ℝ) (hgap_pos : 0 < gap)
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hjoint_lt : max xT xS < 1)
    (hV_S_lip_carrier :
      ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S KS)
    (h_stage_sender_strict_chord :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc xS (1 : ℝ),
          ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
          ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar),
          s₁ ≤ s₂ →
            (p.β_S * KS * p.δ + gap) * (s₂ - s₁)
              ≤ p.U_S x (D.α_on V_T V_S x) s₂
                - p.U_S x (D.α_on V_T V_S x) s₁)
    (hSC_on :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        Sanctions.MilgromShannon.SingleCrossingOn
          Sanctions.I (Set.Icc (max xT xS) 1)
          (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s))
    (M : p.MyopicFeedbackEquilibrium)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max xT xS) 1, p.σ x (M.α x) ≤ max x sbar) :
    p.StandardComplianceLocalCoreCertificate where
  D := D
  h_inv := h_inv
  d := p.δ
  hF_chord := by
    intro x _ s₁ _ s₂ _ hs
    have hval : p.F x s₂ - p.F x s₁ = p.δ * (s₂ - s₁) := by
      rw [hF]; unfold Sanctions.AbstractGame.affineF; ring
    rw [hval]
    exact le_of_eq (abs_of_nonneg
      (mul_nonneg (le_of_lt p.δ_mem.1) (by linarith)))
  β_T := β_T
  β_S := β_S
  L_TS := L_TS
  L_ST := L_ST
  hβ_T_nn := hβ_T_nn
  hβ_S_nn := hβ_S_nn
  hL_TS_nn := hL_TS_nn
  hL_ST_nn := hL_ST_nn
  hT_T_op := hT_T_op
  hT_S_op := hT_S_op
  hsuff_T := hsuff_T
  hsuff_S := hsuff_S
  xT := xT
  xS := xS
  sbar := sbar
  mS := p.β_S * KS * p.δ + gap
  KS := KS
  hxT_mem := hxT_mem
  hxS_mem := hxS_mem
  hsbar_mem := hsbar_mem
  hS_margin := by linarith
  hjoint_lt := hjoint_lt
  hV_S_lip_carrier := hV_S_lip_carrier
  h_stage_sender_on := h_stage_sender_strict_chord
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (hSC_on V_T V_S)
  M := M
  hMyoCeiling := hMyoCeiling

/-! ## Round 38 — affine closed-form compatibility composite

The current model permits a general transition `F`.  For the affine
instance `F(x, s) = (1 − δ) · x + δ · s`, its fixed-sanction state
modulus is `γ_F = 1 − δ`.  The compatibility constructor below fixes
that affine modulus in the R25 closed form
`K_S := L_U_S / (1 − β_S · (1 − δ))` and combines it with R37's
strict-slope bookkeeping.

The constructor does not prove that `p.F` is affine.  Its carrier
Lipschitz and strict-chord premises must already justify the supplied
affine-form constant.  Transition-general consumers should instead use
the explicit-`γ_F` constructor or the exact transition-adjusted chord.
The legacy identifier retains `canonical` only for API compatibility.

## Rule compliance
* Rule 1: structural, no strategy fixings.
* Rule 3 symbol-economy: on the affine route, substitutes the derived
  modulus `γ_F = 1 − δ`; on a general transition this substitution is
  unavailable.
* Rule 5: fully parametric.
* Rule 8: human-language paraphrase below. -/

/-- **Round-38 affine compatibility smart constructor (R37 + R25 + R38).**

    Builds a `StandardComplianceLocalCoreCertificate` taking only:
    * Sender stage-payoff Lipschitz `L_U_S ≥ 0`
    * Strict-slope gap witness `gap > 0` (R37 Lean-internal)
    * The R37 strict chord inequality at the R25-R38-derived
      `K_S := L_U_S / (1 − β_S · (1 − δ))`
    * The value-class fields unchanged (round BJ1.4, 2026-10-07: there are
      no Target-side loss-offset fields any more, and no `0 < s̄`)

    All Sender-side scalars (`K_S`, `m_S`, the contraction-margin
    positivity `0 < 1 − β_S · (1 − δ)`, the margin
    `β_S · K_S · δ < m_S`) are synthesized internally.

    This is the affine compatibility entry path after the
    R25 + R37 + R38 elimination chain. The earlier
    `with_KS_closed_form` (R25) and `with_strict_slope_wedge` (R37)
    constructors remain available for transition-general or explicit
    modulus use.  The declaration name is retained for back-compat. -/
def StandardComplianceLocalCoreCertificate.with_strict_slope_wedge_canonical
    (D : p.ValueClass2) (h_inv : D.IsInvariant)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (β_T β_S L_TS L_ST : ℝ)
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1) (hsuff_S : β_S + L_ST < 1)
    (xT xS sbar : ℝ)
    (L_U_S : ℝ) (hL_U_S_nn : 0 ≤ L_U_S)
    (gap : ℝ) (hgap_pos : 0 < gap)
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hjoint_lt : max xT xS < 1)
    (hV_S_lip_carrier :
      ∀ V_S ∈ D.carrier_S,
        ValueLipschitzWith V_S
          (Sanctions.StokeyLucas.bellmanLipConstant p.β_S (1 - p.δ) L_U_S))
    (h_stage_sender_strict_chord :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc xS (1 : ℝ),
          ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
          ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar),
          s₁ ≤ s₂ →
            (p.β_S *
                (Sanctions.StokeyLucas.bellmanLipConstant
                  p.β_S (1 - p.δ) L_U_S) *
                p.δ + gap) * (s₂ - s₁)
              ≤ p.U_S x (D.α_on V_T V_S x) s₂
                - p.U_S x (D.α_on V_T V_S x) s₁)
    (hSC_on :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        Sanctions.MilgromShannon.SingleCrossingOn
          Sanctions.I (Set.Icc (max xT xS) 1)
          (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s))
    (M : p.MyopicFeedbackEquilibrium)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max xT xS) 1, p.σ x (M.α x) ≤ max x sbar) :
    p.StandardComplianceLocalCoreCertificate :=
  StandardComplianceLocalCoreCertificate.with_strict_slope_wedge p
    D h_inv hF β_T β_S L_TS L_ST
    hβ_T_nn hβ_S_nn hL_TS_nn hL_ST_nn hT_T_op hT_S_op hsuff_T hsuff_S
    xT xS sbar
    (Sanctions.StokeyLucas.bellmanLipConstant p.β_S (1 - p.δ) L_U_S)
    (p.hKS_nonneg_of_closed_form_canonical hL_U_S_nn)
    gap hgap_pos hxT_mem hxS_mem hsbar_mem hjoint_lt
    hV_S_lip_carrier h_stage_sender_strict_chord hSC_on M hMyoCeiling

/-! ## Round 43 Phase A — `s̄` default to joint pivot `max(xT, xS)`

The certificate's `sbar` field bounds the chord domain of
\Cref{ass:sender_pref} on `[0, max(x, sbar)]` and of
\Cref{ass:target_pref} on `[max(x, sbar), 1]`. On the basin
`x ∈ [max xT xS, 1]`, the term `max(x, sbar)` reduces to `x` whenever
`sbar ≤ max(xT, xS)`. The minimal natural default for `sbar` is then
the joint pivot `max(xT, xS)` itself: it is feasible, and on the basin
it makes `max(x, sbar) = x` automatically. (Until round BJ1.4,
2026-10-07, the certificate also asked for `0 < sbar`, which the
default met whenever the basin pivot is positive.)

Round 43 Phase A ships a smart constructor that defaults
`sbar := max(xT, xS)`, removing it from the user-supplied scalar
surface. The constructor takes a single new input `hpivot_pos :
0 < max(xT, xS)` (the basin pivot is positive), which is satisfied
in every concrete sanctions model where the basin is non-degenerate.

## Rule compliance
* Rule 3 symbol-economy: `sbar` is identified with the existing
  primitive `max(xT, xS)` at the canonical natural default; no new
  modeling content is introduced.
* Rule 5: parametric.
* Rule 8: human-language paraphrase below. -/

/-- **Round 43 Phase A: `sbar`-default smart constructor.**

    Builds a `StandardComplianceLocalCoreCertificate` defaulting
    `sbar := max(xT, xS)` (the joint basin pivot). The user no longer
    supplies a `sbar` scalar or `hsbar_mem`; it is auto-discharged from the
    existing pivot hypotheses plus the `hpivot_pos : 0 < max(xT, xS)` input.
    The chord inequality of \Cref{ass:sender_pref} is then stated with
    `sbar = max(xT, xS)` in the implicit-domain `max(x, sbar)`.

    Affine-restricted (it carries `hF`). Round BJ1.4 (2026-10-07): the
    Target loss-offset inputs are gone with the certificate fields they
    filled, and `hpivot_pos` now only places the default floor in `[0, 1]`. -/
def StandardComplianceLocalCoreCertificate.with_strict_slope_wedge_canonical_sbar_default
    (D : p.ValueClass2) (h_inv : D.IsInvariant)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    (β_T β_S L_TS L_ST : ℝ)
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S_op : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1) (hsuff_S : β_S + L_ST < 1)
    (xT xS : ℝ)
    (L_U_S : ℝ) (hL_U_S_nn : 0 ≤ L_U_S)
    (gap : ℝ) (hgap_pos : 0 < gap)
    (hxT_mem : xT ∈ Sanctions.I) (hxS_mem : xS ∈ Sanctions.I)
    (hpivot_pos : 0 < max xT xS) (hjoint_lt : max xT xS < 1)
    (hV_S_lip_carrier :
      ∀ V_S ∈ D.carrier_S,
        ValueLipschitzWith V_S
          (Sanctions.StokeyLucas.bellmanLipConstant p.β_S (1 - p.δ) L_U_S))
    (h_stage_sender_strict_chord :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        ∀ x ∈ Set.Icc xS (1 : ℝ),
          ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x (max xT xS)),
          ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x (max xT xS)),
          s₁ ≤ s₂ →
            (p.β_S *
                (Sanctions.StokeyLucas.bellmanLipConstant
                  p.β_S (1 - p.δ) L_U_S) *
                p.δ + gap) * (s₂ - s₁)
              ≤ p.U_S x (D.α_on V_T V_S x) s₂
                - p.U_S x (D.α_on V_T V_S x) s₁)
    (hSC_on :
      ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
        Sanctions.MilgromShannon.SingleCrossingOn
          Sanctions.I (Set.Icc (max xT xS) 1)
          (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s))
    (M : p.MyopicFeedbackEquilibrium)
    (hMyoCeiling :
      ∀ x ∈ Set.Icc (max xT xS) 1, p.σ x (M.α x) ≤ max x (max xT xS)) :
    p.StandardComplianceLocalCoreCertificate :=
  have hsbar_mem : max xT xS ∈ Sanctions.I := by
    refine ⟨le_of_lt hpivot_pos, le_of_lt hjoint_lt⟩
  StandardComplianceLocalCoreCertificate.with_strict_slope_wedge_canonical p
    D h_inv hF β_T β_S L_TS L_ST
    hβ_T_nn hβ_S_nn hL_TS_nn hL_ST_nn hT_T_op hT_S_op hsuff_T hsuff_S
    xT xS (max xT xS) L_U_S hL_U_S_nn gap hgap_pos hxT_mem hxS_mem
    hsbar_mem hjoint_lt
    hV_S_lip_carrier h_stage_sender_strict_chord hSC_on M hMyoCeiling

namespace StandardComplianceLocalCoreCertificateSchur

/-- The Sender margin at the affine rate. -/
theorem hS_margin_delta (C : p.StandardComplianceLocalCoreCertificateSchur)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    p.β_S * C.KS * p.δ < C.mS := by
  have hδ_le_d : p.δ ≤ C.d := by
    have hxS1 : (1 : ℝ) ∈ Set.Icc C.xS (1 : ℝ) := ⟨C.hxS_mem.2, le_refl _⟩
    have hpos : 0 < max (1 : ℝ) C.sbar := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (max (1 : ℝ) C.sbar) :=
      ⟨le_refl _, le_of_lt hpos⟩
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) (max (1 : ℝ) C.sbar) :=
      ⟨zero_le_one, le_max_left _ _⟩
    have h := C.hF_chord 1 hxS1 0 h0 1 h1 zero_le_one
    have hval : p.F 1 1 - p.F 1 0 = p.δ := by
      rw [hF]; unfold Sanctions.AbstractGame.affineF; ring
    rw [hval] at h
    have : p.δ ≤ C.d * (1 - 0) := le_trans (le_abs_self _) h
    linarith
  calc p.β_S * C.KS * p.δ ≤ p.β_S * C.KS * C.d :=
        mul_le_mul_of_nonneg_left hδ_le_d (mul_nonneg p.β_S_mem.1 C.hKS_nonneg)
    _ < C.mS := C.hS_margin

-- Round BJ1.4 (2026-10-07): the Schur `hT_loss_margin_delta` stood here; it read the
-- deleted Target loss-offset fields and had no consumer.

/-- **Three goals from the Schur-form certificate (Round A2).**
Identical conclusion to
`standardCompliance_three_goals_local_uniform_starts`, reached through the
Round-E1 Perov existence. Since round BH1.7 (2026-10-06) an instance of the
general-`F` Schur sibling `three_goals_local_uniform_starts_generalF`: `hF`
gives `hAdj` and turns the affine trajectory objects into the general-`F` ones
(`pathFamilies_eq_pathFamiliesF_of_affine`). Affine-restricted by its `hF`
binder. -/
theorem three_goals_local_uniform_starts
    (C : p.StandardComplianceLocalCoreCertificateSchur)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ C.D.carrier_T
      ∧ E.V_S ∈ C.D.carrier_S
      ∧ (∀ x₀ ∈ Set.Icc (max C.xT C.xS) 1,
          (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
          (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
          Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => p.joint_T_top_integrand E.V_T E.V_S
                        (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
            Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc (max C.xT C.xS) 1,
           p.σ x (C.M.α x) ≤ p.dynamicTopRealizedRule E.V_S E.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, p.dynamicTopLockInPath E.V_S E.α
                    (p.shockPath x₀shock N) n
                    ∈ Set.Icc (max C.xT C.xS) 1) ∧
            (∀ n, C.sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α
                            (p.shockPath x₀shock N) n) ∧
            (∀ n, max C.xT C.xS ≤ p.dynamicTopLockInSanctions E.V_S E.α
                                    (p.shockPath x₀shock N) n)) := by
  obtain ⟨ePath, eSanc, eShock, -⟩ := p.pathFamilies_eq_pathFamiliesF_of_affine hF
  rw [ePath, eSanc, eShock]
  exact C.three_goals_local_uniform_starts_generalF p
    (Sanctions.AbstractGame.strictAdjustment_of_F_eq_affineF p p.δ_mem hF)

end StandardComplianceLocalCoreCertificateSchur

end Params

end AbstractGame

end

end Sanctions
