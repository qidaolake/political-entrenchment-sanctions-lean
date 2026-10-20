/-
Sanctions/Examples/QuadBumpFiniteEpisode.lean

**The finite-episode non-exit theorem, instantiated at a non-affine
transition** (doc 59 §7: "instantiate through an existing general-`F`
certificate and, where applicable, an existing non-affine witness").

At `qbParams` — transition `quadBumpF`, which is not `affineF δ` for any `δ`
(`quadBumpF_ne_affineF`) — the general-`F` certificate route
`three_goals_local_MS_generalF` constructs a full equilibrium `E` whose
realised rule is at or above the pivot `1/10` on the basin `[1/10, 1]`. That is
exactly the weak-floor input of
`equilibriumTop_post_episode_nonexit_generalF`, with the corner condition free
at `s̄ = x̄` (`corner_of_pivot_le_floor`). Three statements follow:

1. **Any episode ending in the basin.** Whatever the imposed schedule, if it
   leaves the state in `[1/10, 1]` at date `T`, the resumed equilibrium never
   leaves the basin, never sanctions below `1/10`, and never reaches a cutoff
   strictly below `1/10`.
2. **A maximal episode of the canonical length.** With `qbParams`' strict
   adjustment, every full-sanction schedule of length at least
   `fullShockEntryHorizon (1/10)` ends in the basin, from every start.
3. **A non-maximal episode.** Every feasible schedule held at or above a level
   `h ∈ (1/10, 1]` for at least `highEpisodeHorizon h (1/10)` periods ends in
   the basin, from every start.

Rule 9: existence certificates. They show the theorem's hypotheses are met at
one non-affine economy; they license nothing about other economies. Rule 1:
the post-episode rule is `E`'s realised rule, an equilibrium object; the
episode is imposed. Rule 3: no new assumption — every input is a conclusion of
the existing certificate or an existing witness lemma.
-/
import Sanctions.Examples.QuadBumpCertWitnessMS
import Sanctions.Theory.LockIn.FiniteEpisodePersistence

namespace Sanctions
namespace Examples

open Set AbstractGame

/-- The certificate's pivots are `1/10`. -/
theorem qbCertCertificateMS_xT : qbCertCertificateMS.xT = 1/10 := rfl
theorem qbCertCertificateMS_xS : qbCertCertificateMS.xS = 1/10 := rfl

/-- The general-`F` certificate equilibrium at `qbParams`, with its realised
rule at or above the pivot on the basin. -/
theorem qbCertMS_exists_equilibrium_with_pivot_floor :
    ∃ E : qbParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Set.Icc (1/10 : ℝ) 1,
        (1/10 : ℝ) ≤ qbParams.dynamicTopRealizedRule E.V_S E.α x := by
  obtain ⟨E, _, _, hG1, _, _⟩ :=
    qbCertCertificateMS.three_goals_local_MS_generalF (p := qbParams) quadBumpF_hF_top
  refine ⟨E, fun x hx => ?_⟩
  have hx' : x ∈ Set.Icc (max qbCertCertificateMS.xT qbCertCertificateMS.xS) 1 := by
    rw [qbCertCertificateMS_xT, qbCertCertificateMS_xS, max_self]
    exact hx
  have h := (hG1 x hx').2.1 0
  rw [qbCertCertificateMS_xT, qbCertCertificateMS_xS, max_self] at h
  unfold Params.dynamicTopLockInSanctionsF at h
  simpa using h

/-- **(1) Any episode that ends in the basin is followed by no endogenous
exit**, at the non-affine witness. -/
theorem qbCertMS_finite_episode_nonexit :
    ∃ E : qbParams.FeedbackStackelbergEquilibriumTop,
      ∀ (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ),
        qbParams.episodePath u x₀ T ∈ Set.Icc (1/10 : ℝ) 1 →
        (∀ n, qbParams.splicedPath E.V_S E.α u T x₀ (T + n) ∈ Set.Icc (1/10 : ℝ) 1) ∧
        (∀ n, (1/10 : ℝ) ≤ qbParams.splicedSanction E.V_S E.α u T x₀ (T + n)) ∧
        (∀ q, q < (1/10 : ℝ) →
          ∀ n, ¬ qbParams.splicedSanction E.V_S E.α u T x₀ (T + n) ≤ q) := by
  obtain ⟨E, hWeak⟩ := qbCertMS_exists_equilibrium_with_pivot_floor
  refine ⟨E, fun u T x₀ hT => ?_⟩
  exact qbParams.equilibriumTop_post_episode_nonexit_generalF E u T x₀
    (qbParams.corner_of_pivot_le_floor le_rfl) hWeak hT

/-- **(2) A maximal episode of the canonical length, then no endogenous exit**,
at the non-affine witness, from every feasible start. -/
theorem qbCertMS_fullShock_episode_nonexit :
    ∃ E : qbParams.FeedbackStackelbergEquilibriumTop,
      ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ T, qbParams.fullShockEntryHorizon (1/10) ≤ T →
        (∀ n, qbParams.splicedPath E.V_S E.α (fun _ => 1) T x₀ (T + n)
          ∈ Set.Icc (1/10 : ℝ) 1) ∧
        (∀ n, (1/10 : ℝ) ≤ qbParams.splicedSanction E.V_S E.α (fun _ => 1) T x₀ (T + n)) ∧
        (∀ q, q < (1/10 : ℝ) →
          ∀ n, ¬ qbParams.splicedSanction E.V_S E.α (fun _ => 1) T x₀ (T + n) ≤ q) := by
  obtain ⟨E, hWeak⟩ := qbCertMS_exists_equilibrium_with_pivot_floor
  refine ⟨E, fun x₀ hx₀ T hT => ?_⟩
  exact qbParams.equilibriumTop_fullShock_episode_nonexit_generalF E qbParams_strictAdjustment
    (by norm_num) (qbParams.corner_of_pivot_le_floor le_rfl) hWeak hx₀ hT

/-- **(3) A non-maximal episode held at or above `h > 1/10` for the derived
horizon, then no endogenous exit**, at the non-affine witness. -/
theorem qbCertMS_highEpisode_nonexit :
    ∃ E : qbParams.FeedbackStackelbergEquilibriumTop,
      ∀ h : ℝ, (1/10 : ℝ) < h → h ≤ 1 →
      ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (0 : ℝ) 1) →
      ∀ T : ℕ, (∀ n < T, h ≤ u n) → qbParams.highEpisodeHorizon h (1/10) ≤ T →
      ∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
        (∀ n, qbParams.splicedPath E.V_S E.α u T x₀ (T + n) ∈ Set.Icc (1/10 : ℝ) 1) ∧
        (∀ n, (1/10 : ℝ) ≤ qbParams.splicedSanction E.V_S E.α u T x₀ (T + n)) ∧
        (∀ q, q < (1/10 : ℝ) →
          ∀ n, ¬ qbParams.splicedSanction E.V_S E.α u T x₀ (T + n) ≤ q) := by
  obtain ⟨E, hWeak⟩ := qbCertMS_exists_equilibrium_with_pivot_floor
  refine ⟨E, fun h hh0 hh1 u hu_mem T hu hT x₀ hx₀ => ?_⟩
  exact qbParams.equilibriumTop_highEpisode_nonexit_generalF E qbParams_strictAdjustment
    (by norm_num) hh0 hh1 (qbParams.corner_of_pivot_le_floor le_rfl) hWeak hu_mem hu hT hx₀

/-! ## Rule 10 — axiom inventory -/

#print axioms Sanctions.Examples.qbCertMS_finite_episode_nonexit
#print axioms Sanctions.Examples.qbCertMS_fullShock_episode_nonexit
#print axioms Sanctions.Examples.qbCertMS_highEpisode_nonexit

end Examples
end Sanctions
