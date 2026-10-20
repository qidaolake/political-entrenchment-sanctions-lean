/-
Sanctions/Examples/SymbolicCertifiedFamilyGeneralFPersistence.lean

**Primitive persistence for the general-`F` symbolic family (2026-08-09).**

`certificateMS` needs a side condition the structure does not carry — a
strictly interior basin bottom `0 < x̄` — so the MS route certifies only
*some* admissible members. Tracing what it pays for (see
`Theory/Certificates/PersistenceCertificate.lean`) shows it is not needed
for persistence: the strict pivot buys finite shock entry.

**Correction (2026-10-06, plan item BG3.7).** `certificateMS` used to need a
second side condition, the strict placation margin `u₀ + r < k`, which this
banner described as buying the myopic comparison. It does not: the myopic
ceiling closes from the structure's non-strict `hk` and the feasibility of
`σ` (`canonical_myopic_ceiling`), and the constructor no longer takes it.

## READ THIS BEFORE CLASSIFYING ANYTHING IN THIS FILE (audit note)

**The results here are universals over a family, not witness instances.** They
are quantified over `(E : SymbolicEconomy)` — every admissible member — so they
license universal statements about the family, and Rule 9's "a witness proves
only existence" restriction does **not** apply to them.

The file sits under `Examples/` because the family fixes a *functional form*
(`symU_S q u₀ k r w x a s = -(q/2)s² + s(u₀ - k·a + r·x) + w·x`, and its
Target counterpart), not because its theorems are point checks. Rule 19 keeps
`Theory/` for statements over an arbitrary `Params`; a nine-coefficient algebraic
family is narrower than that, so `Examples/` is the correct home and the file is
deliberately not moved.

This banner exists because the filing has already misled an audit. A 2026-08-16
review classified `prop:equilibrium-patience-feedback` as a paper universal
backed only by a witness, having found the `eeCertB_*` numbers cited in the
formalization map and not the `symbolic_*` siblings here. The paper was right and
the audit was wrong. If you are deciding what a paper claim rests on, grep this
file before concluding that a family-level claim has only witness backing.

So the family's persistence theorem takes **no arguments at all**. Given
only the structure — inequalities among payoff coefficients, discount
factors, and transition chord rates — an equilibrium exists in the
certified carriers and its realised path never leaves the high basin.

**The persistence core (plan item BJ4.4, 2026-10-07).** The theorem is proved
on `SymbolicEconomyFPersist`, the family without the Target's conditions
`0 ≤ n`, `ℓ ≤ c − n` and the loss-offset margin, which keeps only `0 ≤ n + v`
on the Target side. `SymbolicEconomyF.persistence_generalF` (headline row 30)
is the one-line corollary through `toPersist`, with its statement unchanged.
The core is strictly larger: `wobbleEconPersist` is a core member whose Target
sanction pain is too large for the loss offset, so it is no `SymbolicEconomyF`
(`wobbleEconPersist_not_toPersist`), and persistence holds there too.

**No curvature bound (plan item BJ4.3, 2026-10-08).** The family no longer
carries an upper sanction chord, curvature ceilings or a curvature margin, so
persistence holds for strongly curved transitions, including the wobble file's
own `wobbleF (1/2) (1/10)` (`wobbleEconFHalfTenth_persistence`). The Sender
carrier is the gain ball alone, so the conclusion `Eq.V_S ∈ E.carrierS` no
longer contains the Riccati semiconcavity clause; `eq_V_S_semiconcave` and
`persistence_generalF_semiconcave` recover it from a corner-section curvature
bound supplied as a hypothesis.

**The symbolic-family proposition on the general family (plan item BJ4.6).**
P4 restates clauses (ii)–(iii) of `prop:symbolic-family` for every member:
an equilibrium in the closed-form carriers, the MS certificate whenever the
basin bottom is strictly interior, and maximal regime separation against the
family's own optimised myopic comparator, with no side condition.

This file used to exhibit `wobbleEconF` as a member the `certificateMS`
route could not certify, because it sits exactly on `u₀ + r = k`. Since plan
item BG3.7 that claim is false: `wobbleEconF` has `x̄ = 1/2 > 0`, and
`wobbleEconF_certificateMS` below inhabits the MS certificate there. It now
witnesses the other strictness — that dropping the placation margin from
`certificateMS` was a genuine generalisation
(`wobbleEconF_MS_certified_without_strict_placation`). What the persistence
route still saves over the MS route is the strict pivot `0 < x̄`.

## What this theorem is, and what it is not

It is a **corner** persistence theorem. The certified equilibrium realises
the maximal sanction at every feasible state, so the monotone-sanction
conclusion holds flatly rather than through a state-dependent ratchet.
Primitive persistence over a general transition is established; a
nontrivial interior ratchet from primitives is not, and remains open.

## Rule compliance

**Rule 5.** The parametric theorem is `persistence_generalF`, universal
over `SymbolicEconomyF`; every witness below is a one-line corollary.

**Rule 9.** The witnesses discharge non-vacuity of the persistence
certificate and, in `wobbleEconF_MS_certified_without_strict_placation`,
the strictness of the BG3.7 relaxation of `certificateMS`. They license
existence and refutation only.

**Rule 22.** The trajectory is evolved by `E.F`, and the exhibited
witnesses are provably non-affine.
-/

import Sanctions.Examples.SymbolicCertifiedFamilyGeneralFRecovery
import Sanctions.Theory.Certificates.PersistenceCertificate

namespace Sanctions

namespace Examples

open Set AbstractGame

noncomputable section

namespace SymbolicEconomyFPersist

variable (E : SymbolicEconomyFPersist)

/-! ### P1 — the argument-free persistence certificate, on the core -/

/-- **Every member of the persistence core carries a persistence certificate**
(plan item BJ4.4).

Identical to `certificateMS` on the fields both share, minus the Target
combined chord, the myopic ceiling, and the strict pivot — which is
exactly why it needs no arguments. Note `hxT_mem` uses the structure's
own non-strict `hxb0 : 0 ≤ x̄`, where `certificateMS` had to be handed
`0 < x̄`. On the Target side it reads only `0 < ℓ` and `0 ≤ n + v`. General
in `F`. -/
def persistenceCertificate :
    E.toParams.StandardCompliancePersistenceCertificate where
  D := E.valueClass
  h_inv := E.valueClass_IsInvariant
  β_T := E.βT
  β_S := E.βS
  L_TS := 0
  L_ST := 0
  hβ_T_nn := E.hβT0
  hβ_S_nn := E.hβS0
  hL_TS_nn := le_refl 0
  hL_ST_nn := le_refl 0
  hT_T_op := E.hT_T_op (E.valueClass_IsInvariant)
  hT_S_op := E.hT_S_op (E.valueClass_IsInvariant)
  hsuff_T := by simpa using E.hβT1
  hsuff_S := by simpa using E.hβS1
  xT := E.xb
  xS := E.xb
  hxT_mem := ⟨E.hxb0, E.xb_le_one⟩
  hxS_mem := ⟨E.hxb0, E.xb_le_one⟩
  h_stage_sender_strictMono := E.h_stage_sender_strictMonoOn
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
      (E.hSC V_T V_S)
  hV_S_mono_carrier := fun _ hV_S =>
    Sanctions.AbstractGame.Params.monotone_of_mem_valLipGainBall
      E.gS_pos.le hV_S

/-! ### P2 — primitive persistence, no arguments -/

/-- **Primitive general-`F` persistence on the persistence core** (plan item
BJ4.4).

For every member of the core: a forward-looking feedback Stackelberg
equilibrium exists in the certified carriers, and from every start in the high
basin the political state remains in the basin, the realised sanction never
falls below the basin pivot, and the realised sanction sequence is
non-decreasing. Compared with `SymbolicEconomyF.persistence_generalF`, the
Target's conditions `0 ≤ n`, `ℓ ≤ c − n` and the loss offset are dropped; only
`0 ≤ n + v` (the Target's corner payoff does not fall with the state) is kept.
General in `F`. -/
theorem persistence_generalF :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT
      ∧ Eq.V_S ∈ E.carrierS
      ∧ ∀ x₀ ∈ Set.Icc E.xb 1,
          (∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc E.xb 1) ∧
          (∀ n, E.xb ≤ E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀ n) ∧
          Monotone (E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀) := by
  obtain ⟨Eq, hVT, hVS, hpath⟩ :=
    E.persistenceCertificate.exists_persistent_equilibrium_generalF
  have hmax : max E.persistenceCertificate.xT E.persistenceCertificate.xS
      = E.xb := max_self E.xb
  rw [hmax] at hpath
  exact ⟨Eq, hVT, hVS, hpath⟩

/-- **Primitive persistence on the core, with the realised sanction pinned
exactly** at the full sanction `σ_n = 1`. General in `F`. -/
theorem persistence_generalF_corner :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT
      ∧ Eq.V_S ∈ E.carrierS
      ∧ ∀ x₀ ∈ Set.Icc E.xb 1,
          (∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc E.xb 1) ∧
          (∀ n, E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀ n = 1) ∧
          (∀ n, E.xb ≤ E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀ n) ∧
          Monotone (E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀) := by
  obtain ⟨Eq, hVT, hVS, hpath⟩ := E.persistence_generalF
  refine ⟨Eq, hVT, hVS, fun x₀ hx₀ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hpath x₀ hx₀
  have hfeas : ∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
      ∈ Sanctions.S := fun n => ⟨le_trans E.hxb0 (h1 n).1, (h1 n).2⟩
  exact ⟨h1, fun n => E.σ_dyn_top_eq_one hVS (hfeas n) (Eq.α_mem _ (hfeas n)),
    h2, h3⟩

end SymbolicEconomyFPersist

namespace SymbolicEconomyF

variable (E : SymbolicEconomyF)

/-- **Every admissible member carries a persistence certificate**: the core's
certificate at `E.toPersist`, whose `Params` is `E`'s own
(`toPersist_toParams`). General in `F`. -/
def persistenceCertificate : E.toParams.StandardCompliancePersistenceCertificate :=
  E.toPersist.persistenceCertificate

/-- **Primitive general-`F` persistence for the symbolic family.**

For every admissible member: a forward-looking feedback Stackelberg
equilibrium exists in the certified carriers, and from every start in
the high basin the political state remains in the basin, the realised
sanction never falls below the basin pivot, and the realised sanction
sequence is non-decreasing.

No equilibrium, value function, policy, single-crossing condition,
sanction floor, or path property appears in the hypotheses — all are
constructed or derived from coefficient and transition inequalities. The
realised recursion is `x_{t+1} = F(x_t, σ_t)` for the member's own `F`,
which may be genuinely non-affine.

Since plan item BJ4.4 this is the one-line corollary of the core theorem
`SymbolicEconomyFPersist.persistence_generalF` at `E.toPersist`; the statement
is unchanged (headline row 30).

**Plan item BJ4.3 (2026-10-08).** The structure lost its curvature block
(`dhi`, `M_F`, `M_state`, `hShi`, `hFsc`, `hGsc`, `hMF0`, `hMstate0`, `hCurv`),
so the theorem now covers every member with a lower sanction chord and a
two-sided corner band, however curved. The statement text is unchanged, but
`E.carrierS` is now the gain ball alone: the conjunct `Eq.V_S ∈ E.carrierS` no
longer includes semiconcavity through the clip at the Riccati modulus. That
conjunct is recovered, given a corner-section curvature bound, by
`persistence_generalF_semiconcave`. General in `F`. -/
theorem persistence_generalF :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT
      ∧ Eq.V_S ∈ E.carrierS
      ∧ ∀ x₀ ∈ Set.Icc E.xb 1,
          (∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc E.xb 1) ∧
          (∀ n, E.xb ≤ E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀ n) ∧
          Monotone (E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀) :=
  E.toPersist.persistence_generalF

/-- **Primitive persistence, with the realised sanction pinned exactly.**

Strengthens the sanction floor of `persistence_generalF` to the identity
`σ_n = 1`: the certified equilibrium sanctions maximally at every date.
This is what makes the monotone conclusion flat, and is the honest
statement of the corner limitation. -/
theorem persistence_generalF_corner :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT
      ∧ Eq.V_S ∈ E.carrierS
      ∧ ∀ x₀ ∈ Set.Icc E.xb 1,
          (∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc E.xb 1) ∧
          (∀ n, E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀ n = 1) ∧
          (∀ n, E.xb ≤ E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀ n) ∧
          Monotone (E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀) := by
  obtain ⟨Eq, hVT, hVS, hpath⟩ := E.persistence_generalF
  refine ⟨Eq, hVT, hVS, fun x₀ hx₀ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hpath x₀ hx₀
  have hfeas : ∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
      ∈ Sanctions.S := fun n => ⟨le_trans E.hxb0 (h1 n).1, (h1 n).2⟩
  exact ⟨h1, fun n => E.realizedRule_eq_one Eq hVS (hfeas n), h2, h3⟩

/-! ### P2b — the semiconcavity conclusion, from curvature data as hypotheses

Plan item BJ4.3 (2026-10-08) deleted the structure's curvature block and the
carrier's semiconcavity clause. The clause is not lost: whenever the corner
section `y ↦ F(y,1)` is semiconcave with some modulus `M_state ≥ 0`, every
equilibrium Sender value in the carrier is semiconcave through the clip at the
Riccati modulus `Σ_V = (β_S·K_S·M_state)/(1 − β_S·ghi²)`. The data
`(M_state, hGsc)` are theorem hypotheses here, not fields; the sanction-direction
curvature, the upper sanction chord and the curvature margin are not needed at
all. -/

/-- **Every carrier equilibrium's Sender value is semiconcave, given the corner
section's curvature** (plan item BJ4.3, 2026-10-08).

If the corner section is semiconcave on `[0,1]` with modulus `M_state ≥ 0`,
then for any top-selector equilibrium whose Sender value lies in the carrier,
that value is semiconcave through the clip at the Riccati modulus
`Σ_V = (β_S·K_S·M_state)/(1 − β_S·ghi²)`. Proof: the semiconcave sub-carrier
`C = carrier ∩ {semiconcave at Σ_V}` is closed, nonempty and mapped into itself
by the corner Bellman step (`carrierS_semiconcave_invariant`), which contracts
towards the equilibrium value at rate `β_S` (`eq_V_S_bellman`); so the distance
from the equilibrium value to `C` is at most `β_S` times itself, hence zero, and
`C` is closed. General in `F`. -/
theorem eq_V_S_semiconcave {Mstate : ℝ} (hMstate0 : 0 ≤ Mstate)
    (hGsc : Sanctions.Semiconcave.SemiconcaveOnSet (fun y => E.F y 1)
      (Set.Icc (0 : ℝ) 1) Mstate)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS : Eq.V_S ∈ E.carrierS) :
    Sanctions.Semiconcave.SemiconcaveOnSet (fun z => Eq.V_S (Sanctions.clipS' z))
      (Set.Icc (0 : ℝ) 1)
      (Sanctions.Semiconcave.bellmanSemiconcaveConstant E.βS E.ghi 0 E.KS Mstate) := by
  set σ := Sanctions.Semiconcave.bellmanSemiconcaveConstant E.βS E.ghi 0 E.KS Mstate
    with hσ
  set C : Set AbstractGame.Params.Val := E.carrierS ∩
    {V | Sanctions.Semiconcave.SemiconcaveOnSet (fun z => V (Sanctions.clipS' z))
      (Set.Icc (0 : ℝ) 1) σ} with hC
  have hCc : IsClosed C :=
    E.carrierS_isClosed.inter (SymbolicEconomyF.semiconcaveClause_isClosed σ)
  have hCne : C.Nonempty :=
    ⟨affineBCF E.gS,
      SymbolicEconomyF.affineBCF_mem_gainBall_cone E.gS_pos.le E.gS_le_KS E.gS_le_MS,
      SymbolicEconomyF.affineBCF_clip_semiconcave (E.semiconcaveModulus_nn hMstate0)⟩
  -- One corner Bellman step maps `C` into `C` and contracts towards `Eq.V_S`.
  have hstep : ∀ W ∈ C, ∃ W' ∈ C, dist Eq.V_S W' ≤ E.βS * dist Eq.V_S W := by
    intro W hW
    refine ⟨E.toParams.bellmanS_BCF (fun _ => 0) continuous_const W, ⟨?_, ?_⟩, ?_⟩
    · exact E.carrierS_invariant hW.1 (fun y => E.bellmanS_image hW.1 y)
    · exact E.carrierS_semiconcave_invariant hMstate0 hGsc hW.1 hW.2
        (fun y => E.bellmanS_image hW.1 y)
    · have hβ0 := E.hβS0
      rw [BoundedContinuousFunction.dist_le (mul_nonneg hβ0 dist_nonneg)]
      intro y
      rw [E.eq_V_S_bellman Eq hVS y, E.bellmanS_image hW.1 y, Real.dist_eq,
        show E.stageS0 + E.stageSlopeS * y.val
              + E.βS * Eq.V_S (Sanctions.clipS' (E.F y.val 1))
            - (E.stageS0 + E.stageSlopeS * y.val
              + E.βS * W (Sanctions.clipS' (E.F y.val 1)))
          = E.βS * (Eq.V_S (Sanctions.clipS' (E.F y.val 1))
              - W (Sanctions.clipS' (E.F y.val 1))) by ring,
        abs_mul, abs_of_nonneg hβ0, ← Real.dist_eq]
      exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.dist_coe_le_dist _) hβ0
  -- The distance from `Eq.V_S` to `C` is at most `β_S` times itself.
  have hmem : Eq.V_S ∈ C := by
    rw [hCc.mem_iff_infDist_zero hCne]
    set d := Metric.infDist Eq.V_S C with hd
    have hd0 : 0 ≤ d := Metric.infDist_nonneg
    have hle : d ≤ E.βS * d := by
      by_contra hcon
      rw [not_le] at hcon
      set ε := (d - E.βS * d) / 2 with hεdef
      have hε : 0 < ε := by rw [hεdef]; linarith
      obtain ⟨W, hW, hWd⟩ := (Metric.infDist_lt_iff hCne).mp (lt_add_of_pos_right d hε)
      obtain ⟨W', hW', hW'd⟩ := hstep W hW
      have h1 : d ≤ dist Eq.V_S W' := Metric.infDist_le_dist_of_mem hW'
      have h2 : E.βS * dist Eq.V_S W ≤ E.βS * (d + ε) :=
        mul_le_mul_of_nonneg_left hWd.le E.hβS0
      have h3 : E.βS * ε ≤ ε := by nlinarith [E.hβS1, hε]
      linarith [mul_add E.βS d ε]
    exact le_antisymm (by nlinarith [E.hβS1, hd0, hle]) hd0
  exact hmem.2

/-- **Primitive persistence with the semiconcavity conclusion restored** (plan
item BJ4.3, 2026-10-08).

`persistence_generalF` together with semiconcavity of the equilibrium Sender
value through the clip at the Riccati modulus
`Σ_V = (β_S·K_S·M_state)/(1 − β_S·ghi²)`, for any corner-section curvature bound
`M_state ≥ 0` supplied as a hypothesis (`hGsc`). With the curvature data of a
pre-BJ4.3 member, `Eq.V_S ∈ E.carrierS` plus this clause is exactly the old
carrier membership, so no conclusion is lost by deleting the curvature block.
Only the corner-section curvature is needed: the sanction-direction curvature,
the upper sanction chord and the curvature margin are not. General in `F`. -/
theorem persistence_generalF_semiconcave {Mstate : ℝ} (hMstate0 : 0 ≤ Mstate)
    (hGsc : Sanctions.Semiconcave.SemiconcaveOnSet (fun y => E.F y 1)
      (Set.Icc (0 : ℝ) 1) Mstate) :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT
      ∧ Eq.V_S ∈ E.carrierS
      ∧ Sanctions.Semiconcave.SemiconcaveOnSet (fun z => Eq.V_S (Sanctions.clipS' z))
          (Set.Icc (0 : ℝ) 1)
          (Sanctions.Semiconcave.bellmanSemiconcaveConstant E.βS E.ghi 0 E.KS Mstate)
      ∧ ∀ x₀ ∈ Set.Icc E.xb 1,
          (∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc E.xb 1) ∧
          (∀ n, E.xb ≤ E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀ n) ∧
          Monotone (E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀) := by
  obtain ⟨Eq, hVT, hVS, hpath⟩ := E.persistence_generalF
  exact ⟨Eq, hVT, hVS, E.eq_V_S_semiconcave hMstate0 hGsc Eq hVS, hpath⟩

/-! ### P4 — the symbolic-family proposition on the general family (BJ4.6)

`prop:symbolic-family` is stated on the affine family. Clauses (ii)–(iii) hold
on the general family as follows, re-verified here (plan item BJ4.6):

* an equilibrium in carriers with closed-form constants exists at **every**
  member (`persistence_generalF`), with `K_S = (r + w)/(1 − β_S·ghi)`,
  `g_S = (r + w)/(1 − β_S·glo)` and `g_T = (n + v)/(1 − β_T·ghi)`;
* the MS / general-`F` certificate exists whenever the basin bottom is strictly
  interior (`certificateMS`); the strict placation margin the proposition still
  names is not needed (plan item BG3.7);
* maximal regime separation holds against the family's own optimised myopic
  comparator `symMyopic` at every member, with no side condition
  (`regime_separation_symMyopic`); against the canonical comparator it needs
  a strictly interior basin bottom `0 < x̄` and `u₀ + r < k` (`regime_separation`).

The legacy-form certificate of clause (ii) has no general-family counterpart:
its consequences hard-require the affine law, so that clause stays
affine-only. The affine closed forms are the members `A.toF`, where
`glo = ghi = 1 − δ`. -/

/-- **Maximal regime separation against the family's own myopic comparator,
at every member, with no side condition.** There is an equilibrium in the
carriers whose realised sanction is the full sanction at every feasible state,
while the family's optimised myopic regime (`symMyopic`) imposes no sanction
at all. Neither a strictly interior basin bottom nor a strict placation margin
is needed: the equilibrium comes from the persistence route, and the myopic
comparator zeroes the static sanction by construction. General in `F`; the
general-family form of the affine `SymbolicEconomy.regime_separation`. -/
theorem regime_separation_symMyopic :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT ∧ Eq.V_S ∈ E.carrierS
      ∧ ∀ x ∈ Sanctions.S,
          E.toParams.myopicEquilibriumRule E.symMyopic x = 0
          ∧ E.toParams.dynamicEquilibriumRule Eq x = 1 := by
  obtain ⟨Eq, hVT, hVS, _⟩ := E.persistence_generalF
  exact ⟨Eq, hVT, hVS, fun x hx =>
    ⟨E.symMyopic_rule_eq_zero x, E.realizedRule_eq_one Eq hVS hx⟩⟩

/-- **Directional sign witness (Rule 16a)** for `regime_separation_symMyopic`:
the forward-looking regime's realised sanction strictly exceeds the family's
myopic regime's at every feasible state, at every member. General in `F`. -/
theorem regime_separation_symMyopic_strict :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.S,
        E.toParams.myopicEquilibriumRule E.symMyopic x
          < E.toParams.dynamicEquilibriumRule Eq x := by
  obtain ⟨Eq, _hVT, _hVS, h⟩ := E.regime_separation_symMyopic
  refine ⟨Eq, fun x hx => ?_⟩
  rw [(h x hx).1, (h x hx).2]
  exact zero_lt_one

/-- **Clauses (ii)–(iii) of `prop:symbolic-family`, on the general family**
(plan item BJ4.6). At every admissible member: the carrier constants are the
closed forms `K_S = (r + w)/(1 − β_S·ghi)`, `g_S = (r + w)/(1 − β_S·glo)`,
`g_T = (n + v)/(1 − β_T·ghi)`; an equilibrium lies in those carriers and
realises the full sanction at every feasible state while the family's own
optimised myopic regime realises none; and a strictly interior basin bottom
gives the MS / general-`F` certificate. General in `F`. -/
theorem symbolic_family_generalF :
    E.KS = (E.r + E.w) / (1 - E.βS * E.ghi)
    ∧ E.gS = (E.r + E.w) / (1 - E.βS * E.glo)
    ∧ E.gT = (E.n + E.v) / (1 - E.βT * E.ghi)
    ∧ (∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
        Eq.V_T ∈ E.carrierT ∧ Eq.V_S ∈ E.carrierS
        ∧ ∀ x ∈ Sanctions.S,
            E.toParams.myopicEquilibriumRule E.symMyopic x = 0
            ∧ E.toParams.dynamicEquilibriumRule Eq x = 1)
    ∧ (0 < E.xb → Nonempty E.toParams.StandardComplianceLocalCoreCertificate_MS) :=
  ⟨rfl, rfl, rfl, E.regime_separation_symMyopic, fun h => ⟨E.certificateMS h⟩⟩

end SymbolicEconomyF

/-! ### P3 — non-vacuity, and the strictness of the BG3.7 relaxation

`wobbleEconMS` carries both certificates. So, since plan item BG3.7
(2026-10-06), does `wobbleEconF`: it sits exactly on `u₀ + r = k = 3`, so it
fails the strict placation margin that `certificateMS` used to require, but
the constructor now needs only `0 < x̄`, and `x̄ = 1/2` there. Earlier
versions of this section said the `certificateMS` route was closed to
`wobbleEconF`; that is no longer true, and `wobbleEconF_certificateMS` below
is the witness. `wobbleEconF10` also sits on `u₀ + r = k` and is certified
the same way (`wobbleEconF10_certificateMS`). `wobbleEconFHalfTenth`, at the
wobble file's own published transition, persists as well
(`wobbleEconFHalfTenth_persistence`; plan item BJ4.3). -/

/-- Persistence at the certificate-bearing non-affine witness. -/
theorem wobbleEconMS_persistence :
    ∃ Eq : wobbleEconMS.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ wobbleEconMS.carrierT
      ∧ Eq.V_S ∈ wobbleEconMS.carrierS
      ∧ ∀ x₀ ∈ Set.Icc wobbleEconMS.xb 1,
          (∀ n, wobbleEconMS.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc wobbleEconMS.xb 1) ∧
          (∀ n, wobbleEconMS.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀ n = 1) ∧
          (∀ n, wobbleEconMS.xb ≤ wobbleEconMS.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀ n) ∧
          Monotone (wobbleEconMS.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀) :=
  wobbleEconMS.persistence_generalF_corner

/-- **`wobbleEconF` sits exactly on the placation boundary.**
`u₀ + r = k`, so the strict placation margin `u₀ + r < k` fails.

**Scope (Rule 9 / Rule 11).** This refutes the strict placation margin at
this economy, and nothing more. It never refuted the existence of an MS
certificate here, and since plan item BG3.7 it no longer refutes the
hypothesis of the `certificateMS` constructor either: the margin fed only
`hMyoCeiling`, which `canonical_myopic_ceiling` now discharges from the
weaker bound `σ x (α_myo x) ≤ max x (max xT xS)` that the field asks for.
`wobbleEconF_certificateMS` is the certificate. The margin is still a
hypothesis of the regime-separation theorems, which assert a zero myopic
sanction at the top state. Prose citing this theorem must say "fails the
strict placation margin", never "has no certificate". -/
theorem wobbleEconF_not_strict_placation :
    ¬ (wobbleEconF.u₀ + wobbleEconF.r < wobbleEconF.k) := by
  show ¬ ((2 : ℝ) + 1 < 3)
  norm_num

/-- **…and is certified for persistence.** This used to be described as
what the debundling buys, a member the bundled route could not certify.
Since plan item BG3.7 the bundled MS route certifies `wobbleEconF` too
(`wobbleEconF_certificateMS`); what the persistence route still saves is
the strict pivot `0 < x̄`, which this member happens to satisfy. -/
theorem wobbleEconF_persistence :
    ∃ Eq : wobbleEconF.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ wobbleEconF.carrierT
      ∧ Eq.V_S ∈ wobbleEconF.carrierS
      ∧ ∀ x₀ ∈ Set.Icc wobbleEconF.xb 1,
          (∀ n, wobbleEconF.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc wobbleEconF.xb 1) ∧
          (∀ n, wobbleEconF.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀ n = 1) ∧
          (∀ n, wobbleEconF.xb ≤ wobbleEconF.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀ n) ∧
          Monotone (wobbleEconF.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀) :=
  wobbleEconF.persistence_generalF_corner

/-- **`wobbleEconF` carries the MS / general-`F` certificate (plan item
BG3.7).** General in `F`: the member's transition is the non-affine
`wobbleF (1/2) (1/100)`. The constructor needs only `0 < x̄`, and
`x̄ = 1/2` here; the strict placation margin, which this member fails
(`wobbleEconF_not_strict_placation`), is no longer an argument. -/
def wobbleEconF_certificateMS :
    wobbleEconF.toParams.StandardComplianceLocalCoreCertificate_MS :=
  wobbleEconF.certificateMS (by change (0 : ℝ) < 1 / 2; norm_num)

/-- **Dropping the strict placation margin from `certificateMS` was a strict
generalisation.** `wobbleEconF` fails `u₀ + r < k`, which the constructor
used to require, and still carries an MS certificate. General in `F`. -/
theorem wobbleEconF_MS_certified_without_strict_placation :
    ¬ (wobbleEconF.u₀ + wobbleEconF.r < wobbleEconF.k)
      ∧ Nonempty wobbleEconF.toParams.StandardComplianceLocalCoreCertificate_MS :=
  ⟨wobbleEconF_not_strict_placation, ⟨wobbleEconF_certificateMS⟩⟩

/-- The same at the ten-times-stronger bend. -/
theorem wobbleEconF10_persistence :
    ∃ Eq : wobbleEconF10.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ wobbleEconF10.carrierT
      ∧ Eq.V_S ∈ wobbleEconF10.carrierS
      ∧ ∀ x₀ ∈ Set.Icc wobbleEconF10.xb 1,
          (∀ n, wobbleEconF10.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc wobbleEconF10.xb 1) ∧
          (∀ n, wobbleEconF10.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀ n = 1) ∧
          (∀ n, wobbleEconF10.xb ≤
                  wobbleEconF10.toParams.dynamicTopLockInSanctionsF
                    Eq.V_S Eq.α x₀ n) ∧
          Monotone (wobbleEconF10.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀) :=
  wobbleEconF10.persistence_generalF_corner

/-- **Persistence at the wobble file's own published transition** (plan item
BJ4.3, 2026-10-08). At `wobbleEconFHalfTenth`, whose transition is
`wobbleF (1/2) (1/10)`, an equilibrium exists in the carriers and from every
start in the high basin the state stays in the basin under the full sanction at
every date. Under the deleted curvature block no member had this transition.
General in `F`: the transition is the non-affine `wobbleF`. -/
theorem wobbleEconFHalfTenth_persistence :
    ∃ Eq : wobbleEconFHalfTenth.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ wobbleEconFHalfTenth.carrierT
      ∧ Eq.V_S ∈ wobbleEconFHalfTenth.carrierS
      ∧ ∀ x₀ ∈ Set.Icc wobbleEconFHalfTenth.xb 1,
          (∀ n, wobbleEconFHalfTenth.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc wobbleEconFHalfTenth.xb 1) ∧
          (∀ n, wobbleEconFHalfTenth.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀ n = 1) ∧
          (∀ n, wobbleEconFHalfTenth.xb ≤
                  wobbleEconFHalfTenth.toParams.dynamicTopLockInSanctionsF
                    Eq.V_S Eq.α x₀ n) ∧
          Monotone (wobbleEconFHalfTenth.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀) :=
  wobbleEconFHalfTenth.persistence_generalF_corner

/-- **`wobbleEconF10` carries the MS / general-`F` certificate too (plan item
BG3.7).** General in `F`: the transition is the non-affine
`wobbleF (3/4) (1/10)`. This member also sits on the placation boundary
(`u₀ + r = 1 + 1/4 = 5/4 = k`), so before BG3.7 the `certificateMS`
constructor did not apply to it either; it needs only `x̄ = 1/2 > 0`. -/
def wobbleEconF10_certificateMS :
    wobbleEconF10.toParams.StandardComplianceLocalCoreCertificate_MS :=
  wobbleEconF10.certificateMS (by change (0 : ℝ) < 1 / 2; norm_num)

/-! ### P5 — the persistence core is strictly larger than the family (BJ4.4)

`wobbleEconPersist` is `wobbleEconF` with the Target's sanction pain raised from
`c = 1` to `c = 100`. Everything the core reads is unchanged — the transition,
the Sender side, `ℓ = 1 > 0` and `n + v = 4 ≥ 0` — but the loss offset fails:
`(c − n·x̄)(1 − β_T·glo) = 76` against `β_T·dlo·(n + v) = 24/25`. So it is no
member of `SymbolicEconomyF`, and persistence holds there anyway. Economically:
once the Sender is implacable, complying costs the Target `ℓ` per unit and buys
nothing, so however much the sanctions hurt it stays defiant, and the regime
persists. Rule 9: an existence certificate for the strictness of the
relaxation, nothing more. -/

/-- **A member of the persistence core with a large Target sanction pain.** Same
non-affine transition `wobbleF (1/2) (1/100)` and payoff point as `wobbleEconF`,
except `c = 100`. The curvature-block fields were dropped with the core's (plan
item BJ4.3, 2026-10-08). -/
def wobbleEconPersist : SymbolicEconomyFPersist where
  F := wobbleF (1 / 2) (1 / 100)
  F_continuous := wobbleF_continuous _ _
  F_mono_x := wobbleF_mono_x (by norm_num) (by norm_num)
  F_mono_s := wobbleF_mono_s (by norm_num) (by norm_num)
  F_diag := wobbleF_diag _ _
  glo := 1 - 1 / 2 - 2 * (1 / 100)
  ghi := 1 - 1 / 2
  dlo := 1 / 2 - 2 * (1 / 100)
  hband := wobbleF_cornerStateChord (by norm_num)
  hSlo := wobbleF_sanctionLowerChord (by norm_num)
  hglo0 := by norm_num
  hghi1 := by norm_num
  hdlo0 := by norm_num
  δ := 1 / 2
  βS := 1 / 2
  βT := 1 / 2
  q := 1 / 2
  u₀ := 2
  k := 3
  r := 1
  w := 4
  ℓ := 1
  c := 100
  n := 0
  v := 4
  xb := 1 / 2
  hδ0 := by norm_num
  hδ1 := by norm_num
  hβS0 := by norm_num
  hβS1 := by norm_num
  hβT0 := by norm_num
  hβT1 := by norm_num
  hq := by norm_num
  hqr := by norm_num
  hu₀ := by norm_num
  hk := by norm_num
  hℓ := by norm_num
  hnv := by norm_num
  hxb0 := by norm_num
  hxb1 := by norm_num
  hCorner := by norm_num

/-- **The loss offset fails at `wobbleEconPersist`**: the Target's stage
sanction loss `(c − n·x̄)(1 − β_T·glo) = 76` is not covered by its discounted
continuation gain `β_T·dlo·(n + v) = 24/25`. -/
theorem wobbleEconPersist_not_TMargin :
    ¬ ((wobbleEconPersist.c - wobbleEconPersist.n * wobbleEconPersist.xb)
          * (1 - wobbleEconPersist.βT * wobbleEconPersist.glo)
        ≤ wobbleEconPersist.βT * wobbleEconPersist.dlo
          * (wobbleEconPersist.n + wobbleEconPersist.v)) := by
  change ¬ (((100 : ℝ) - 0 * (1 / 2)) * (1 - 1 / 2 * (1 - 1 / 2 - 2 * (1 / 100)))
      ≤ 1 / 2 * (1 / 2 - 2 * (1 / 100)) * (0 + 4))
  norm_num

/-- **`wobbleEconPersist` is not a member of `SymbolicEconomyF`**: no member of
the family maps to it under `toPersist`, because every member satisfies the
loss offset. So the persistence core strictly enlarges the family (plan item
BJ4.4). General in `F`. -/
theorem wobbleEconPersist_not_toPersist :
    ¬ ∃ E : SymbolicEconomyF, E.toPersist = wobbleEconPersist := by
  rintro ⟨E, h⟩
  apply wobbleEconPersist_not_TMargin
  rw [← h]
  exact E.hTMargin

/-- **Persistence at a member outside the family.** At `wobbleEconPersist` an
equilibrium exists in the carriers and, from every start in the high basin, the
state stays in the basin and the realised sanction is the full sanction at
every date. General in `F`: the transition is the non-affine `wobbleF`. -/
theorem wobbleEconPersist_persistence :
    ∃ Eq : wobbleEconPersist.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ wobbleEconPersist.carrierT
      ∧ Eq.V_S ∈ wobbleEconPersist.carrierS
      ∧ ∀ x₀ ∈ Set.Icc wobbleEconPersist.xb 1,
          (∀ n, wobbleEconPersist.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc wobbleEconPersist.xb 1) ∧
          (∀ n, wobbleEconPersist.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀ n = 1) ∧
          (∀ n, wobbleEconPersist.xb ≤
                  wobbleEconPersist.toParams.dynamicTopLockInSanctionsF
                    Eq.V_S Eq.α x₀ n) ∧
          Monotone (wobbleEconPersist.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀) :=
  wobbleEconPersist.persistence_generalF_corner

end

end Examples

end Sanctions

#print axioms Sanctions.Examples.SymbolicEconomyF.persistence_generalF
#print axioms Sanctions.Examples.SymbolicEconomyF.persistence_generalF_corner
#print axioms Sanctions.Examples.SymbolicEconomyF.eq_V_S_semiconcave
#print axioms Sanctions.Examples.SymbolicEconomyF.persistence_generalF_semiconcave
#print axioms Sanctions.Examples.wobbleEconFHalfTenth_persistence
#print axioms Sanctions.Examples.wobbleEconMS_persistence
#print axioms Sanctions.Examples.wobbleEconF_not_strict_placation
#print axioms Sanctions.Examples.wobbleEconF_certificateMS
#print axioms Sanctions.Examples.wobbleEconF_MS_certified_without_strict_placation
#print axioms Sanctions.Examples.wobbleEconF_persistence
#print axioms Sanctions.Examples.wobbleEconF10_persistence
#print axioms Sanctions.Examples.wobbleEconF10_certificateMS
#print axioms Sanctions.Examples.SymbolicEconomyFPersist.persistenceCertificate
#print axioms Sanctions.Examples.SymbolicEconomyFPersist.persistence_generalF
#print axioms Sanctions.Examples.SymbolicEconomyFPersist.persistence_generalF_corner
#print axioms Sanctions.Examples.SymbolicEconomyF.regime_separation_symMyopic
#print axioms Sanctions.Examples.SymbolicEconomyF.regime_separation_symMyopic_strict
#print axioms Sanctions.Examples.SymbolicEconomyF.symbolic_family_generalF
#print axioms Sanctions.Examples.wobbleEconPersist_not_TMargin
#print axioms Sanctions.Examples.wobbleEconPersist_not_toPersist
#print axioms Sanctions.Examples.wobbleEconPersist_persistence
