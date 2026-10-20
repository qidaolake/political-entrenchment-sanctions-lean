/-
Sanctions/Theory/Certificates/SenderPersistencePackage.lean

**The manuscript's P1–P3 + P5 package, without P4 (2026-08-09).**

`thm:persistence` in the manuscript is stated over five hypotheses and
says, in its discussion, that the Target combined chord P4 yields
conclusion (vi) while conclusions (i)–(iii) use P1–P3 and P5. The
formal counterpart of the theorem — `GeneralFPersistencePackage` and
`standardCompliance_persistence_generalF_from_package` — bundled all
five and converted them through `JointPreferenceBasinTop`, so the
division of labour the paper stated had no formal witness. A referee
comparing the two could reasonably have objected.

This file supplies the witness in the paper's own vocabulary.
`SenderPersistencePackage` is `GeneralFPersistencePackage` with the
`target_combined_chord` field deleted and nothing else changed, and
`standardCompliance_persistence_generalF_from_sender_package` delivers
conclusions (i)–(iii) from it over a general transition.

The economics of the separation: P5, the transition-adjusted sub-pivot
chord, says the Sender's stage gain from raising the sanction over the
sub-pivot range strictly exceeds the worst continuation loss its
carrier's Lipschitz bound permits. That is what puts the Sender's
greatest response at or above the pivot — the *level*. P3, interval
dominance after substituting the Target policy, is what makes that
response non-decreasing in the inherited state — the *direction*. Level
plus direction plus monotonicity of the transition give basin
invariance and non-decreasing sanctions. The Target's own preference
over sanctions is a separate economic fact; it is what makes the
mechanism two-sided, and it is conclusion (vi), not an input to the
path.

## Rule compliance

**Rule 3.** No new assumption. Every field is a field of
`GeneralFPersistencePackage` verbatim, and
`GeneralFPersistencePackage.toSenderPersistencePackage` exhibits the
projection; the `example` after it re-derives the existing paper-facing
persistence theorem through the slim route.

**Rule 22.** General `F` throughout — the transition enters only
through `F_mono_s` / `F_diag` / `F_mem` and the chord in P5.

**Round BJ1.3 (2026-10-07, author-approved re-pin of contract rows 272 and
360).** P5 is quantified on the basin `[max xT xS, 1]` only, and in pivot-star
form: at each basin state the stage gain of moving from a sub-pivot sanction up
to the pivot beats the worst continuation loss, one comparison per sanction,
always against the pivot. No *conclusion* of the persistence route needs the
pairwise comparison of two sub-pivot sanctions, or any state below the joint
basin: the Sender level only needs the pivot to beat every sub-pivot sanction
(`sender_high_argmax_exists_of_pivot_beats_subpivot`), and every persistence
conclusion is about basin states. The old *proofs* did read more (they went
through strict monotonicity below the pivot at every state of `[xS, 1]`), so
they were re-routed, and two projections had to change their statements:
`SenderPersistencePackage.toLocal` now returns the star chord instead of the
pairwise one, and `SenderPersistencePackage.static_response_ge_pivot`
(`SubpivotChordNecessity.lean`) now holds on the basin `[max xT xS, 1]` instead
of on `[xS, 1]`. When `xT > xS` the package no longer asks anything of the
Sender on `[xS, xT)`.
-/

import Sanctions.Theory.Certificates.StandardComplianceMain
import Sanctions.Theory.Basin.SenderPersistence

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The P4-free package -/

/-- **Sender persistence package: P1, P2, P3, P5.**

Exactly `GeneralFPersistencePackage` minus its `target_combined_chord`
field.

The Target is still very much present, and load-bearingly so: its value
lies in the carrier, and `α` is the carrier's policy selector at that
pair, which is what makes `α` the *equilibrium* policy rather than an
arbitrary function (Rule 1). `α` is then an argument of the Sender's
objective at every step below. What is absent — the single thing this
package does without — is any hypothesis constraining the Target's
*ranking over sanction levels*, which is P4. -/
structure SenderPersistencePackage
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
  /-- **P2** — every Sender carrier value is `K_S`-Lipschitz. -/
  sender_carrier_lipschitz :
    ∀ V_S ∈ D.carrier_S, ValueLipschitzWith V_S K_S
  /-- **P3** — interval dominance in `(s, x)` after substituting the
  carrier-parameterised Target policy: the *direction* input. -/
  sender_IDO_after_target_policy :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc (max xT xS) 1)
        (fun s x =>
          p.senderDynObjective V_S.val x
            (D.α_on V_T V_S x) s)
  /-- **P5** — the transition-adjusted sub-pivot chord: the *level*
  input. At every basin state, the Sender's stage gain from raising any
  sub-pivot sanction to the pivot `max x (max xT xS)` strictly exceeds the
  worst continuation loss its carrier's Lipschitz bound allows.

  Round BJ1.3 (2026-10-07): weakened from the pairwise chord over every
  sanction pair below the pivot at every state of `[xS, 1]` to this
  pivot-star form on the basin `[max xT xS, 1]` (the field of
  `GeneralFPersistencePackage` changed identically). General in `F`: the
  transition enters only through the successor-state distance. -/
  sender_subpivot_chord :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        ∀ s₁ ∈ Set.Ico (0 : ℝ) (max x (max xT xS)),
          p.β_S * K_S *
              dist (Sanctions.clipS' (p.F x s₁))
                   (Sanctions.clipS' (p.F x (max x (max xT xS))))
            < p.U_S x (D.α_on V_T V_S x) (max x (max xT xS)) -
                p.U_S x (D.α_on V_T V_S x) s₁

/-! ## The full package projects onto it -/

/-- **The paper-facing package forgets its Target chord.** -/
theorem GeneralFPersistencePackage.toSenderPersistencePackage
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.GeneralFPersistencePackage D E xT xS K_S) :
    p.SenderPersistencePackage D E xT xS K_S where
  xT_mem := P.xT_mem
  xS_mem := P.xS_mem
  target_value_mem := P.target_value_mem
  sender_value_mem := P.sender_value_mem
  target_policy_eq := P.target_policy_eq
  sender_carrier_lipschitz := P.sender_carrier_lipschitz
  sender_IDO_after_target_policy := P.sender_IDO_after_target_policy
  sender_subpivot_chord := P.sender_subpivot_chord

/-! ## The basin, without a Target sanction-preference hypothesis -/

/-- **P1–P3 + P5 build the P4-free persistence basin.**

`sender_high_argmax_exists` comes from P5 against P2 (level);
`top_rule_mono` comes from P3 (direction). Both steps evaluate the
Sender's objective *at the equilibrium Target action*, so the Target's
policy — and through `target_policy_eq`, its continuation value — is
present throughout. What neither step uses is any hypothesis about how
the Target ranks sanction levels, which is P4.

Since round BJ1.3 (2026-10-07) the level step reads P5 in its pivot-star form
on the basin (`SenderPersistenceBasinTop.of_pivot_beats_subpivot`).
Statement unchanged. General in `F`. -/
theorem SenderPersistencePackage.toSenderPersistenceBasinTop
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.SenderPersistencePackage D E xT xS K_S) :
    p.SenderPersistenceBasinTop E.V_S E.α (max xT xS) (max xT xS) := by
  let V_T_sub : D.CarrierT := ⟨E.V_T, P.target_value_mem⟩
  let V_S_sub : D.CarrierS := ⟨E.V_S, P.sender_value_mem⟩
  have hV_S_lip : ValueLipschitzWith E.V_S K_S :=
    P.sender_carrier_lipschitz E.V_S P.sender_value_mem
  have hpivot_mem : max xT xS ∈ Sanctions.I :=
    ⟨le_trans P.xT_mem.1 (le_max_left xT xS),
      max_le P.xT_mem.2 P.xS_mem.2⟩
  refine SenderPersistenceBasinTop.of_pivot_beats_subpivot p
    hpivot_mem.1 hpivot_mem ?_ ?_
  · -- level: P5 (pivot-star) against P2, on the basin
    intro x hx
    refine p.senderDynObjective_lt_pivot_of_star_chord_and_V_lipschitz
      (V_S := E.V_S) (α := E.α) (x := x) (sbar := max xT xS) (K := K_S) ?_ hV_S_lip
    intro s₁ hs₁
    have hchord := P.sender_subpivot_chord V_T_sub V_S_sub x hx s₁ hs₁
    simpa [P.target_policy_eq] using hchord
  · -- direction: P3
    have h := P.sender_IDO_after_target_policy V_T_sub V_S_sub
    convert h using 2
    rw [P.target_policy_eq]

/-! ## The paper-facing P4-free persistence theorem -/

/-- **General-`F` persistence from P1–P3 and P5 alone.**

Conclusions (i)–(iii) of `thm:persistence`: from every start in the high
basin, the political state stays in the basin, the realised sanction
never falls below the pivot, and the realised sanction sequence is
non-decreasing — with the Target combined chord P4 deleted from the
hypotheses and the trajectory evolved by the general transition `p.F`.

This is the formal counterpart of the manuscript's statement that
conclusions (i)–(iii) use P1–P3 and P5. -/
theorem standardCompliance_persistence_generalF_from_sender_package
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.SenderPersistencePackage D E xT xS K_S) :
    ∀ x₀ ∈ Set.Icc (max xT xS) 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, max xT xS ≤
                p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  intro x₀ hx₀
  -- Routed through the EQUILIBRIUM-ANCHORED theorem, not the kinematic
  -- one: the trajectory here must be an equilibrium path (Rule 1), and
  -- `E` is in scope, so there is no reason to consume the free-policy
  -- form. The discarded conjunct is the per-period Target-argmax
  -- certificate, which this signature does not report.
  have h :=
    p.equilibriumTop_senderPersistenceF_long_run_nonDecreasing E
      (SenderPersistencePackage.toSenderPersistenceBasinTop p P) hx₀
  exact ⟨h.1, h.2.2.1, h.2.2.2.1⟩

/-! ## The equilibrium-local form (round I, doc 75 R3)

`SenderPersistenceBasinTop.of_sender_dynamic_margin` never needed the carrier:
it consumes a Lipschitz modulus of *one* value, a chord at *one* policy and
interval dominance of *one* substituted objective. The package evaluates its
carrier-wide P2, P3 and P5 at the equilibrium pair to supply exactly those
(`toSenderPersistenceBasinTop`). Stating the theorem at the pair is therefore
a weakening of the same *conditional* result and nothing more: it constructs no
equilibrium, it enlarges no class on which one is constructed, and its
hypotheses are properties of the endogenous object `E` rather than of a class
the certificates witness — which is why the manuscript keeps the carrier-wide
statement (doc 75, J3) and this form is recorded in the formalization map. -/

/-- **Local P2, P3 and P5 at the equilibrium pair build the P4-free basin**, with
the pivot `x̄` also the sanction floor. -/
theorem SenderPersistenceBasinTop.of_local
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar K_S : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlip : ValueLipschitzWith E.V_S K_S)
    (hchord : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x xbar), ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x xbar), s₁ < s₂ →
        p.β_S * K_S * dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
          < p.U_S x (E.α x) s₂ - p.U_S x (E.α x) s₁)
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I (Set.Icc xbar 1)
      (fun s x => p.senderDynObjective E.V_S x (E.α x) s)) :
    p.SenderPersistenceBasinTop E.V_S E.α xbar xbar := by
  refine SenderPersistenceBasinTop.of_sender_dynamic_margin p hxbar_mem.1 hxbar_mem ?_ hIDO
  intro x hx
  exact p.senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz
    (V_S := E.V_S) (α := E.α) (x := x) (sbar := xbar) (K := K_S)
    (fun s₁ hs₁ s₂ hs₂ h => hchord x hx s₁ hs₁ s₂ hs₂ h) hlip

/-- **General-`F` persistence from the equilibrium-local inputs.** Conclusions
(i)–(iii) of `thm:persistence` from a Lipschitz modulus of the equilibrium
Sender value, the sub-pivot chord at the equilibrium policy, and interval
dominance of the substituted objective — no carrier, no `ValueClass2`.
Conditional on `E` exactly as the package form is. -/
theorem standardCompliance_persistence_generalF_local
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar K_S : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlip : ValueLipschitzWith E.V_S K_S)
    (hchord : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x xbar), ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x xbar), s₁ < s₂ →
        p.β_S * K_S * dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
          < p.U_S x (E.α x) s₂ - p.U_S x (E.α x) s₁)
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I (Set.Icc xbar 1)
      (fun s x => p.senderDynObjective E.V_S x (E.α x) s)) :
    ∀ x₀ ∈ Set.Icc xbar 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc xbar 1) ∧
      (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  intro x₀ hx₀
  have h :=
    p.equilibriumTop_senderPersistenceF_long_run_nonDecreasing E
      (SenderPersistenceBasinTop.of_local p E hxbar_mem hlip hchord hIDO) hx₀
  exact ⟨h.1, h.2.2.1, h.2.2.2.1⟩

/-! ### The pivot-star form (round M, doc 82 P3; the reader's round-I plan §6)

The local theorem above takes the sub-pivot chord for every pair of sanctions
below the pivot, but its proof compares each sanction only with the pivot. The
star form takes exactly that: for each basin state and each sanction below
`max x xbar`, the stage gain of moving to the pivot exceeds the worst continuation
loss the Lipschitz modulus allows. The pairwise chord implies it
(`star_chord_of_pairwise_chord`), and the pairwise theorem is recovered as a
corollary. This is the form the manuscript's remark after `thm:persistence` cites
(N61, promoted 2026-09-10). The package's bridge `toLocal` kept the pairwise chord
when this section was added; since round BJ1.3 (2026-10-07), when the package's
own P5 became the star chord on the basin, `toLocal` returns the star chord. -/

/-- The pairwise chord implies the star chord: instantiate `s₂ := max x xbar`. -/
theorem star_chord_of_pairwise_chord
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar K_S : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hchord : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x xbar), ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x xbar), s₁ < s₂ →
        p.β_S * K_S * dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
          < p.U_S x (E.α x) s₂ - p.U_S x (E.α x) s₁) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ), ∀ s₁ ∈ Set.Ico (0 : ℝ) (max x xbar),
      p.β_S * K_S * dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x (max x xbar)))
        < p.U_S x (E.α x) (max x xbar) - p.U_S x (E.α x) s₁ := by
  intro x hx s₁ hs₁
  have hpiv : max x xbar ∈ Set.Icc (0 : ℝ) (max x xbar) :=
    ⟨le_max_of_le_left (le_trans hxbar_mem.1 hx.1), le_rfl⟩
  exact hchord x hx s₁ ⟨hs₁.1, hs₁.2.le⟩ (max x xbar) hpiv hs₁.2

/-- **The local bridge in pivot-star form.** -/
theorem SenderPersistenceBasinTop.of_local_star
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar K_S : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlip : ValueLipschitzWith E.V_S K_S)
    (hstar : ∀ x ∈ Set.Icc xbar (1 : ℝ), ∀ s₁ ∈ Set.Ico (0 : ℝ) (max x xbar),
      p.β_S * K_S * dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x (max x xbar)))
        < p.U_S x (E.α x) (max x xbar) - p.U_S x (E.α x) s₁)
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I (Set.Icc xbar 1)
      (fun s x => p.senderDynObjective E.V_S x (E.α x) s)) :
    p.SenderPersistenceBasinTop E.V_S E.α xbar xbar :=
  SenderPersistenceBasinTop.of_pivot_beats_subpivot p hxbar_mem.1 hxbar_mem
    (fun x hx => p.senderDynObjective_lt_pivot_of_star_chord_and_V_lipschitz
      (V_S := E.V_S) (α := E.α) (x := x) (sbar := xbar) (K := K_S) (hstar x hx) hlip)
    hIDO

/-! ### The level alone: conclusions (i)–(ii) without interval dominance
(BH2.1, 2026-10-06)

The pivot-star theorem below takes interval dominance (A1, `hIDO`) but uses it
for one conclusion only, (iii) Monotone sanctions. The level — the Sender's
greatest response at or above `max x xbar` on the basin — comes from the star
chord against the Lipschitz modulus alone (P5 with P2, at the equilibrium
pair), and the level already gives basin invariance, a non-decreasing state
path and the inherited floor `max x₀ xbar`. The two declarations here state
that, and the pivot-star theorem is re-proved as the level theorem plus `hIDO`
(statement unchanged). -/

/-- **The pivot-star inputs give the level at the equilibrium** (general in
`F`). From a Lipschitz modulus of the equilibrium Sender value and one
comparison per sub-pivot sanction against the pivot at the equilibrium policy,
the realised equilibrium rule satisfies `max x xbar ≤ R_E x` on `[xbar, 1]`, so
in particular the ratchet `x ≤ R_E x`. Interval dominance (A1) is not used, nor
is any Target sanction preference (P4): the star chord makes the pivot beat
every sub-pivot sanction, so some maximiser, and hence the greatest one, lies
at or above it (`level_dyn_top_of_high_argmax`). -/
theorem level_dyn_top_of_local_star
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar K_S : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlip : ValueLipschitzWith E.V_S K_S)
    (hstar : ∀ x ∈ Set.Icc xbar (1 : ℝ), ∀ s₁ ∈ Set.Ico (0 : ℝ) (max x xbar),
      p.β_S * K_S * dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x (max x xbar)))
        < p.U_S x (E.α x) (max x xbar) - p.U_S x (E.α x) s₁) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ), max x xbar ≤ p.dynamicTopRealizedRule E.V_S E.α x :=
  p.level_dyn_top_of_high_argmax
    (p.sender_high_argmax_exists_of_pivot_beats_subpivot hxbar_mem.1 hxbar_mem
      (fun x hx => p.senderDynObjective_lt_pivot_of_star_chord_and_V_lipschitz
        (V_S := E.V_S) (α := E.α) (x := x) (sbar := xbar) (K := K_S) (hstar x hx) hlip))

/-- **General-`F` persistence (i)–(ii) from the level alone, pivot-star form**
(general in `F`; BH2.1, 2026-10-06). From a Lipschitz modulus of the equilibrium
Sender value and the pivot-star chord at the equilibrium policy, from every
start `x₀` in the basin `[xbar, 1]`, along the general-`F` equilibrium path:
the state stays in the basin; every realised sanction is at least the
inherited level `max x₀ xbar` (so at least the pivot `xbar`); the state path is
non-decreasing; and the Target's action maximises its complete Bellman
objective at every date.

Dropped against `standardCompliance_persistence_generalF_local_star`: interval
dominance (A1, `hIDO`), which that theorem uses only for conclusion (iii),
Monotone sanctions. No Target sanction preference (P4) either. The level
premise is unchanged, so this applies wherever the star form applies (it adds
no new instances); what it changes is which hypothesis each conclusion rests
on. Conditional on `E` exactly as the star form is. -/
theorem standardCompliance_persistence_generalF_level_star
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar K_S : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlip : ValueLipschitzWith E.V_S K_S)
    (hstar : ∀ x ∈ Set.Icc xbar (1 : ℝ), ∀ s₁ ∈ Set.Ico (0 : ℝ) (max x xbar),
      p.β_S * K_S * dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x (max x xbar)))
        < p.U_S x (E.α x) (max x xbar) - p.U_S x (E.α x) s₁) :
    ∀ x₀ ∈ Set.Icc xbar 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc xbar 1) ∧
      (∀ n, max x₀ xbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInPathF E.V_S E.α x₀) ∧
      (∀ n, IsMaxOn
        (fun a => p.joint_T_top_integrand E.V_T E.V_S
                    (p.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
        Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n))) := by
  intro x₀ hx₀
  have hlevel := p.level_dyn_top_of_local_star E hxbar_mem hlip hstar
  have hmem := p.dynamicTopLockInPathF_mem_basin E.V_S E.α hlevel hx₀
  refine ⟨hmem,
    p.dynamicTopLockInSanctionsF_ge_entry E.V_S E.α
      (fun x hx => le_trans (le_max_left x xbar) (hlevel x hx)) hx₀,
    p.dynamicTopLockInPathF_mono E.V_S E.α hlevel hx₀, ?_⟩
  intro n
  exact E.α_opt_top _ ⟨le_trans hxbar_mem.1 (hmem n).1, (hmem n).2⟩

/-- **General-`F` persistence from the equilibrium-local inputs, pivot-star
form.** Conclusions (i)–(iii) of `thm:persistence` from a Lipschitz modulus of
the equilibrium Sender value, one comparison per sub-pivot sanction against the
pivot at the equilibrium policy, and interval dominance of the substituted
objective — no carrier, no `ValueClass2`, no pairwise chord. Conditional on `E`
exactly as the package form is.

Since BH2.1 (2026-10-06) proved as
`standardCompliance_persistence_generalF_level_star` for (i)–(ii) plus `hIDO`
for (iii) alone: interval dominance makes the realised rule monotone on the
basin (`dynamicTopRealizedRule_mono_of_IDOFamilyOn`), and a monotone rule along
a monotone in-basin path gives Monotone sanctions. Statement unchanged. -/
theorem standardCompliance_persistence_generalF_local_star
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar K_S : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlip : ValueLipschitzWith E.V_S K_S)
    (hstar : ∀ x ∈ Set.Icc xbar (1 : ℝ), ∀ s₁ ∈ Set.Ico (0 : ℝ) (max x xbar),
      p.β_S * K_S * dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x (max x xbar)))
        < p.U_S x (E.α x) (max x xbar) - p.U_S x (E.α x) s₁)
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I (Set.Icc xbar 1)
      (fun s x => p.senderDynObjective E.V_S x (E.α x) s)) :
    ∀ x₀ ∈ Set.Icc xbar 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc xbar 1) ∧
      (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  intro x₀ hx₀
  obtain ⟨h1, h2, -, -⟩ :=
    p.standardCompliance_persistence_generalF_level_star E hxbar_mem hlip hstar x₀ hx₀
  exact ⟨h1, fun n => le_trans (le_max_right x₀ xbar) (h2 n),
    p.dynamicTopLockInSanctionsF_mono E.V_S E.α
      (p.level_dyn_top_of_local_star E hxbar_mem hlip hstar)
      (p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO) hx₀⟩

/-- The pairwise local theorem is the star form at the pairwise chord. -/
theorem standardCompliance_persistence_generalF_local_of_star
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar K_S : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlip : ValueLipschitzWith E.V_S K_S)
    (hchord : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x xbar), ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x xbar), s₁ < s₂ →
        p.β_S * K_S * dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
          < p.U_S x (E.α x) s₂ - p.U_S x (E.α x) s₁)
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I (Set.Icc xbar 1)
      (fun s x => p.senderDynObjective E.V_S x (E.α x) s)) :
    ∀ x₀ ∈ Set.Icc xbar 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc xbar 1) ∧
      (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) :=
  p.standardCompliance_persistence_generalF_local_star E hxbar_mem hlip
    (p.star_chord_of_pairwise_chord E hxbar_mem hchord) hIDO

/-- **The package supplies the local inputs** at the pivot `max xT xS`, by
evaluating P2, P3 and P5 at the equilibrium pair: the bridge from the
carrier-wide statement to the local one.

Round BJ1.3 (2026-10-07): the chord conjunct is now the pivot-star chord at
the equilibrium policy, the input of `SenderPersistenceBasinTop.of_local_star`
and `standardCompliance_persistence_generalF_local_star`, because the package's
P5 is itself in that form; the pairwise chord no longer follows. General in
`F`. -/
theorem SenderPersistencePackage.toLocal
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.SenderPersistencePackage D E xT xS K_S) :
    ValueLipschitzWith E.V_S K_S ∧
    (∀ x ∈ Set.Icc (max xT xS) (1 : ℝ), ∀ s₁ ∈ Set.Ico (0 : ℝ) (max x (max xT xS)),
      p.β_S * K_S * dist (Sanctions.clipS' (p.F x s₁))
          (Sanctions.clipS' (p.F x (max x (max xT xS))))
        < p.U_S x (E.α x) (max x (max xT xS)) - p.U_S x (E.α x) s₁) ∧
    Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I (Set.Icc (max xT xS) 1)
      (fun s x => p.senderDynObjective E.V_S x (E.α x) s) := by
  let V_T_sub : D.CarrierT := ⟨E.V_T, P.target_value_mem⟩
  let V_S_sub : D.CarrierS := ⟨E.V_S, P.sender_value_mem⟩
  refine ⟨P.sender_carrier_lipschitz E.V_S P.sender_value_mem, ?_, ?_⟩
  · intro x hx s₁ hs₁
    have hchord := P.sender_subpivot_chord V_T_sub V_S_sub x hx s₁ hs₁
    simpa [P.target_policy_eq] using hchord
  · have h := P.sender_IDO_after_target_policy V_T_sub V_S_sub
    convert h using 2
    rw [P.target_policy_eq]

/-- Rule-13 check: the existing paper-facing persistence theorem is
recovered verbatim through the P4-free route, so deleting P4 from the
hypotheses removed no content from conclusions (i)–(iii). -/
example
    {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (P : p.GeneralFPersistencePackage D E xT xS K_S) :
    ∀ x₀ ∈ Set.Icc (max xT xS) 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
                ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, max xT xS ≤
                p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) :=
  p.standardCompliance_persistence_generalF_from_sender_package
    (GeneralFPersistencePackage.toSenderPersistencePackage p P)

end Params
end AbstractGame

end

end Sanctions
