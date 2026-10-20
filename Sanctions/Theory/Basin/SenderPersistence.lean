/-
Sanctions/Theory/Basin/SenderPersistence.lean

**Persistence without the Target combined chord (debundling round, 2026-08-09).**

The manuscript states a division of labour for `thm:persistence`: the
Target combined chord P4 yields conclusion (vi) — the Target-side
preference evidence — while the three *kinematic* conclusions

  (i)   the state stays in the basin,
  (ii)  the realised sanction is bounded below by the pivot,
  (iii) the realised sanction sequence is non-decreasing,

do not need it. That statement is *mathematically* true of the existing
proofs, but until this file it was **not instantiated anywhere**: every
route to (i)–(iii) went through `JointPreferenceBasinTop`, which carries
`target_prefers_sanctions` as a mandatory field, so the paper asserted a
separation the Lean did not exhibit.

This file closes that gap by *debundling*, not by weakening anything.
The observation it rests on is that the two load-bearing lemmas already
ignore the Target-preference field:

* `JointPreferenceBasinTop.level_dyn_top` — the floor
  `max x s̄ ≤ σ_dyn_top` — consumes only `sender_high_argmax_exists`;
* `jointPreferenceBasinTopF_long_run_nonDecreasing` consumes only
  `xbar_nonneg`, that floor, and `top_rule_mono`.

## What is dropped, and what is emphatically NOT

`JointPreferenceBasinTop` has **eight** fields.
`SenderPersistenceBasinTop` below keeps three of them and drops five,
but the five are not equally interesting:

| Dropped field | Why |
|---|---|
| `target_prefers_sanctions` | **This is P4.** Genuinely deleted; it is the hypothesis this file exists to remove. |
| `target_policy_feasible`, `target_policy_optimal` | Recovered, in stronger form, by the equilibrium-anchored layer below (`E.α_mem`, `E.α_opt_top`). |
| `xbar_le_one`, `sbar_mem` | Simply unconsumed by the path lemmas. |

**The Target's equilibrium policy is not dropped and could not be.**
The Sender's forward-looking objective is
`senderDynObjective V_S x (α x) s` — the Target's action is an argument
of it — so every conclusion below is *conditional on the Target playing
its Bellman-optimal equilibrium policy*. What P4 adds on top of that,
and what is removed here, is a hypothesis about the Target's *ranking
over sanction levels*. Reading these theorems as "the Sender alone
sustains the path" would be an overclaim; the correct reading is "given
the Target's optimal policy, the Sender-side level and direction
conditions suffice, and no assumption about the Target's sanction
preference is needed."

## Two layers, and why both

The file ships the parametric layer and an equilibrium-anchored layer,
mirroring `JointPreferenceBasin.lean`, which pairs the free-parametric
`jointPreferenceBasinTop_long_run_nonDecreasing` with the in-file
anchored `equilibriumTop_jointPreferenceBasinTop_long_run_nonDecreasing`.

* The **parametric** theorems quantify over `(V_S, α)`. This is the
  Rule-5 general form, and it is what makes the structure reusable and
  the Rule-13 recovery check below meaningful at full generality.
* The **anchored** theorems (`equilibriumTop_senderPersistence_*`) take
  `E : FeedbackStackelbergEquilibriumTop` and instantiate at `E.V_S`,
  `E.α`, so the Target policy driving the trajectory is feasible and
  Bellman-optimal by construction. These are the ones downstream code
  and the paper should cite.

A referee round on 2026-08-09 read the parametric layer alone as a
Rule-1 defect, on the ground that its trajectory theorems run on an
unconstrained `α`. That reading does not survive checking: Rule 1 fences
*fixed, hand-chosen* policies ("if the Target plays `a = 0` every
period…"), not universally quantified ones, and `JointPreferenceBasinTop`
— the basis of every headline theorem in the project — is equally free in
`(V_T, V_S, α)`; its `target_policy_optimal` field asserts optimality
only against the *free* `V_T`, so it too is a real discharge only once
instantiated at an equilibrium. What the round did legitimately catch is
that this file shipped **no anchored sibling at all**, leaving its
equilibrium anchor two files away and invisible to a reader. That is
what the second layer fixes.

## Rule compliance

**Rule 1.** Discharged where the project discharges it: at instantiation.
Every downstream consumer — `SenderPersistencePackage`,
`StandardCompliancePersistenceCertificate`, and the Rule-18 headline row
— supplies an `E`, and the anchored layer below makes that visible here
rather than only at the call site. The Sender side is the upper dynamic
argmax `σ_dyn_top` throughout.

**Rule 3.** No new assumption. Every field is a field of
`JointPreferenceBasinTop` verbatim, and the bridge is by projection.
This is the "pure refactor" exemption; the assumption surface *shrinks*.

**Rule 5.** The parametric form is primary; the anchored theorems are
one-line specialisations of it.

**Rule 22.** The general-`F` path theorems are primary; the affine
sibling is derived, not the other way round.
-/

import Sanctions.Theory.Basin.JointPreferenceBasin

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The P4-free basin object -/

/-- **Sender-side persistence basin (no Target sanction-preference
hypothesis).**

The sub-bundle of `JointPreferenceBasinTop` that the three kinematic
persistence conclusions actually consume.

In economic terms: on the basin `[xbar, 1]`, *against whatever Target
policy `α` is supplied*, the forward-looking Sender always has a
maximiser at or above `max(x, s̄)` — so the realised sanction never falls
below the pivot — and its greatest maximiser moves weakly upward with
the inherited state — so the realised sanction sequence cannot fall.

What is absent is any hypothesis on how the **Target** ranks sanction
levels. That is P4, and it is what this structure exists to do without.
Optimality of `α` is discharged at instantiation, exactly as for
`JointPreferenceBasinTop`; see `equilibriumTop_senderPersistence_*`
below for the anchored form. -/
structure SenderPersistenceBasinTop
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α : ℝ → ℝ) (xbar sbar : ℝ) : Prop where
  /-- The basin pivot is a feasible state from below. -/
  xbar_nonneg : 0 ≤ xbar
  /-- At every basin state the Sender's forward-looking argmax, against
  the supplied Target action, contains an element at or above
  `max(x, s̄)`. -/
  sender_high_argmax_exists :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      ∃ s ∈ Sanctions.I,
        IsMaxOn (fun s' => p.senderDynObjective V_S x (α x) s') Sanctions.I s ∧
        max x sbar ≤ s
  /-- The greatest dynamic Sender response is non-decreasing in the
  inherited state on the basin. -/
  top_rule_mono :
    MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc xbar 1)

/-! ## The floor, without the Target-preference field -/

/-- **Sanction floor from the Sender side.** Verbatim the proof of
`JointPreferenceBasinTop.level_dyn_top`, which never referred to
`target_prefers_sanctions`. -/
theorem SenderPersistenceBasinTop.level_dyn_top
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hB : p.SenderPersistenceBasinTop V_S α xbar sbar) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar ≤ p.dynamicTopRealizedRule V_S α x := by
  intro x hx
  obtain ⟨s, hsI, hsMax, hsHigh⟩ := hB.sender_high_argmax_exists x hx
  have hsSet : s ∈ p.dynamicArgmaxSet V_S x (α x) := by
    refine ⟨hsI, ?_⟩
    intro s' hs'
    exact hsMax hs'
  unfold dynamicTopRealizedRule σ_dyn_top
  exact le_trans hsHigh (le_csSup (p.dynamicArgmaxSet_bddAbove V_S x (α x)) hsSet)

/-! ## Conclusions (i)–(iii), general `F` -/

/-- **Kinematic layer — internal. Not an economic statement.**

From any basin start, the state path stays in the basin, the realised
sanction is bounded below by both `s̄` and the pivot, and the sanction
sequence is non-decreasing — with no hypothesis on the Target's ranking
over sanctions.

`α` here is an arbitrary policy, so the trajectory this evolves need not
be an equilibrium path: the statement is a fact about the *iteration*,
not about the game. **Do not cite it for an economic claim.** The
equilibrium-anchored forms
`equilibriumTop_senderPersistenceF_long_run_nonDecreasing` and
`equilibriumTop_senderPersistenceF_long_run_with_evidence` are the public
interface, and every consumer in this repository routes through them. -/
theorem senderPersistenceBasinTopF_long_run_nonDecreasing
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.SenderPersistenceBasinTop V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n) ∧
    (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctionsF V_S α x₀) := by
  have hlevel := SenderPersistenceBasinTop.level_dyn_top p hB
  exact ⟨
    p.dynamicTopLockInPathF_mem_basin V_S α hlevel hx₀,
    p.dynamicTopLockInSanctionsF_floor V_S α hlevel hx₀,
    p.dynamicTopLockInSanctionsF_ge_xbar V_S α hlevel hx₀,
    p.dynamicTopLockInSanctionsF_mono V_S α hlevel
      hB.top_rule_mono hx₀⟩

/-- **Persistence without P4, affine sibling.** The `p.F = affineF p.δ`
specialisation of the previous theorem's trajectory (Rule 22 axis 2:
`dynamicTopLockInPath` hard-codes the affine law). Retained because the
legacy manuscript statements are phrased over it. -/
theorem senderPersistenceBasinTop_long_run_nonDecreasing
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.SenderPersistenceBasinTop V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n) ∧
    (∀ n, xbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions V_S α x₀) := by
  have hlevel := SenderPersistenceBasinTop.level_dyn_top p hB
  exact ⟨
    p.dynamicTopLockInPath_mem_basin V_S α hlevel hx₀,
    p.dynamicTopLockInSanctions_floor V_S α hlevel hx₀,
    p.dynamicTopLockInSanctions_ge_xbar V_S α hlevel hx₀,
    p.dynamicTopLockInSanctions_mono V_S α hlevel hB.top_rule_mono hx₀⟩

/-! ## The shock leg, minus its one P4-dependent conjunct -/

/-- **Kinematic layer — internal.** Finite shock entry over the general
transition `F`, without P4. As with the long-run theorem above, `α` is
arbitrary here, so this is a statement about the iteration and not about
an equilibrium path; cite
`equilibriumTop_senderPersistenceF_temporary_shock_permanent_high`
instead.

The five kinematic conjuncts of
`jointPreferenceBasinTopF_temporary_shock_permanent_high`. The sixth
conjunct of that theorem — the Target's sanction objective being
monotone along the post-shock path — is precisely the P4-dependent one
and is *not* claimed here.

The exogenous shock phase is the Rule-1 transient-shock exception: the
sanction path during the shock is externally imposed, and the natural
optimal dynamics resume at the end of it. -/
theorem senderPersistenceBasinTopF_temporary_shock_permanent_high
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.SenderPersistenceBasinTop V_S α xbar sbar)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    (hxbar_lt_one : xbar < 1)
    (hsbar_pos : 0 < sbar)
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPathF V_S α (p.shockPathF x₀ N) n
              ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α (p.shockPathF x₀ N) n) ∧
      (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF V_S α (p.shockPathF x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctionsF V_S α (p.shockPathF x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctionsF V_S α (p.shockPathF x₀ N)) := by
  have hlevel := SenderPersistenceBasinTop.level_dyn_top p hB
  obtain ⟨N, hN⟩ :=
    p.shockPathF_eventually_in_basin hF_top hx₀_nn hx₀_le hxbar_lt_one
  have h_N_in : p.shockPathF x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  have h_floor :=
    p.dynamicTopLockInSanctionsF_floor V_S α hlevel h_N_in
  refine ⟨N, ?_, h_floor, ?_, ?_, ?_⟩
  · exact p.dynamicTopLockInPathF_mem_basin V_S α hlevel h_N_in
  · exact p.dynamicTopLockInSanctionsF_ge_xbar V_S α hlevel h_N_in
  · intro n; exact lt_of_lt_of_le hsbar_pos (h_floor n)
  · exact p.dynamicTopLockInSanctionsF_mono V_S α hlevel
      hB.top_rule_mono h_N_in

/-! ## Nothing is lost: the full basin forgets to the slim one -/

/-- **The joint basin projects onto the Sender persistence basin.**
Field-by-field projection, so every consumer of the slim structure is
available to every consumer of the full one. -/
theorem JointPreferenceBasinTop.toSenderPersistence
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar) :
    p.SenderPersistenceBasinTop V_S α xbar sbar where
  xbar_nonneg := hB.xbar_nonneg
  sender_high_argmax_exists := hB.sender_high_argmax_exists
  top_rule_mono := hB.top_rule_mono

/-- Rule-13 check that this file is a refactor and not a restatement:
the existing general-`F` Goal-1 theorem is recovered verbatim by routing
through the slim structure, at full parametric generality. If the
debundling had dropped content, this would not typecheck. -/
example
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.JointPreferenceBasinTop V_T V_S α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n) ∧
    (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF V_S α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctionsF V_S α x₀) :=
  p.senderPersistenceBasinTopF_long_run_nonDecreasing
    (JointPreferenceBasinTop.toSenderPersistence p hB) hx₀

/-! ## Equilibrium-anchored layer (Rule 1 visible in this file)

The house pattern of `JointPreferenceBasin.lean`, whose
`equilibriumTop_jointPreferenceBasinTop_long_run_nonDecreasing` pairs the
free-parametric Goal-1 theorem with an equilibrium-anchored sibling in
the same file. These are the declarations downstream code and the paper
should cite: the Target policy driving the trajectory is `E.α`, feasible
(`E.α_mem`) and Bellman-optimal against the joint top integrand
(`E.α_opt_top`), with both value functions at their Bellman fixed
points. -/

/-- **Anchored general-`F` persistence.** Conclusions (i)–(iii) along the
path of an actual feedback Stackelberg equilibrium, with no hypothesis on
the Target's ranking over sanction levels. -/
theorem equilibriumTop_senderPersistenceF_long_run_nonDecreasing
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar sbar x₀ : ℝ}
    (hB : p.SenderPersistenceBasinTop E.V_S E.α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
    (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn
      (fun a => p.joint_T_top_integrand E.V_T E.V_S
                  (p.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
      Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n))) := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    p.senderPersistenceBasinTopF_long_run_nonDecreasing hB hx₀
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro n
  exact E.α_opt_top _ ⟨le_trans hB.xbar_nonneg (h1 n).1, (h1 n).2⟩

/-- **Anchored general-`F` persistence with the complete P4-free evidence.**

Everything `jointPreferenceBasinTopF_long_run_with_equilibrium_evidence`
returns, *except* its final conjunct — the Target's sanction objective
being monotone above the realised-state floor, which is conclusion (vi)
and the one thing P4 is responsible for.

Concretely, at every date along the equilibrium path: the state is in the
basin, the realised sanction clears both floors and never falls, the
Target's action is feasible and maximises its complete Bellman objective,
and the realised sanction maximises the Sender's forward-looking
objective. So conclusions (i)–(v) of `thm:persistence` hold with the
Target combined chord deleted from the hypotheses, which is what makes
the manuscript's division of labour formally transparent rather than
merely asserted.

No new hypothesis: Target feasibility and optimality come from `E.α_mem`
and `E.α_opt_top`, and Sender optimality from `σ_dyn_top_isMaxOn` — the
upper selector is a maximiser by construction. -/
theorem equilibriumTop_senderPersistenceF_long_run_with_evidence
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar sbar x₀ : ℝ}
    (hB : p.SenderPersistenceBasinTop E.V_S E.α xbar sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
    (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) ∧
    (∀ n, E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n) ∈ Sanctions.I) ∧
    (∀ n, IsMaxOn
      (fun a => p.joint_T_top_integrand E.V_T E.V_S
                  (p.dynamicTopLockInPathF E.V_S E.α x₀ n) a)
      Sanctions.I (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n))) ∧
    (∀ n, IsMaxOn
      (fun s' => p.senderDynObjective E.V_S
                  (p.dynamicTopLockInPathF E.V_S E.α x₀ n)
                  (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n)) s')
      Sanctions.I (p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)) := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    p.senderPersistenceBasinTopF_long_run_nonDecreasing hB hx₀
  have hmemS : ∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Sanctions.S :=
    fun n => ⟨le_trans hB.xbar_nonneg (h1 n).1, (h1 n).2⟩
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
  · intro n; exact E.α_mem _ (hmemS n)
  · intro n; exact E.α_opt_top _ (hmemS n)
  · intro n s' hs'
    exact p.σ_dyn_top_isMaxOn E.V_S
      (p.dynamicTopLockInPathF E.V_S E.α x₀ n)
      (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n)) hs'

/-- **Anchored finite shock entry.** The general-`F` shock leg along an
actual equilibrium path, with the Target-argmax certificate attached.

Round BB (2026-09-28): three of this theorem's premises are more than the
conclusion needs.
`equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent`
(`Basin/SenderPersistenceLocalisedShock.lean`) proves the same conclusion
without `hsbar_pos` (a positive sanction floor) and `hxbar_lt_one` (the
threshold below one), and with `hF_top` localised: full-sanction ascent only
on `[0, x̄]` instead of on `[0, 1)`. -/
theorem equilibriumTop_senderPersistenceF_temporary_shock_permanent_high
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar sbar x₀ : ℝ}
    (hB : p.SenderPersistenceBasinTop E.V_S E.α xbar sbar)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    (hxbar_lt_one : xbar < 1)
    (hsbar_pos : 0 < sbar)
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α (p.shockPathF x₀ N) n
              ∈ Set.Icc xbar 1) ∧
      (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                      (p.shockPathF x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α
                  (p.shockPathF x₀ N)) ∧
      (∀ n, IsMaxOn
        (fun a => p.joint_T_top_integrand E.V_T E.V_S
                    (p.dynamicTopLockInPathF E.V_S E.α
                      (p.shockPathF x₀ N) n) a)
        Sanctions.I
        (E.α (p.dynamicTopLockInPathF E.V_S E.α
                (p.shockPathF x₀ N) n))) := by
  obtain ⟨N, h1, _h2, h3, _h4, h5⟩ :=
    p.senderPersistenceBasinTopF_temporary_shock_permanent_high hB hF_top
      hxbar_lt_one hsbar_pos hx₀_nn hx₀_le
  refine ⟨N, h1, h3, h5, ?_⟩
  intro n
  exact E.α_opt_top _ ⟨le_trans hB.xbar_nonneg (h1 n).1, (h1 n).2⟩

/-! ## Constructors -/

/-- **From the dynamic Sender margin.** If the Sender's forward-looking
objective — evaluated at the supplied Target action — is strictly
increasing in the sanction below `max(x, s̄)` at every basin state, and
its greatest maximiser satisfies the interval-dominance family condition
in the state, the basin object follows.

This is the shape the general-`F` certificate route supplies: the strict
monotonicity is the *level* input (the transition-adjusted sub-pivot
chord against the Sender carrier's Lipschitz bound, P5 with P2), and the
interval-dominance condition is the *direction* input (P3, the
manuscript's Assumption A1). -/
theorem SenderPersistenceBasinTop.of_sender_dynamic_margin
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hxbar_nonneg : 0 ≤ xbar)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h_sender_dyn :
      ∀ x ∈ Set.Icc xbar (1 : ℝ),
        StrictMonoOn (fun s => p.senderDynObjective V_S x (α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc xbar 1)
        (fun s x => p.senderDynObjective V_S x (α x) s)) :
    p.SenderPersistenceBasinTop V_S α xbar sbar where
  xbar_nonneg := hxbar_nonneg
  sender_high_argmax_exists :=
    p.sender_high_argmax_exists_of_strictMono_below_threshold
      hxbar_nonneg hsbar_mem h_sender_dyn
  top_rule_mono := p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO

/-- **From the pivot beating every sub-pivot sanction** (round M, doc 82 P3): the
level input in its pivot-star form — the objective at `max x sbar` strictly above
its value at every lower sanction — plus the interval-dominance direction input.
`of_sender_dynamic_margin` is the case where the star comparison comes from strict
monotonicity below the pivot. -/
theorem SenderPersistenceBasinTop.of_pivot_beats_subpivot
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hxbar_nonneg : 0 ≤ xbar)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (h_star : ∀ x ∈ Set.Icc xbar (1 : ℝ), ∀ s ∈ Set.Ico (0 : ℝ) (max x sbar),
      p.senderDynObjective V_S x (α x) s
        < p.senderDynObjective V_S x (α x) (max x sbar))
    (hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc xbar 1)
        (fun s x => p.senderDynObjective V_S x (α x) s)) :
    p.SenderPersistenceBasinTop V_S α xbar sbar where
  xbar_nonneg := hxbar_nonneg
  sender_high_argmax_exists :=
    p.sender_high_argmax_exists_of_pivot_beats_subpivot hxbar_nonneg hsbar_mem h_star
  top_rule_mono := p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO

/-- **From the stage Sender margin plus a monotone Sender value.** The
route used by the Milgrom–Shannon certificate: stage-level strict
monotonicity of `U_S` in the sanction below threshold, lifted to the
forward-looking objective by monotonicity of the Sender's continuation
value. Note this is a *level* input, not the manuscript's Assumption A1,
which is the interval-dominance direction condition supplied separately
as `hIDO`. -/
theorem SenderPersistenceBasinTop.of_stage_sender_margin
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar : ℝ}
    (hxbar_nonneg : 0 ≤ xbar)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hV_S_mono : Monotone V_S)
    (h_stage_sender :
      ∀ x ∈ Set.Icc xbar (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (hIDO :
      Sanctions.IntervalDominanceOrder.IDOFamilyOn
        Sanctions.I (Set.Icc xbar 1)
        (fun s x => p.senderDynObjective V_S x (α x) s)) :
    p.SenderPersistenceBasinTop V_S α xbar sbar :=
  SenderPersistenceBasinTop.of_sender_dynamic_margin p
    hxbar_nonneg hsbar_mem
    (fun x hx =>
      p.senderDynObjective_strictMono_of_stage_strictMono_and_V_mono
        hV_S_mono (h_stage_sender x hx))
    hIDO

end Params
end AbstractGame

end

end Sanctions
