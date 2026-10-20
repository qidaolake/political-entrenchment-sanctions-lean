/-
Sanctions/Theory/Basin/SenderPersistenceLow.lean

**Low-basin persistence without the Target's sanction preference
(round BB, 2026-09-28; doc 110 item R6(b)).**

Headline row 3, `standardCompliance_three_goals_local_low_basin_generalF`, is
the low-basin mirror of persistence: from any start in a low political basin
`[0, x̄]` the equilibrium state stays in the basin, the realised sanction stays
at or below a ceiling and never rises. Its hypothesis bundle,
`OneSidedSanctionLowBasinPreferenceThresholds`, carries a Target field,
`target_dislikes_high_sanctions` — the Target's forward-looking sanction
objective is non-increasing in the sanction on the low basin. **None of row 3's
four conclusions reads that field.** The row-3 proof builds a
`JointPreferenceBasinLow`, whose own Target field `target_dislikes_sanctions`
is filled from it, and the four path lemmas it then calls
(`dynamicTopLockInPathF_mem_low_basin`, `..._ceiling_low`, `..._le_xbar_low`,
`..._anti_low`) consume only three things: `xbar_low ≤ 1`, the Sender's
low-level condition, and monotonicity of the realised rule.

This file makes that visible, exactly as `SenderPersistence.lean` did for the
high basin on 2026-08-09:

* `SenderPersistenceBasinLow` — the three-field sub-bundle of
  `JointPreferenceBasinLow` that the path lemmas read;
* projections onto it from `JointPreferenceBasinLow` and from the row-3
  hypothesis bundle, the latter reading only the Sender fields;
* an equilibrium-anchored persistence theorem over it, with Target
  feasibility, Target optimality and Sender optimality along the path;
* `standardCompliance_low_basin_generalF_of_sender_level`, a row-3 sibling
  whose hypotheses are the Sender's strict low-level input, `x̄ ≤ 1`,
  feasibility of the ceiling and rule monotonicity — no Target hypothesis —
  and a Rule-13 `example` recovering row 3's statement from it;
* `standardCompliance_low_basin_generalF_of_sender_star` (round BH-2,
  2026-10-06), the same conclusions from the pivot-star form of the level
  input — the Sender's objective at the ceiling `min(x, s̄)` strictly beats
  every heavier sanction — and `0 ≤ s̄`; the headline above is now its
  corollary;
* the Sender-only form of initial-condition selection (one equilibrium, two
  disjoint basins), with no Target-preference hypothesis on either side.

## Why the level field is the top-selector bound, not an existence claim

`SenderPersistenceBasinTop` states its level input as an *existence* claim —
some Sender maximiser sits at or above `max x s̄` — and gets the floor
`max x s̄ ≤ σ_dyn_top` from `le_csSup`. The naive order dual, "some maximiser
sits at or below `min x s̄`", does **not** give the ceiling
`σ_dyn_top ≤ min x s̄`: the realised rule is the *greatest* maximiser, and one
low maximiser says nothing about the greatest (doc 110, G2 corrections (d)).
The low basin needs a bound on *every* maximiser. The field below is therefore
the existing `JointPreferenceBasinLow.sender_low_argmax_le_threshold`
verbatim — the greatest maximiser is at most `min x s̄` — and
`SenderPersistenceBasinLow.argmax_le` shows it is the same statement as
"every Sender best response lies at or below `min x s̄`". Its constructor from
primitives uses the strict input the Lean low basin has always used: the
Sender's forward-looking objective strictly decreasing in the sanction above
`min x s̄` (`StrictAntiOn`), which bounds every maximiser. Only the comparisons
of that input against the pivot `min x s̄` are ever read, so since round BH-2
the primary constructor takes exactly those (`of_pivot_beats_superpivot`), and
the `StrictAntiOn` constructor is its corollary.

## Scope (Rule 9)

Nothing here is an existence claim and nothing is witnessed: every theorem is
a universal statement over an arbitrary economy `p`, an arbitrary equilibrium
`E` and arbitrary basin data satisfying the stated Sender conditions. The
conclusions are about the equilibrium `E` supplied — *any* feedback
Stackelberg equilibrium meeting the conditions, not only a constructed one.
The Sender's action is the upper dynamic argmax `σ_dyn_top` throughout, the
selector the whole project uses. The Target's equilibrium policy `E.α` is not
dropped and could not be: it is an argument of the Sender's forward-looking
objective. What is dropped is a hypothesis about how the Target *ranks
sanction levels*.

## Rule compliance

**Rule 1.** The anchored theorems take `E : FeedbackStackelbergEquilibriumTop`;
the Target policy is feasible and Bellman-optimal by `E.α_mem`, `E.α_opt_top`,
and the realised sanction is the Sender's forward-looking argmax. The one
internal kinematic lemma over a free `α` is marked as such.

**Rule 3.** No new assumption. Each field of `SenderPersistenceBasinLow` is a
field of `JointPreferenceBasinLow` verbatim, and
`JointPreferenceBasinLow.toSenderPersistenceLow` is the projection; the
row-3 sibling's hypotheses are components of row 3's (`x̄ ≤ 1` is implied by
`xT_star_mem`, the Sender input is `sender_dislikes_above_threshold`
restricted to the basin). The assumption surface strictly shrinks: row 3
follows from the sibling (the `example` below), and the sibling's hypotheses
do not mention `target_dislikes_high_sanctions`. No economy is yet exhibited
in which that field fails while the Sender conditions hold (Rule 9B:
generality unwitnessed).

**Rule 14.** The structure is a `Prop`-valued bundle of relations stated
directly over the data `(V_S, α, x̄, s̄)` through the realised rule
`dynamicTopRealizedRule V_S α`; there is no opaque `Prop` field.

**Rule 22.** General in `F`. The state path is `dynamicTopLockInPathF`, whose
step is `p.F x (rule x)`; the descent `F(x, σ) ≤ F(x, x) = x` uses only
`F_mono_s` and `F_diag`. The affine law appears nowhere, on any of the three
axes.
-/

import Sanctions.Theory.Basin.SenderPersistence
import Sanctions.Theory.Certificates.StandardComplianceLowBasin

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The Target-preference-free low basin -/

/-- **Sender-side low persistence basin (no Target sanction-preference
hypothesis).**

The sub-bundle of `JointPreferenceBasinLow` that the four low-basin path
conclusions consume. In economic terms: on the low basin `[0, x̄]`, against
the supplied Target policy `α`, the forward-looking Sender's greatest best
response never exceeds `min(x, s̄)` — so the realised sanction never pushes
the state up — and that best response moves weakly upward with the inherited
state — so, as the state falls, the realised sanction cannot rise.

What is absent is any hypothesis on how the Target ranks sanction levels
(`JointPreferenceBasinLow.target_dislikes_sanctions`). Rule 9B: this bundle's
generality over `JointPreferenceBasinLow` is as yet unwitnessed. Its only
inhabitants in the tree are projections of joint-basin witnesses; no economy
is exhibited in which the Target field fails while this bundle holds. -/
structure SenderPersistenceBasinLow
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (α : ℝ → ℝ) (xbar_low sbar_low : ℝ) : Prop where
  /-- The basin ceiling is a feasible state. -/
  xbar_low_le_one : xbar_low ≤ 1
  /-- At every low-basin state the Sender's greatest forward-looking best
  response, against the supplied Target action, is at most `min(x, s̄)`. -/
  sender_low_argmax_le_threshold :
    ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
      p.dynamicTopRealizedRule V_S α x ≤ min x sbar_low
  /-- The greatest dynamic Sender response is non-decreasing in the
  inherited state on the low basin. -/
  top_rule_mono :
    MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc (0 : ℝ) xbar_low)

/-! ## The level field is a statement about every best response -/

/-- **Every Sender best response respects the ceiling.** The level field
bounds the greatest maximiser, hence every maximiser: at every low-basin
state, any sanction maximising the Sender's forward-looking objective
against the supplied Target action is at most `min(x, s̄)`. -/
theorem SenderPersistenceBasinLow.argmax_le
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar_low sbar_low : ℝ}
    (hB : p.SenderPersistenceBasinLow V_S α xbar_low sbar_low) :
    ∀ x ∈ Set.Icc (0 : ℝ) xbar_low, ∀ s ∈ Sanctions.I,
      IsMaxOn (fun s' => p.senderDynObjective V_S x (α x) s') Sanctions.I s →
        s ≤ min x sbar_low := by
  intro x hx s hsI hsMax
  have hsSet : s ∈ p.dynamicArgmaxSet V_S x (α x) := by
    refine ⟨hsI, ?_⟩
    intro s' hs'
    exact hsMax hs'
  exact le_trans (le_csSup (p.dynamicArgmaxSet_bddAbove V_S x (α x)) hsSet)
    (hB.sender_low_argmax_le_threshold x hx)

/-- **From a ceiling on every Sender best response.** The converse of
`argmax_le`: if every maximiser of the Sender's forward-looking objective lies
at or below `min(x, s̄)` on the low basin, so does the greatest one, and the
basin object follows. Together with `argmax_le` this shows the level field
says exactly "no Sender best response exceeds the ceiling". -/
theorem SenderPersistenceBasinLow.of_every_argmax_le
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar_low sbar_low : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (h_every : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low, ∀ s ∈ Sanctions.I,
      IsMaxOn (fun s' => p.senderDynObjective V_S x (α x) s') Sanctions.I s →
        s ≤ min x sbar_low)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc (0 : ℝ) xbar_low)) :
    p.SenderPersistenceBasinLow V_S α xbar_low sbar_low where
  xbar_low_le_one := hxbar_low_le_one
  sender_low_argmax_le_threshold := fun x hx =>
    h_every x hx _ (p.σ_dyn_top_mem_I V_S x (α x))
      (fun _ hy => p.σ_dyn_top_isMaxOn V_S x (α x) hy)
  top_rule_mono := hTopMono

/-! ## Constructors from the strict level input -/

/-- **From the pivot beating every super-pivot sanction (round BH-2,
2026-10-06, BH2.6).** If, at every low-basin state `x ∈ [0, x̄]`, the Sender's
forward-looking objective (evaluated at the supplied Target action) is strictly
higher at the pivot `min(x, s̄)` than at every heavier feasible sanction in
`(min(x, s̄), 1]`, then no best response lies above `min(x, s̄)`; together with
`x̄ ≤ 1`, `0 ≤ s̄` and monotonicity of the realised rule, the basin object
follows.

In plain terms: on the low basin the Sender prefers the ceiling sanction to any
heavier one, so it never sanctions above the ceiling. This is the order dual of
`SenderPersistenceBasinTop.of_pivot_beats_subpivot`.

Dropped relative to `of_sender_dynamic_strictAnti`: strict decrease of the
objective on all of `[min(x, s̄), 1]` (two heavier sanctions are never
compared), and `s̄ ≤ 1` (only `0 ≤ s̄` is read). The comparison stays strict: a
weak one would not bound the greatest maximiser. General in `F`. -/
theorem SenderPersistenceBasinLow.of_pivot_beats_superpivot
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar_low sbar_low : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (hsbar_nn : 0 ≤ sbar_low)
    (h_star : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
      ∀ s ∈ Set.Ioc (min x sbar_low) (1 : ℝ),
        p.senderDynObjective V_S x (α x) s
          < p.senderDynObjective V_S x (α x) (min x sbar_low))
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc (0 : ℝ) xbar_low)) :
    p.SenderPersistenceBasinLow V_S α xbar_low sbar_low where
  xbar_low_le_one := hxbar_low_le_one
  sender_low_argmax_le_threshold :=
    p.sender_low_argmax_le_threshold_of_pivot_beats_superpivot V_S α hsbar_nn h_star
  top_rule_mono := hTopMono

/-- **From the Sender's strict dynamic low-level input.** If, at every
low-basin state, the Sender's forward-looking objective (evaluated at the
supplied Target action) is strictly decreasing in the sanction on
`[min(x, s̄), 1]`, then no best response lies above `min(x, s̄)`; together with
feasibility of the ceilings and monotonicity of the realised rule, the basin
object follows. The strict input is what the Lean low basin has always used
(`sender_low_argmax_le_threshold_of_strictAntiOn`); a weak one would not bound
the greatest maximiser.

Since round BH-2 (2026-10-06, BH2.6) a corollary of
`of_pivot_beats_superpivot`: strict decrease on `[min(x, s̄), 1]` gives the
pivot-star comparison. Statement unchanged. General in `F`. -/
theorem SenderPersistenceBasinLow.of_sender_dynamic_strictAnti
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar_low sbar_low : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (hsbar_mem : sbar_low ∈ Sanctions.I)
    (h_sender_low :
      ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
        StrictAntiOn (fun s => p.senderDynObjective V_S x (α x) s)
          (Set.Icc (min x sbar_low) (1 : ℝ)))
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc (0 : ℝ) xbar_low)) :
    p.SenderPersistenceBasinLow V_S α xbar_low sbar_low :=
  SenderPersistenceBasinLow.of_pivot_beats_superpivot p hxbar_low_le_one hsbar_mem.1
    (fun x hx _ hs =>
      h_sender_low x hx ⟨le_rfl, hs.1.le.trans hs.2⟩ ⟨hs.1.le, hs.2⟩ hs.1)
    hTopMono

/-- **From the stage Sender low-level input plus a decreasing Sender value.**
Stage-level strict decrease of `U_S` in the sanction above `min(x, s̄)`,
lifted to the forward-looking objective by an antitone Sender continuation
value (`senderDynObjective_strictAntiOn_of_stage_strictAntiOn_and_V_antiMono`).
This is the Sender half of the low-basin stage route
`OneSidedSanctionLowBasinPreferenceThresholds.of_stage_preferences_low`, with
its Target half deleted. -/
theorem SenderPersistenceBasinLow.of_stage_sender_strictAnti
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar_low sbar_low : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (hsbar_mem : sbar_low ∈ Sanctions.I)
    (hV_S_anti : Antitone V_S)
    (h_stage_sender_low :
      ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
        StrictAntiOn (fun s => p.U_S x (α x) s)
          (Set.Icc (min x sbar_low) (1 : ℝ)))
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc (0 : ℝ) xbar_low)) :
    p.SenderPersistenceBasinLow V_S α xbar_low sbar_low :=
  SenderPersistenceBasinLow.of_sender_dynamic_strictAnti p hxbar_low_le_one
    hsbar_mem
    (fun x hx =>
      p.senderDynObjective_strictAntiOn_of_stage_strictAntiOn_and_V_antiMono
        hV_S_anti (h_stage_sender_low x hx))
    hTopMono

/-! ## Nothing is lost: the existing low-basin objects project onto it -/

/-- **The joint low basin forgets to the Sender one.** Field-by-field
projection: `target_policy_feasible`, `target_dislikes_sanctions` and
`target_policy_optimal` are dropped. -/
theorem JointPreferenceBasinLow.toSenderPersistenceLow
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar_low sbar_low : ℝ}
    (hB : p.JointPreferenceBasinLow V_T V_S α xbar_low sbar_low) :
    p.SenderPersistenceBasinLow V_S α xbar_low sbar_low where
  xbar_low_le_one := hB.xbar_low_le_one
  sender_low_argmax_le_threshold := hB.sender_low_argmax_le_threshold
  top_rule_mono := hB.top_rule_mono

/-- **Row 3's hypothesis bundle yields the Sender low basin without its
Target field.** Built at `x̄ = min(xT⋆, xS⋆)` from `xT_star_mem`,
`sbar_star_mem` and `sender_dislikes_above_threshold` alone;
`target_dislikes_high_sanctions` is not read. (The bundle's former field
`xS_star_mem` was deleted in round BJ1.5, 2026-10-07, as read by nothing.) -/
theorem OneSidedSanctionLowBasinPreferenceThresholds.toSenderPersistenceLow
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xT_star xS_star sbar_star : ℝ}
    (hOne : p.OneSidedSanctionLowBasinPreferenceThresholds V_T V_S α
              xT_star xS_star sbar_star)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule V_S α)
        (Set.Icc (0 : ℝ) (min xT_star xS_star))) :
    p.SenderPersistenceBasinLow V_S α (min xT_star xS_star) sbar_star :=
  SenderPersistenceBasinLow.of_sender_dynamic_strictAnti p
    (le_trans (min_le_left _ _) hOne.xT_star_mem.2) hOne.sbar_star_mem
    (fun x hx => hOne.sender_dislikes_above_threshold x
      ⟨hx.1, le_trans hx.2 (min_le_right _ _)⟩)
    hTopMono

/-! ## Conclusions, general `F` -/

/-- **Kinematic layer — internal. Not an economic statement.**

From any low-basin start the general-`F` state path stays in `[0, x̄]`, the
realised sanction is bounded above by `s̄` and by `x̄`, and the sanction
sequence is non-increasing. `α` is arbitrary here, so the trajectory need not
be an equilibrium path; cite
`equilibriumTop_senderPersistenceLowF_long_run_with_evidence` instead. -/
theorem senderPersistenceBasinLowF_long_run_nonIncreasing
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar_low sbar_low x₀ : ℝ}
    (hB : p.SenderPersistenceBasinLow V_S α xbar_low sbar_low)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    (∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF V_S α x₀ n ≤ sbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF V_S α x₀ n ≤ xbar_low) ∧
    Antitone (p.dynamicTopLockInSanctionsF V_S α x₀) :=
  ⟨p.dynamicTopLockInPathF_mem_low_basin V_S α hB.xbar_low_le_one
     hB.sender_low_argmax_le_threshold hx₀,
   p.dynamicTopLockInSanctionsF_ceiling_low V_S α hB.xbar_low_le_one
     hB.sender_low_argmax_le_threshold hx₀,
   p.dynamicTopLockInSanctionsF_le_xbar_low V_S α hB.xbar_low_le_one
     hB.sender_low_argmax_le_threshold hx₀,
   p.dynamicTopLockInSanctionsF_anti_low V_S α hB.xbar_low_le_one
     hB.sender_low_argmax_le_threshold hB.top_rule_mono hx₀⟩

/-- **Anchored general-`F` low-basin persistence with equilibrium evidence,
no Target sanction preference.**

Along the path of an actual feedback Stackelberg equilibrium `E`, from every
start in the low basin `[0, x̄]`: the state stays in the basin, the realised
sanction stays at or below `s̄` and `x̄` and never rises; and at every date the
Target's action is feasible and maximises its full Bellman objective, and the
realised sanction maximises the Sender's forward-looking objective.

This is `jointPreferenceBasinLowF_long_run_with_equilibrium_evidence` minus
its last conjunct — the Target's sanction objective being non-increasing,
which is the one thing the deleted Target field paid for. Target feasibility
and optimality now come from `E` itself rather than from basin fields. -/
theorem equilibriumTop_senderPersistenceLowF_long_run_with_evidence
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar_low sbar_low x₀ : ℝ}
    (hB : p.SenderPersistenceBasinLow E.V_S E.α xbar_low sbar_low)
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ sbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ xbar_low) ∧
    Antitone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) ∧
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
    p.senderPersistenceBasinLowF_long_run_nonIncreasing hB hx₀
  have hmemS : ∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Sanctions.S :=
    fun n => ⟨(h1 n).1, le_trans (h1 n).2 hB.xbar_low_le_one⟩
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
  · intro n; exact E.α_mem _ (hmemS n)
  · intro n; exact E.α_opt_top _ (hmemS n)
  · intro n s' hs'
    exact p.σ_dyn_top_isMaxOn E.V_S
      (p.dynamicTopLockInPathF E.V_S E.α x₀ n)
      (E.α (p.dynamicTopLockInPathF E.V_S E.α x₀ n)) hs'

/-! ## The row-3 sibling -/

/-- **Low political absorbing basin, general `F`, from the Sender's pivot-star
level condition (round BH-2, 2026-10-06, BH2.6).**

Given a forward-looking feedback Stackelberg equilibrium `E`, a basin ceiling
`x̄ ≤ 1`, a sanction ceiling `s̄ ≥ 0`, and

* the Sender's pivot-star low-level input: at every state `x ∈ [0, x̄]` the
  Sender's forward-looking objective, at the Target's equilibrium action, is
  strictly higher at the pivot `min(x, s̄)` than at every heavier feasible
  sanction in `(min(x, s̄), 1]`;
* monotonicity of the Sender's greatest best response in the state on
  `[0, x̄]`,

then from every start in `[0, x̄]`: (i) the general-`F` state path stays in the
low basin forever; (ii) the realised sanction is at most `s̄`; (iii) it is at
most `x̄`; (iv) the realised sanction sequence is non-increasing.

In plain terms: if, wherever the political state is low, the Sender strictly
prefers the ceiling sanction to anything heavier, and its best response does not
fall as the state rises, then a low state stays low and sanctions only ease.

Dropped relative to the pinned sibling
`standardCompliance_low_basin_generalF_of_sender_level` (which is now a
corollary of this theorem): strict decrease of the objective on the whole
interval `[min(x, s̄), 1]` (only comparisons against the pivot are read) and
`s̄ ≤ 1` (only `0 ≤ s̄` is read; it is needed, since a negative ceiling would
contradict feasibility of the realised sanction). No Target hypothesis. General
in `F`. -/
theorem standardCompliance_low_basin_generalF_of_sender_star
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar_low sbar_low x₀ : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (hsbar_nn : 0 ≤ sbar_low)
    (h_star : ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
      ∀ s ∈ Set.Ioc (min x sbar_low) (1 : ℝ),
        p.senderDynObjective E.V_S x (E.α x) s
          < p.senderDynObjective E.V_S x (E.α x) (min x sbar_low))
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (0 : ℝ) xbar_low))
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ sbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ xbar_low) ∧
    Antitone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    p.equilibriumTop_senderPersistenceLowF_long_run_with_evidence E
      (SenderPersistenceBasinLow.of_pivot_beats_superpivot p hxbar_low_le_one
        hsbar_nn h_star hTopMono) hx₀
  exact ⟨h1, h2, h3, h4⟩

/-- **Low political absorbing basin, general `F`, from the Sender's level
condition alone.**

Row-3 sibling with no Target-preference hypothesis. Given a forward-looking
feedback Stackelberg equilibrium `E`, a basin ceiling `x̄ ≤ 1`, a feasible
sanction ceiling `s̄ ∈ [0, 1]`, and

* the Sender's strict low-level input: at every state `x ∈ [0, x̄]` the
  Sender's forward-looking objective, at the Target's equilibrium action, is
  strictly decreasing in the sanction on `[min(x, s̄), 1]`;
* monotonicity of the Sender's greatest best response in the state on
  `[0, x̄]`,

then from every start in `[0, x̄]`: (i) the general-`F` state path stays in the
low basin forever; (ii) the realised sanction is at most `s̄`; (iii) it is at
most `x̄`; (iv) the realised sanction sequence is non-increasing.

Row 3 is the case `x̄ = min(xT⋆, xS⋆)` (the `example` below). Its Target field
`target_dislikes_high_sanctions` is not a hypothesis here, and neither is the
second pivot's membership (the bundle no longer carries it since round BJ1.5).
General in `F`.

Since round BH-2 (2026-10-06, BH2.6) a one-line corollary of
`standardCompliance_low_basin_generalF_of_sender_star`, which reads only the
comparisons against the pivot and `0 ≤ s̄`. The statement is unchanged (it is a
pinned headline row). -/
theorem standardCompliance_low_basin_generalF_of_sender_level
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar_low sbar_low x₀ : ℝ}
    (hxbar_low_le_one : xbar_low ≤ 1)
    (hsbar_mem : sbar_low ∈ Sanctions.I)
    (h_sender_low :
      ∀ x ∈ Set.Icc (0 : ℝ) xbar_low,
        StrictAntiOn (fun s => p.senderDynObjective E.V_S x (E.α x) s)
          (Set.Icc (min x sbar_low) (1 : ℝ)))
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (0 : ℝ) xbar_low))
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) xbar_low) :
    (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc (0 : ℝ) xbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ sbar_low) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ xbar_low) ∧
    Antitone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) :=
  p.standardCompliance_low_basin_generalF_of_sender_star E hxbar_low_le_one hsbar_mem.1
    (fun x hx _ hs =>
      h_sender_low x hx ⟨le_rfl, hs.1.le.trans hs.2⟩ ⟨hs.1.le, hs.2⟩ hs.1)
    hTopMono hx₀

/-- Rule-13 check: headline row 3
(`standardCompliance_three_goals_local_low_basin_generalF`) is recovered, in
its exact statement, from the Sender-only sibling. The proof reads
`xT_star_mem`, `sbar_star_mem` and `sender_dislikes_above_threshold` from the
row-3 bundle and never `target_dislikes_high_sanctions`. -/
example
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT_star xS_star sbar_star x₀ : ℝ}
    (hOne : p.OneSidedSanctionLowBasinPreferenceThresholds E.V_T E.V_S E.α
              xT_star xS_star sbar_star)
    (hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
                  (Set.Icc (0 : ℝ) (min xT_star xS_star)))
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) :
    (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n
            ∈ Set.Icc (0 : ℝ) (min xT_star xS_star)) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ sbar_star) ∧
    (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n
            ≤ min xT_star xS_star) ∧
    Antitone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) :=
  p.standardCompliance_low_basin_generalF_of_sender_level E
    (le_trans (min_le_left _ _) hOne.xT_star_mem.2) hOne.sbar_star_mem
    (fun x hx => hOne.sender_dislikes_above_threshold x
      ⟨hx.1, le_trans hx.2 (min_le_right _ _)⟩)
    hTopMono hx₀

/-! ## Initial-condition selection, Sender side only -/

/-- **One equilibrium, two disjoint basins, no Target sanction preference on
either side.**

Sender-only sibling of `equilibriumTop_initial_condition_selects_generalF`:
the same equilibrium `E` carries a Sender high basin on `[x̄_high, 1]` and a
Sender low basin on `[0, x̄_low]` with `x̄_low < x̄_high`. Then the basins are
disjoint; every high start generates a general-`F` path that stays in the high
basin with a sanction floor and non-decreasing sanctions; every low start
generates one that stays in the low basin with a sanction ceiling and
non-increasing sanctions. Only the initial political state differs between the
two conclusions. Neither `JointPreferenceBasinTop.target_prefers_sanctions`
nor `JointPreferenceBasinLow.target_dislikes_sanctions` is assumed; the
original theorem follows by the two projections
`JointPreferenceBasinTop.toSenderPersistence` and
`JointPreferenceBasinLow.toSenderPersistenceLow`. General in `F`. -/
theorem equilibriumTop_initial_condition_selects_generalF_of_sender_basins
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar_high sbar_high xbar_low sbar_low : ℝ}
    (hHigh : p.SenderPersistenceBasinTop E.V_S E.α xbar_high sbar_high)
    (hLow : p.SenderPersistenceBasinLow E.V_S E.α xbar_low sbar_low)
    (hsep : xbar_low < xbar_high) :
    Disjoint (Set.Icc xbar_high 1) (Set.Icc 0 xbar_low) ∧
      (∀ x₀ ∈ Set.Icc xbar_high 1,
        (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc xbar_high 1) ∧
        (∀ n, sbar_high ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
        (∀ n, xbar_high ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
        Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀)) ∧
      (∀ x₀ ∈ Set.Icc 0 xbar_low,
        (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc 0 xbar_low) ∧
        (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ sbar_low) ∧
        (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ xbar_low) ∧
        Antitone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hxHigh hxLow
    linarith [hxHigh.1, hxLow.2]
  · intro x₀ hx₀
    obtain ⟨h1, h2, h3, h4, -⟩ :=
      p.equilibriumTop_senderPersistenceF_long_run_nonDecreasing E hHigh hx₀
    exact ⟨h1, h2, h3, h4⟩
  · intro x₀ hx₀
    obtain ⟨h1, h2, h3, h4, -⟩ :=
      p.equilibriumTop_senderPersistenceLowF_long_run_with_evidence E hLow hx₀
    exact ⟨h1, h2, h3, h4⟩

/-- Rule-13 check: `equilibriumTop_initial_condition_selects_generalF` is
recovered, in its exact statement, through the Sender-only sibling and the
two projections. -/
example
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar_high sbar_high xbar_low sbar_low : ℝ}
    (hHigh : p.JointPreferenceBasinTop E.V_T E.V_S E.α xbar_high sbar_high)
    (hLow : p.JointPreferenceBasinLow E.V_T E.V_S E.α xbar_low sbar_low)
    (hsep : xbar_low < xbar_high) :
    Disjoint (Set.Icc xbar_high 1) (Set.Icc 0 xbar_low) ∧
      (∀ x₀ ∈ Set.Icc xbar_high 1,
        (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc xbar_high 1) ∧
        (∀ n, sbar_high ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
        (∀ n, xbar_high ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
        Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀)) ∧
      (∀ x₀ ∈ Set.Icc 0 xbar_low,
        (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc 0 xbar_low) ∧
        (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ sbar_low) ∧
        (∀ n, p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n ≤ xbar_low) ∧
        Antitone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀)) :=
  p.equilibriumTop_initial_condition_selects_generalF_of_sender_basins E
    (JointPreferenceBasinTop.toSenderPersistence p hHigh)
    (JointPreferenceBasinLow.toSenderPersistenceLow p hLow) hsep

end Params
end AbstractGame

end

end Sanctions

-- The axiom report below names declarations in full; several names pass the
-- 100-character line limit, which is accepted for these report lines only.
set_option linter.style.longLine false

#print axioms Sanctions.AbstractGame.Params.SenderPersistenceBasinLow.argmax_le
#print axioms Sanctions.AbstractGame.Params.SenderPersistenceBasinLow.of_every_argmax_le
#print axioms Sanctions.AbstractGame.Params.SenderPersistenceBasinLow.of_pivot_beats_superpivot
#print axioms Sanctions.AbstractGame.Params.SenderPersistenceBasinLow.of_sender_dynamic_strictAnti
#print axioms Sanctions.AbstractGame.Params.SenderPersistenceBasinLow.of_stage_sender_strictAnti
#print axioms Sanctions.AbstractGame.Params.JointPreferenceBasinLow.toSenderPersistenceLow
#print axioms Sanctions.AbstractGame.Params.OneSidedSanctionLowBasinPreferenceThresholds.toSenderPersistenceLow
#print axioms Sanctions.AbstractGame.Params.senderPersistenceBasinLowF_long_run_nonIncreasing
#print axioms Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceLowF_long_run_with_evidence
#print axioms Sanctions.AbstractGame.Params.standardCompliance_low_basin_generalF_of_sender_star
#print axioms Sanctions.AbstractGame.Params.standardCompliance_low_basin_generalF_of_sender_level
#print axioms Sanctions.AbstractGame.Params.equilibriumTop_initial_condition_selects_generalF_of_sender_basins
