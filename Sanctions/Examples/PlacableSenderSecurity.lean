/-
Sanctions/Examples/PlacableSenderSecurity.lean

**The Target's security bound: under the loss-offset margin no sanction
sequence pushes the Target below its permanent-relief payoff** (round BB,
2026-09-28; doc 110 item C2a, the coercion theorem).

## What this file proves

Fix a chord economy, a start `x₀ ∈ [0,1]` and **any** sanction sequence
`s : ℕ → [0,1]` (open loop: the Sender's choices need not come from any rule).
The state moves by `x_{t+1} = F(x_t, s_t)` (`episodePath`; compliance does not
move the state). Let `W(x₀)` be the Target's discounted payoff from always
defying under permanent relief (`s ≡ 0`; the path is `reliefState`).

1. **The security gap** (`reliefPayoff_add_le_defiancePayoff`, no margin):
   the Target's payoff from always defying against `s` is at least
   `W(x₀) + (β_T·d_lo·g_T⁰ − c)·Σ β_T^t s_t`, with `g_T⁰ = v_lo/(1 − β_T·g_lo)`.
   The derivation: the gap `e_t = x_t − x'_t` between the sanctioned path and
   the relief path starts at `0` and obeys `e_{t+1} ≥ g_lo·e_t + d_lo·s_t`
   (the lower state chord at sanction `0` plus the lower sanction chord); the
   stage gap is at least `v_lo·e_t − c·s_t` (T6 at sanction `0`, T4); summing
   with weights `β_T^t` (the chord-sum inequality of
   `Foundations/DiscountedChordSum`) gives the bound.
2. **The security bound** (`reliefPayoff_le_defiancePayoff`): under the
   unrefined loss-offset margin `LossOffset₀` (`c ≤ β_T·d_lo·g_T⁰` — the
   Target's marginal sanction pain is covered by the discounted value of the
   entrenchment the sanction produces), always defying earns at least `W(x₀)`
   against every sanction sequence.
3. **Attainment** (`targetPathPayoff_relief_add_cost_le`): against permanent
   relief every compliance sequence earns at most `W(x₀)` less its discounted
   compliance cost (T2: compliance costs at least `ℓ_lo` per unit, and it does
   not move the state). Hence (`reliefPayoff_isLeast`) `W(x₀)` is the least
   payoff ceiling the Sender can impose on the Target with a pure open-loop
   sanction sequence: the Target's minmax over such sequences, attained by
   relief.
4. **The equilibrium corollary** (`reliefPayoff_le_V_T`): under `LossOffset₀`,
   every top-selector
   feedback Stackelberg equilibrium has `W(x₀) ≤ V_T(x₀)` at every feasible
   state, and (`compliance_for_relief_add_cost_le_V_T`) a compliance sequence
   paired with zero sanctions at every date gives the Target at most its
   equilibrium value less the discounted compliance cost — strictly less when
   it ever complies (`compliance_for_relief_lt_V_T`). The route: the Target's
   value weakly exceeds its joint integrand at full defiance (its policy is an
   argmax, `target_one_shot_deviation_top`); along the path on which the Target
   defies at every date and the Sender answers with its equilibrium response
   `σ_dyn_top V_S`, this one-step inequality sums, by boundedness, to
   `V_T(x₀) ≥` the defiance payoff against that sanction sequence
   (`Foundations/DiscountedChordSum.tsum_pow_mul_le_of_le_add_mul_succ`), which
   is `≥ W(x₀)` by item 2.

## Scope (Rules 1 and 9)

* Items 1–3 are statements about a **fixed Target plan** (always defy) against
  an arbitrary open-loop Sender sequence, and about arbitrary compliance
  sequences against relief. They are security-level lemmas, not equilibrium
  statements (Rule 1); the paper-facing results are their equilibrium
  corollaries in item 4.
* Item 4 quantifies over **all** top-selector feedback Stackelberg equilibria
  (`FeedbackStackelbergEquilibriumTop`: continuous Markov policies, the Sender
  answering with the greatest dynamic argmax), with **no class restriction**
  on the equilibrium, given the economy-level margin `LossOffset₀`:
  no monotonicity of the policy or the rule, no placability, no rally margin,
  no zero-sanction neutrality. It is a **bound, not a characterisation**: it
  says nothing about which equilibria exist or how many.
* "Compliance for relief is never individually rational" is proved only for
  compliance paired with **zero sanctions at every date**. Under the margin
  sanctions *raise* the Target's defiance payoff (item 1), so a deal that
  rewards compliance with positive sanctions is not covered.
* The minmax of item 3 is over pure open-loop sanction sequences. A
  history-dependent pure Sender strategy played against the always-defy plan
  induces one such sequence, so the security bound applies to it as well. That
  remark is proved, in a two-sided form (minmax and maxmin over pure
  history-dependent strategies on both sides), in
  `PlacableSenderSecurityHistory.lean` (round BD).

Rule 22: **general in `F`** — only the chord conditions of the chord economy
(the lower state chord `g_lo`, the lower sanction chord `d_lo`) and
`F`-feasibility are read. Rule 3: **no new assumption** — `LossOffset₀` is the
existing definition of `PlacableSenderUniqueness.lean`, used as a hypothesis on
the quantifier as there; `targetPathPayoff`, `defiancePayoff`, `reliefPayoff`,
`defiancePath`, `defianceSanction` are definitions, not hypotheses. Rule 9B:
the margin holds at the quartic member `qwDefiance`, outside the
quadratic–linear family and non-affine in `F` (`qwDefiance_security_margin`),
and the equilibrium corollary is instantiated at its constructed equilibrium
(`qwDefiance_reliefPayoff_le_V_T`); that is existence only.

This is the permanent-relief (`T = ∞`) counterpart of
`prop:relief-participation`'s Target half
(`PlacableSenderReliefParticipation.lean`, `targetReliefValue_add_cost_le`:
finite relief spells followed by the constructed equilibrium, under the
refined margin and a monotone response). It holds at every top-selector
equilibrium rather than the constructed one, at the price of the unrefined
margin `LossOffset₀`. Finite spells followed by equilibrium play are not
covered here: they would need a lower slope on the equilibrium value, which an
arbitrary equilibrium does not supply. Neither result implies the other.

**Since renovation item BH3.6 (2026-10-06) the theorems here are corollaries** of
their `Params`-level forms in `Theory/Equilibrium/SecurityCore.lean`, with their
statements unchanged; the derivations sketched above are that file's. The core
holds over any economy with the zero-section state chord, the sanction lower chord
from zero, the Target's three bounds at the one level where each is read (T6 at full
defiance and zero sanction, T4 at full defiance, T2 against a zero sanction) and the
margin, for any Sender objective. The chord economy supplies them through
`security_band0`, `security_sanction0`, `security_state0`, `security_pain0` and
`security_cost0`. The generality is witnessed (Rule 9B) at `ocParams`, whose Target
payoff no chord economy has (`oc_security_outside_chord_class`, the last section).
-/
import Sanctions.Examples.PlacableSenderUniqueness
import Sanctions.Examples.PlacableSenderReliefParticipation
import Sanctions.Examples.ChordEconomyQuarticWitness
import Sanctions.Foundations.DiscountedChordSum
import Sanctions.Theory.Equilibrium.SecurityCore
import Sanctions.Examples.DefianceCoreOutsideChordWitness

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
open Sanctions.Foundations.DiscountedChordSum

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 1. Payoffs along an open-loop sanction sequence -/

/-- **The Target's discounted payoff** from the compliance sequence `a` when the
Sender imposes the sanction sequence `s` from the start `x₀`. The state follows
`x_{t+1} = F(x_t, s_t)` (`episodePath`): compliance does not move it. -/
def targetPathPayoff (a s : ℕ → ℝ) (x₀ : ℝ) : ℝ :=
  ∑' t, E.β_T ^ t * E.toParams.U_T (E.toParams.episodePath s x₀ t) (a t) (s t)

/-- The Target's payoff from **always defying** (`a_t = 0` at every date)
against the sanction sequence `s`. -/
def defiancePayoff (s : ℕ → ℝ) (x₀ : ℝ) : ℝ := E.targetPathPayoff (fun _ => 0) s x₀

/-- **The permanent-relief payoff** `W(x₀)`: always defying against zero
sanctions at every date. -/
def reliefPayoff (x₀ : ℝ) : ℝ := E.defiancePayoff (fun _ => 0) x₀

/-- `W(x₀)` is the discounted defiance payoff along the relief path of
`PlacableSenderReliefParticipation.lean`. -/
theorem reliefPayoff_eq (x₀ : ℝ) :
    E.reliefPayoff x₀ = ∑' t, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) 0 0 := rfl

/-- The Target's payoff series converges for feasible sequences. The corollary of
`AbstractGame.Params.summable_targetPath` (BH3.6). -/
theorem summable_targetPath {a s : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I)
    (hs : ∀ t, s t ∈ Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Summable (fun t => E.β_T ^ t * E.toParams.U_T (E.toParams.episodePath s x₀ t) (a t) (s t)) :=
  E.toParams.summable_targetPath ha hs hx₀

/-! ### The chord economy satisfies the security core's hypotheses (BH3.6)

Each lemma restates one chord-economy field at the level where
`Theory/Equilibrium/SecurityCore.lean` reads it. General in `F`. -/

/-- The lower state chord along the zero-sanction section (from `hbandAll`). -/
theorem security_band0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
    E.glo * (y₂ - y₁) ≤ E.F y₂ 0 - E.F y₁ 0 :=
  fun y₁ hy₁ y₂ hy₂ hle => (E.hbandAll 0 zero_mem_I y₁ hy₁ y₂ hy₂ hle).1

/-- The lower sanction chord from a zero sanction (from `hSlo`). -/
theorem security_sanction0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
    E.dlo * s ≤ E.F x s - E.F x 0 :=
  E.toParams.sanctionLowerChord_from_zero E.hSlo

/-- T4 at full defiance, from a zero sanction: a sanction `s` costs at most `c·s`. -/
theorem security_pain0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
    E.U_T x 0 0 - E.U_T x 0 s ≤ E.c * s := by
  intro x hx s hs
  have h := E.hUT_painHi x hx 0 zero_mem_I 0 zero_mem_I s hs hs.1
  linarith

/-- T6 at full defiance and zero sanction: the state is worth at least `v_lo` per
unit. -/
theorem security_state0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
    E.vlo * (y₂ - y₁) ≤ E.U_T y₂ 0 0 - E.U_T y₁ 0 0 := by
  intro y₁ hy₁ y₂ hy₂ hle
  have h := E.hUT_stateLo 0 zero_mem_I 0 zero_mem_I y₁ hy₁ y₂ hy₂ hle
  linarith

/-- T2 against a zero sanction: compliance `a` costs at least `ℓ_lo·a`. -/
theorem security_cost0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
    E.ℓlo * a ≤ E.U_T x 0 0 - E.U_T x a 0 := by
  intro x hx a ha
  have h := E.hUT_costLo x hx 0 zero_mem_I 0 zero_mem_I a ha ha.1
  linarith

/-- The sign of T2 against a zero sanction: compliance is weakly costly. -/
theorem security_costSign0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
    E.U_T x a 0 ≤ E.U_T x 0 0 := by
  intro x hx a ha
  have h := E.security_cost0 x hx a ha
  have := mul_nonneg E.hℓlo.le ha.1
  linarith

/-! ## 2. The security gap and the security bound -/

/-- **The security gap.** For every feasible start and every feasible sanction
sequence `s`, the Target's payoff from always defying against `s` is at least
its permanent-relief payoff plus `(β_T·d_lo·g_T⁰ − c)` times the discounted sum
of the sanctions. No margin is assumed: the sign of the coefficient is left
open. General in `F`. A lemma about a fixed Target plan (Rule 1). Since BH3.6 the
corollary of `AbstractGame.Params.reliefPayoff_add_le_defiancePayoff`, which reads
only the zero-section state chord, the sanction chord from zero, and T6 and T4 at
full defiance. -/
theorem reliefPayoff_add_le_defiancePayoff {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {s : ℕ → ℝ}
    (hs : ∀ t, s t ∈ Sanctions.I) :
    E.reliefPayoff x₀ + (E.β_T * E.dlo * E.gT₀ - E.c) * ∑' t, E.β_T ^ t * s t
      ≤ E.defiancePayoff s x₀ :=
  E.toParams.reliefPayoff_add_le_defiancePayoff E.security_band0 E.security_sanction0
    E.security_pain0 E.security_state0 E.hvlo.le hx₀ hs

/-- **The Target's security bound.** Under the unrefined loss-offset margin
`LossOffset₀` (`c ≤ β_T·d_lo·g_T⁰`: the Target's marginal sanction pain is at
most the discounted value of the entrenchment a unit of sanction produces),
always defying earns the Target at least its permanent-relief payoff `W(x₀)`,
against **every** feasible sanction sequence. General in `F`. A security level
for a fixed Target plan, a lemma (Rule 1); the equilibrium statement is
`reliefPayoff_le_V_T`. Since BH3.6 the corollary of
`AbstractGame.Params.reliefPayoff_le_defiancePayoff`. -/
theorem reliefPayoff_le_defiancePayoff (hTM : E.LossOffset₀) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {s : ℕ → ℝ} (hs : ∀ t, s t ∈ Sanctions.I) :
    E.reliefPayoff x₀ ≤ E.defiancePayoff s x₀ :=
  E.toParams.reliefPayoff_le_defiancePayoff E.security_band0 E.security_sanction0
    E.security_pain0 E.security_state0 E.hvlo.le hTM hx₀ hs

/-! ## 3. Attainment: relief is the harshest open-loop punishment -/

/-- **Against permanent relief, compliance only costs.** For every feasible
compliance sequence `a`, the Target's payoff against zero sanctions at every
date plus its discounted compliance cost `ℓ_lo·Σ β_T^t a_t` is at most `W(x₀)`:
with the sanction fixed at zero, compliance moves neither the state nor the
sanction and costs at least `ℓ_lo` per unit (T2). No margin. General in `F`. Since
BH3.6 the corollary of `AbstractGame.Params.targetPathPayoff_relief_add_cost_le`,
which reads T2 against a zero sanction only. -/
theorem targetPathPayoff_relief_add_cost_le {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ}
    (ha : ∀ t, a t ∈ Sanctions.I) :
    E.targetPathPayoff a (fun _ => 0) x₀ + E.ℓlo * ∑' t, E.β_T ^ t * a t
      ≤ E.reliefPayoff x₀ :=
  E.toParams.targetPathPayoff_relief_add_cost_le E.security_cost0 hx₀ ha

/-- Against permanent relief no compliance sequence beats always defying. General in
`F`. Since BH3.6 the corollary of `AbstractGame.Params.targetPathPayoff_relief_le`,
which reads only the sign of T2 against a zero sanction. -/
theorem targetPathPayoff_relief_le {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ}
    (ha : ∀ t, a t ∈ Sanctions.I) :
    E.targetPathPayoff a (fun _ => 0) x₀ ≤ E.reliefPayoff x₀ :=
  E.toParams.targetPathPayoff_relief_le E.security_costSign0 hx₀ ha

/-- **`W(x₀)` is the Target's minmax over pure open-loop sanction sequences,
attained by relief.** Among the payoff ceilings the Sender can impose — numbers
`v` for which some feasible sanction sequence holds every feasible compliance
sequence of the Target to at most `v` — the least is `W(x₀)`: relief imposes it
(`targetPathPayoff_relief_le`), and no sequence imposes less, because always
defying earns at least `W(x₀)` against any of them
(`reliefPayoff_le_defiancePayoff`, under `LossOffset₀`). General in `F`. Since BH3.6
the corollary of `AbstractGame.Params.reliefPayoff_isLeast`. -/
theorem reliefPayoff_isLeast (hTM : E.LossOffset₀) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    IsLeast {v : ℝ | ∃ s : ℕ → ℝ, (∀ t, s t ∈ Sanctions.I) ∧
        ∀ a : ℕ → ℝ, (∀ t, a t ∈ Sanctions.I) → E.targetPathPayoff a s x₀ ≤ v}
      (E.reliefPayoff x₀) :=
  E.toParams.reliefPayoff_isLeast E.security_band0 E.security_sanction0 E.security_pain0
    E.security_state0 E.hvlo.le E.security_costSign0 hTM hx₀

/-! ## 4. Every top-selector equilibrium -/

/-- The state path on which the Target defies at every date and the Sender
answers with its equilibrium response `σ_dyn_top V_S` (the greatest maximiser
of its dynamic objective at the equilibrium's own Sender value): the path of
the Target's full-defiance deviation. -/
def defiancePath (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | t + 1 => E.F (defiancePath Eq x₀ t) (E.toParams.σ_dyn_top Eq.V_S (defiancePath Eq x₀ t) 0)

/-- The Sender's equilibrium response to defiance along `defiancePath`. -/
def defianceSanction (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (x₀ : ℝ) (t : ℕ) : ℝ :=
  E.toParams.σ_dyn_top Eq.V_S (E.defiancePath Eq x₀ t) 0

theorem defianceSanction_mem (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (x₀ : ℝ)
    (t : ℕ) : E.defianceSanction Eq x₀ t ∈ Sanctions.I :=
  E.toParams.σ_dyn_top_mem_I _ _ _

/-- The deviation path is the state path of its own sanction sequence. -/
theorem episodePath_defianceSanction (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (x₀ : ℝ) (t : ℕ) :
    E.toParams.episodePath (E.defianceSanction Eq x₀) x₀ t = E.defiancePath Eq x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Params.episodePath_succ, ih]
    rfl

/-- The deviation path is the `Params`-level one of `SecurityCore` (BH3.6). -/
theorem defiancePath_eq_params (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (x₀ : ℝ)
    (t : ℕ) : E.defiancePath Eq x₀ t = E.toParams.defiancePath Eq x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change E.F (E.defiancePath Eq x₀ t) (E.toParams.σ_dyn_top Eq.V_S (E.defiancePath Eq x₀ t) 0)
      = E.toParams.F (E.toParams.defiancePath Eq x₀ t)
          (E.toParams.σ_dyn_top Eq.V_S (E.toParams.defiancePath Eq x₀ t) 0)
    rw [ih]

/-- The deviation's sanctions are the `Params`-level ones of `SecurityCore` (BH3.6). -/
theorem defianceSanction_eq_params (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (x₀ : ℝ) : E.defianceSanction Eq x₀ = E.toParams.defianceSanction Eq x₀ := by
  funext t
  change E.toParams.σ_dyn_top Eq.V_S (E.defiancePath Eq x₀ t) 0
    = E.toParams.σ_dyn_top Eq.V_S (E.toParams.defiancePath Eq x₀ t) 0
  rw [E.defiancePath_eq_params]

/-- **The Target's value dominates its full-defiance deviation.** At every
top-selector equilibrium and every feasible start, the Target's value is at
least its discounted payoff from defying at every date against the Sender's
equilibrium responses. The Target's policy is an argmax of its joint integrand
(`target_one_shot_deviation_top`), so the one-step inequality holds at every
date; it sums by boundedness. No class restriction, no margin. General in
`F`. Since BH3.6 the corollary of `AbstractGame.Params.defiancePayoff_le_V_T`, which
holds at every top-selector equilibrium of any economy. -/
theorem defiancePayoff_le_V_T (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    E.defiancePayoff (E.defianceSanction Eq x₀) x₀ ≤ Eq.V_T ⟨x₀, hx₀⟩ := by
  rw [E.defianceSanction_eq_params]
  exact E.toParams.defiancePayoff_le_V_T Eq hx₀

/-- **The security gap at every equilibrium.** At every top-selector
equilibrium and every feasible start, `V_T(x₀) ≥ W(x₀) + (β_T·d_lo·g_T⁰ − c)`
times the discounted sanctions the Sender's equilibrium response would impose on
a Target that defied at every date. No margin, no class restriction. General in
`F`. Since BH3.6 the corollary of `AbstractGame.Params.reliefPayoff_add_le_V_T`. -/
theorem reliefPayoff_add_le_V_T (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    E.reliefPayoff x₀
        + (E.β_T * E.dlo * E.gT₀ - E.c) * ∑' t, E.β_T ^ t * E.defianceSanction Eq x₀ t
      ≤ Eq.V_T ⟨x₀, hx₀⟩ := by
  rw [E.defianceSanction_eq_params]
  exact E.toParams.reliefPayoff_add_le_V_T E.security_band0 E.security_sanction0
    E.security_pain0 E.security_state0 E.hvlo.le Eq hx₀

/-- **Every top-selector equilibrium gives the Target at least its
permanent-relief payoff** (the coercion theorem). Under the unrefined
loss-offset margin `LossOffset₀`, for **every**
`FeedbackStackelbergEquilibriumTop` of a chord economy and every feasible state
`x₀`, `W(x₀) ≤ V_T(x₀)`. Over all top-selector equilibria (continuous Markov
policies), with no class restriction; a bound, not a characterisation. General
in `F`. A pinned headline, kept verbatim; since BH3.6 the corollary of
`AbstractGame.Params.reliefPayoff_le_V_T`, which holds over any economy with the
zero-section state chord, the sanction chord from zero, T6 and T4 at full defiance
and the margin, for any Sender objective. -/
theorem reliefPayoff_le_V_T (hTM : E.LossOffset₀)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    E.reliefPayoff x₀ ≤ Eq.V_T ⟨x₀, hx₀⟩ :=
  E.toParams.reliefPayoff_le_V_T E.security_band0 E.security_sanction0 E.security_pain0
    E.security_state0 E.hvlo.le hTM Eq hx₀

/-- **Compliance paired with permanent relief is worth at most the equilibrium
value less the compliance cost.** Under `LossOffset₀`, at every top-selector
equilibrium and every feasible start, a feasible compliance sequence `a` paired
with **zero sanctions at every date** gives the Target at most `V_T(x₀)` less
its discounted compliance cost `ℓ_lo·Σ β_T^t a_t`. Covers compliance paired
with zero sanctions only: a deal rewarding compliance with positive sanctions is
not covered. General in `F`. Since BH3.6 the corollary of
`AbstractGame.Params.compliance_for_relief_add_cost_le_V_T`. -/
theorem compliance_for_relief_add_cost_le_V_T (hTM : E.LossOffset₀)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) :
    E.targetPathPayoff a (fun _ => 0) x₀ + E.ℓlo * ∑' t, E.β_T ^ t * a t
      ≤ Eq.V_T ⟨x₀, hx₀⟩ :=
  E.toParams.compliance_for_relief_add_cost_le_V_T E.security_band0 E.security_sanction0
    E.security_pain0 E.security_state0 E.hvlo.le E.security_cost0 hTM Eq hx₀ ha

/-- **Compliance for permanent relief is never individually rational.** Under
`LossOffset₀`, if the compliance sequence ever complies (`a_t > 0` at some
date), pairing it with zero sanctions at every date gives the Target strictly
less than its value at any top-selector equilibrium. Covers compliance paired
with zero sanctions only. General in `F`. -/
theorem compliance_for_relief_lt_V_T (hTM : E.LossOffset₀)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {t₀ : ℕ} (ht₀ : 0 < a t₀) :
    E.targetPathPayoff a (fun _ => 0) x₀ < Eq.V_T ⟨x₀, hx₀⟩ := by
  have h := E.compliance_for_relief_add_cost_le_V_T hTM Eq hx₀ ha
  have hB : Summable (fun t => E.β_T ^ t * a t) :=
    summable_pow_mul_of_abs_le E.hβT0.le E.hβT1 (M := 1)
      (fun t => by rw [abs_le]; constructor <;> linarith [(ha t).1, (ha t).2])
  have hpos : 0 < ∑' t, E.β_T ^ t * a t :=
    hB.tsum_pos (fun t => mul_nonneg (pow_nonneg E.hβT0.le t) (ha t).1) t₀
      (mul_pos (pow_pos E.hβT0 t₀) ht₀)
  have := mul_pos E.hℓlo hpos
  linarith

end ChordEconomy

/-! ## Non-vacuity (Rule 9B): the quartic member

`qwDefiance` is the chord economy of `ChordEconomyQuarticWitness.lean` at
`β_T = 1/2`: outside the quadratic–linear family and non-affine in `F`
(`quadDiagF`). Existence only (Rule 9A). -/

/-- **The unrefined loss-offset margin holds at the quartic member**:
`c = 9/2 ≤ β_T·d_lo·v_lo/(1 − β_T·g_lo) = (1/2)(2/5)·28/(4/5) = 7`. So the
security bound's hypotheses are jointly satisfiable outside the family.

This is the same fact as `qwDefiance_lossOffset₀` in
`PlacableSenderDefianceCore.lean`; it is kept so this file does not import
that one. -/
theorem qwDefiance_security_margin : qwDefiance.toChordEconomy.LossOffset₀ := by
  change (9 / 2 : ℝ) ≤ 1 / 2 * (2 / 5) * (28 / (1 - 1 / 2 * (2 / 5)))
  norm_num

/-- **The coercion theorem at the quartic member's constructed equilibrium**:
there `W(x₀) ≤ V_T(x₀)` at every feasible state. -/
theorem qwDefiance_reliefPayoff_le_V_T {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    qwDefiance.toChordEconomy.reliefPayoff x₀
      ≤ (qwDefiance.equilibriumTop_of_margin qwDefiance_lossOffset
          (qw_rallyMargin _ _ _)).V_T ⟨x₀, hx₀⟩ :=
  qwDefiance.toChordEconomy.reliefPayoff_le_V_T qwDefiance_security_margin _ hx₀

/-! ## The generality witness (Rule 9B, BH3.6): an economy outside the chord class

`ocParams` (`DefianceCoreOutsideChordWitness.lean`) has the affine transition at rate
`1/2` and a Target whose compliance cost `a + 10·a·(1 − a)` is at least `a` but not
monotone, so no chord economy has its Target payoff (`oc_not_chord`). It satisfies the
hypotheses of `Theory/Equilibrium/SecurityCore.lean` with `g_lo = d_lo = 1/2`, `v = 3`,
`c = 1`, and the margin binds (`oc_margin`). Existence only (Rule 9A). Rule 22:
AFFINE TRANSITION in this witness; the generality it witnesses is in the Target's
payoff, the theorem it instantiates is general in `F`. -/

/-- **The coercion theorem outside the chord class**: no chord economy has `ocParams`'s
Target payoff, and at every top-selector equilibrium of `ocParams` and every feasible
state, `W(x₀) ≤ V_T(x₀)` (`AbstractGame.Params.reliefPayoff_le_V_T`). -/
theorem oc_security_outside_chord_class :
    (¬ ∃ E : ChordEconomy, E.U_T = ocParams.U_T) ∧
      ∀ (Q : ocParams.FeedbackStackelbergEquilibriumTop) (x₀ : ℝ) (hx₀ : x₀ ∈ Sanctions.I),
        ocParams.reliefPayoff x₀ ≤ Q.V_T ⟨x₀, hx₀⟩ := by
  refine ⟨oc_not_chord, fun Q x₀ hx₀ => ?_⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine ocParams.reliefPayoff_le_V_T
    (fun y₁ hy₁ y₂ hy₂ hle => oc_band 0 h0 y₁ hy₁ y₂ hy₂ hle)
    (ocParams.sanctionLowerChord_from_zero oc_Slo) (fun x hx s hs => ?_)
    (fun y₁ hy₁ y₂ hy₂ hle => oc_state 0 h0 y₁ hy₁ y₂ hy₂ hle) (by norm_num) oc_margin Q hx₀
  have h := oc_pain x hx 0 h0 s hs hs.1
  simp only at h
  linarith

end

#print axioms Sanctions.Examples.ChordEconomy.reliefPayoff_eq
#print axioms Sanctions.Examples.ChordEconomy.summable_targetPath
#print axioms Sanctions.Examples.ChordEconomy.security_band0
#print axioms Sanctions.Examples.ChordEconomy.security_sanction0
#print axioms Sanctions.Examples.ChordEconomy.security_pain0
#print axioms Sanctions.Examples.ChordEconomy.security_state0
#print axioms Sanctions.Examples.ChordEconomy.security_cost0
#print axioms Sanctions.Examples.ChordEconomy.security_costSign0
#print axioms Sanctions.Examples.ChordEconomy.reliefPayoff_add_le_defiancePayoff
#print axioms Sanctions.Examples.ChordEconomy.reliefPayoff_le_defiancePayoff
#print axioms Sanctions.Examples.ChordEconomy.targetPathPayoff_relief_add_cost_le
#print axioms Sanctions.Examples.ChordEconomy.targetPathPayoff_relief_le
#print axioms Sanctions.Examples.ChordEconomy.reliefPayoff_isLeast
#print axioms Sanctions.Examples.ChordEconomy.defianceSanction_mem
#print axioms Sanctions.Examples.ChordEconomy.episodePath_defianceSanction
#print axioms Sanctions.Examples.ChordEconomy.defiancePath_eq_params
#print axioms Sanctions.Examples.ChordEconomy.defianceSanction_eq_params
#print axioms Sanctions.Examples.ChordEconomy.defiancePayoff_le_V_T
#print axioms Sanctions.Examples.ChordEconomy.reliefPayoff_add_le_V_T
#print axioms Sanctions.Examples.ChordEconomy.reliefPayoff_le_V_T
#print axioms Sanctions.Examples.ChordEconomy.compliance_for_relief_add_cost_le_V_T
#print axioms Sanctions.Examples.ChordEconomy.compliance_for_relief_lt_V_T
#print axioms Sanctions.Examples.qwDefiance_security_margin
#print axioms Sanctions.Examples.qwDefiance_reliefPayoff_le_V_T
#print axioms Sanctions.Examples.oc_security_outside_chord_class

end Examples
end Sanctions
