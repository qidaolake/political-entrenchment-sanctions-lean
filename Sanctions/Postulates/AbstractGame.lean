/-
Sanctions/Postulates/AbstractGame.lean

**Abstract two-player dynamic game on a shared scalar state.**

This module is the *abstract core* of the Sanctions formalization.
Concrete instantiations (e.g. a bilateral LQ specification) provide
specific `U_T`, `U_S`, `σ` functions; the abstract Bellman theory in
`Theory/Bilateral/BellmanT.lean` and `BellmanS.lean` is built
generically on this structure.

**Architecture (2026-05-23 abstraction).** The earlier
`Sanctions.Bilateral.Params` hard-coded a 17-coefficient LQ
specification with `U_T`, `U_S`, `σ_raw` as derived defs. That
specification has been demoted from "core model" to "one
instantiation"; this module replaces it as the abstract structure on
which all theory is layered.

**Rule-1 compliance.** `σ_isMaxOn_U_S` couples the abstract Sender
stage selector `σ` to `U_S` as the Sender's stage-game argmax (not an
arbitrary function): the supplied comparator is feasible and stage-optimal
(its joint continuity is the separate condition
`Params.StaticSelectorContinuous`, since round BJ5.1). That is what the
structure certifies on the Sender side,
and no more — the forward-looking Sender response (`σ_dyn`, `σ_dyn_top`)
and the joint equilibrium are constructed and verified by the downstream
objects that consume this structure, and a theorem stated over `Params`
solves the joint game only where it says so (wording corrected
2026-09-11, the reader's C11). On the
Target side, the abstract Bellman theory delivers the optimal policy
as the argmax of the Bellman integrand (existence via
`verification_target_exists` in `Theory/Bellman/Verification.lean`),
which is the canonical equilibrium-derived form.

**Rule-3 status.** This structure is the user-approved replacement
for `Bilateral.Params`. It introduces new abstract function fields
and structural hypotheses, but every concrete `Bilateral.Params` it
displaces was strictly LQ-specific — the abstract version
*generalizes* (every LQ instantiation satisfies the new hypotheses;
no LQ-specific hypothesis is needed in the abstract layer).
-/

import Sanctions.Foundations.Basic
import Sanctions.Foundations.DiagonalMonotone
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.Filter.Extr

namespace Sanctions
namespace AbstractGame

open Set

/-- **An abstract two-player dynamic game with a single shared scalar
state.**

The environment has one political state `x ∈ [0, 1]`, a Target
compliance action `a ∈ [0, 1]`, and a Sender sanction `s ∈ [0, 1]`.
State transitions are `x' = F(x, s)`, where `s` is the Sender sanction
selected in the relevant problem (the static / myopic stage selector
`σ(x, a)` in the myopic comparator, and the forward-looking dynamic
selector `σ_dyn` / `σ_dyn_top` in the Stackelberg equilibrium — see
`Theory.Equilibrium.JointMPE` and `Theory.LockIn.SigmaDynComparison`).
The paper-facing maintained restriction that `F` moves strictly toward
`s` off the diagonal is stated transparently as `Params.StrictAdjustment`
below. Both players have discount factors `(β_T, β_S) ∈ [0, 1)`.

The field `σ` is the **static / myopic Sender stage selector** used
for the static-sanctions stage comparator (the myopic comparator in
`MyopicFeedbackEquilibrium`). The forward-looking Sender response
used in the Stackelberg equilibrium is constructed downstream as
`p.σ_dyn V_S x a` (and its top-selector variant `p.σ_dyn_top`) from
the Sender continuation value `V_S`; `σ` is not the equilibrium
Sender response.

The fields `U_T`, `U_S`, `σ` are *abstract function fields* (no closed
form). Structural hypotheses (continuity on `ℝ³`, σ-feasibility in
`[0,1]`, σ-consistency with `U_S` as the Sender stage argmax) make
the abstract Bellman theory available; the Target's Bellman value against
the static selector also needs `[p.StaticSelectorContinuous]`. Concrete instantiations (e.g.
a six-monomial LQ specification) supply specific formulas and prove
the structural hypotheses. Boundedness on the feasible cube is *not*
postulated separately — it follows from continuity on the compact
cube `[0,1]³` and is derived locally where needed (e.g. inside the
Banach BCF construction). -/
structure Params where
  /-- **Adjustment rate of the AFFINE INSTANCE.** In the affine law
  `affineF δ x s = (1 − δ)·x + δ·s`, this is the weight on the current
  sanction, with `(1 − δ)` the inherited-state weight.

  **⚠ Nothing in this structure connects `δ` to `F`.** None of
  `F_continuous`, `F_mono_x`, `F_mono_s`, `F_diag` mentions it. The
  displayed formula holds only where a theorem *separately* supplies
  `hF : p.F = affineF p.δ`. Under a general transition the two are
  independent, and `δ` is inert: every economy must supply an adjustment
  rate, including the non-affine witnesses (`qbParams`, `lbParams`,
  `wobbleEconF` …) whose transition ignores it.

  Measured 2026-08-11: the four general-`F` headline theorems —
  `three_goals_local_MS_generalF`,
  `standardCompliance_persistence_generalF_from_sender_package`,
  `equilibriumTop_senderPersistenceF_long_run_nonDecreasing`,
  `SymbolicEconomyF.persistence_generalF` — read `δ` **zero** times in
  statement or proof. Where the general route needs what `δ` used to
  price, it uses the transition-adjusted chord
  `β_S·K_S·|F(x,s₂) − F(x,s₁)| < ΔU_S` instead of `β_S·K_S·δ < m_S`.

  `δ` is retained because three things genuinely need it: the closed-form
  shock horizon `⌈log(1−x̄)/log(1−δ)⌉` (headline row 5, deliberately
  affine — the general-`F` sibling, headline row 2 with
  `fullShockEntryHorizon x̄ = ⌈x̄/η_F(x̄)⌉` in `Theory/LockIn/LockIn.lean`,
  gives an explicit minimum-drift ceiling under strict adjustment and
  continuity, not a closed form in `δ`; updated 2026-09-11), the
  comparative statics in the adjustment rate, and the legacy affine
  margin routes. Removing it from `Params` would relocate the assumption
  into 195 declarations across 68 files rather than eliminate it. See
  `docs/READING-TRAPS.md` #15. -/
  δ : ℝ
  /-- `δ ∈ (0, 1)` — strict interior so that, *in the affine instance*,
  both the inherited weight `(1 − δ)` and the current-action weight `δ`
  are strictly positive. Under a general `F` this constrains a number no
  general-`F` theorem reads; it is satisfiable by any economy and adds no
  content there. -/
  δ_mem : δ ∈ Set.Ioo (0 : ℝ) 1
  /-- Target discount factor. -/
  β_T : ℝ
  /-- `β_T ∈ [0, 1)` — admits the myopic limit `β_T = 0` and Banach
  contraction for `β_T < 1`. -/
  β_T_mem : β_T ∈ Set.Ico (0 : ℝ) 1
  /-- Sender discount factor. -/
  β_S : ℝ
  /-- `β_S ∈ [0, 1)` — admits the myopic limit `β_S = 0` and Banach
  contraction for `β_S < 1`. -/
  β_S_mem : β_S ∈ Set.Ico (0 : ℝ) 1

  /-- Target stage payoff `U_T(x, a, s)`. Abstract function field
  (no closed form at this layer). -/
  U_T : ℝ → ℝ → ℝ → ℝ
  /-- Sender stage payoff `U_S(x, a, s)`. Abstract function field. -/
  U_S : ℝ → ℝ → ℝ → ℝ
  /-- Static / myopic Sender stage selector `σ(x, a)`. Primitive
  abstract field, coupled to `U_S` by `σ_isMaxOn_U_S` below — it is
  the Sender's stage argmax of `U_S(x, a, ·)` on `[0, 1]`. **Used
  for the myopic comparator only** (`MyopicFeedbackEquilibrium`).
  The forward-looking equilibrium Sender response is constructed
  downstream as `σ_dyn V_S x a` / `σ_dyn_top V_S x a` from the
  Sender continuation value `V_S` (see
  `Theory.Equilibrium.JointMPE` and
  `Theory.LockIn.SigmaDynComparison`); `σ` is **not** the
  equilibrium Sender response. -/
  σ : ℝ → ℝ → ℝ

  /-- `σ x a ∈ [0, 1]` (feasibility). -/
  σ_mem : ∀ x a, σ x a ∈ Set.Icc (0 : ℝ) 1
  /- Joint continuity of `σ` was a field here until 2026-10-07 (round BJ5.1,
  user-approved, checklist 21). Together with `σ_isMaxOn_U_S` it forced every
  economy to have a jointly continuous stage-argmax selection, which fails, for
  example, for a Sender payoff linear in `s` with a state-dependent sign. It is
  now the class `Params.StaticSelectorContinuous` below, taken only by the
  myopic-comparator and static-Sender results that read it; `p.σ_continuous`
  is a theorem under that instance. -/
  /-- **Rule-1 coupling.** `σ x a` is the Sender's stage argmax of
  `U_S(x, a, ·)` on `[0, 1]`. This makes `σ` a *stage-optimal* object
  rather than an arbitrary response function — the static comparator is
  derived, not assumed. It does not by itself certify the forward-looking
  Sender response or any dynamic equilibrium policy; those are constructed
  downstream (`σ_dyn`, `σ_dyn_top`). -/
  σ_isMaxOn_U_S :
    ∀ x a, IsMaxOn (fun s => U_S x a s) (Set.Icc (0 : ℝ) 1) (σ x a)

  /-- `U_T` jointly continuous in `(x, a, s)`. Needed for Bellman BCF
  construction. -/
  U_T_continuous :
    Continuous (fun (xas : ℝ × ℝ × ℝ) => U_T xas.1 xas.2.1 xas.2.2)
  /-- `U_S` jointly continuous in `(x, a, s)`. -/
  U_S_continuous :
    Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2)

  /-- **Transition law** `x' = F(x, s)`: the next political state as a
  function of the current state `x` and the Sender sanction `s`. This is
  the abstract generalisation of the affine law `(1 − δ)·x + δ·s`; the
  canonical instance is `affineF δ` (below), but every theorem in the
  abstract layer is stated against this opaque field. Compliance `a` does
  **not** enter the transition (the Target affects the future state only
  through the Sender's response). -/
  F : ℝ → ℝ → ℝ
  /- Feasibility (`F` maps `[0,1]²` into `[0,1]`) was a field here until
  2026-09-29 (round BC, doc 110 R1a, user-approved). It is not an assumption:
  it follows from `F_mono_x`, `F_mono_s` and `F_diag`, and is now the theorem
  `Params.F_mem` below, with the field's statement and argument order. -/
  /-- `F` is jointly continuous (needed for the Bellman BCF construction:
  continuity of the integrand `V(F(x, s))`). -/
  F_continuous : Continuous (fun (xs : ℝ × ℝ) => F xs.1 xs.2)
  /-- **Power persists**: `F` is non-decreasing in the current state `x`
  (`∂F/∂x ≥ 0`). Higher inherited hardliner power leads to a higher
  future state. -/
  F_mono_x : ∀ s, Monotone (fun x => F x s)
  /-- **Sanctions raise the baseline power**: `F` is non-decreasing in the
  sanction `s` (`∂F/∂s ≥ 0`). Heavier sanctions today entrench a higher
  future political state. -/
  F_mono_s : ∀ x, Monotone (fun s => F x s)
  /-- **Steady-state diagonal**: a sanction equal to the current state
  reproduces it, `F x x = x` (no net pressure when `s = x`). This anchors
  the basin arguments — `s ≥ x ⟹ F x s ≥ F x x = x` keeps the state from
  falling out of the basin — and is the transition-level form of the
  long-run steady state `s* = x*`. -/
  F_diag : ∀ x, F x x = x

/-! ## Continuity of the static Sender selector

Joint continuity of the static selector `σ` is a condition, not a field (round
BJ5.1, 2026-10-07). The general theory (existence, persistence, the shock and
relief results, basins, order selection) never reads it. The results that do
are the ones that build something from the static selector itself: the
Target's Bellman value against the static Sender (`V_T` in
`Theory/Bellman/BellmanT.lean`, the regime-`10` value), the canonical myopic
equilibrium, and the theorems that compare against it. Those take the
instance `[p.StaticSelectorContinuous]`; nothing else does. -/

/-- **The static Sender response is continuous in the state and the
compliance level.** The Sender's stage best response `σ (x, a)` (the
myopic sanction, `Params.σ`) varies continuously with the political state and
with the Target's compliance, jointly on `ℝ × ℝ`.

General in `F`: the condition is about the stage selector alone and does not
mention the transition. It was the structure field `Params.σ_continuous` until
round BJ5.1 (2026-10-07); dropping it from `Params` lets every theorem that does
not read it hold for economies whose stage argmax has no continuous selection
(a Sender payoff linear in `s` with a state-dependent sign is bang-bang, and its
best response jumps). It holds, for example, when `U_S` is jointly continuous
and strictly concave in `s`: the unique stage maximiser is then continuous
(`Foundations/Berge.lean`, `argmax_continuous`; for `Params` built that way,
`ofStrictConcaveUSF_staticSelectorContinuous`). -/
class Params.StaticSelectorContinuous (p : Params) : Prop where
  /-- Joint continuity of `(x, a) ↦ σ x a` on `ℝ × ℝ`. -/
  σ_continuous : Continuous (fun (xa : ℝ × ℝ) => p.σ xa.1 xa.2)

/-- **The former field, re-exposed under the instance.** `σ` is jointly
continuous on `ℝ × ℝ` whenever the economy carries
`[p.StaticSelectorContinuous]`. General in `F`. Every `p.σ_continuous` in the
tree reads as before; the condition now sits in the binder of the theorem that
uses it rather than in every `Params`. -/
theorem Params.σ_continuous (p : Params) [h : p.StaticSelectorContinuous] :
    Continuous (fun (xa : ℝ × ℝ) => p.σ xa.1 xa.2) :=
  h.σ_continuous

/-! ## Strict adjustment toward the current sanction

The paper's maintained transition regime strengthens the five structural
`Params` fields without adding another field to the structure. Keeping the
restriction as a transparent predicate preserves the stronger general-`F`
theorems already proved for every `Params`, while allowing results that need
directional convergence to take one explicit, auditable hypothesis.
-/

/-- **Strict directional adjustment (F5).** On the feasible square, the
next state moves strictly toward the current sanction whenever sanction and
state differ:

* `s < x` implies `F(x,s) < x`;
* `x < s` implies `x < F(x,s)`.

Together with `F_diag`, this is exactly the sign condition
`sign (F(x,s) - x) = sign (s - x)`. The relations are written directly
over `p.F`, so the assumption cannot be satisfied by an unrelated opaque
proposition. -/
def Params.StrictAdjustment (p : Params) : Prop :=
  (∀ ⦃x s : ℝ⦄, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
    s < x → p.F x s < x) ∧
  (∀ ⦃x s : ℝ⦄, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
    x < s → x < p.F x s)

namespace Params

/-! ## The transition is internal, with no strictness assumed

`Params.StrictAdjustment.between_of_s_lt` and `between_of_x_lt` below record the
*strict* bracket, under the strict-adjustment hypothesis. The weak bracket needs
none of it: monotonicity in each argument plus `F x x = x` already confines the
successor state to the interval between the current state and the sanction.

Reading the two existing proofs makes the point concrete — each derives its
non-strict half from `F_diag` and `F_mono_x` alone, and calls on strict
adjustment only for the strict half. What follows lifts that observation out of
the strict namespace, where it does not belong, and states it for every economy
in the class.

The bracket matters because it is *metric* while its hypotheses are *ordinal*.
It bounds how far one sanction can move the political state *away from where the
state already is*, and therefore how far a Lipschitz continuation value can
depart from its reading at the current state, with nothing assumed about the
curvature of `F` or the differentiability of anything.

**Radial, not pairwise.** Every bound below is anchored at `x`, the point `F`
fixes. None of them bounds `|F x s₂ - F x s₁|` by `|s₂ - s₁|`, and no such bound
is available: `Examples/GeneralFNonLipschitzCounterexample.lean` exhibits a
transition meeting every field of this structure that answers two sanctions
`1/4` apart with states `5/16` apart
(`sqrtMeanTransitionParams_not_pairwise_nonexpansive`), and refutes every finite
action-Lipschitz modulus besides
(`sqrtMeanTransitionParams_no_finite_action_lipschitz`). Where a proof needs a
genuine pairwise modulus it must assume one; internality will not supply it.

The general statements are in `Foundations/DiagonalMonotone.lean`. -/

variable (p : Params)

/-- **The successor state lies between the current state and the sanction.**

No strict adjustment, no continuity, no functional form. A sanction below the
state cannot push the state below the sanction, and a sanction above it cannot
push it above. -/
theorem F_mem_uIcc (x s : ℝ) : p.F x s ∈ Set.uIcc x s :=
  Sanctions.mem_uIcc_of_mono_of_diag p.F_mono_x p.F_mono_s p.F_diag x s

/-- **Feasibility preservation is derived, not assumed.**

`F_mem_derived` — the transition maps the feasible square into itself — follows
from three transition primitives, because `F x s` lies between `x` and `s` and
`[0,1]` is order-convex. It uses `F_mono_x`, `F_mono_s` and `F_diag`, and
nothing else.

Until 2026-09-29 feasibility was also a field of this structure, redundant with
this theorem. Round BC (doc 110 R1a, user-approved) removed the field. The
theorem `F_mem` below restates it with the field's argument order, so every
`p.F_mem x s hx hs` in the tree reads the same as before. -/
theorem F_mem_derived {x s : ℝ} (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    p.F x s ∈ Sanctions.I := by
  have h := p.F_mem_uIcc x s
  rw [Set.mem_uIcc] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨le_trans hx.1 h1, le_trans h2 hs.2⟩
  · exact ⟨le_trans hs.1 h1, le_trans h2 hx.2⟩

/-- **The transition keeps the political state feasible**: `F` maps `[0,1]²`
into `[0,1]`. A theorem (round BC, 2026-09-29), not a field: it is
`F_mem_derived` with the former field's statement and argument order. -/
theorem F_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
    p.F x s ∈ Set.Icc (0 : ℝ) 1 :=
  fun _ _ hx hs => p.F_mem_derived hx hs

/-- **One period moves the state by at most the sanction's distance from it.**

The metric form of `F_mem_uIcc`: `|F(x,s) - x| ≤ |s - x|`. This is the bound that
replaces a derivative of `F` in arguments that need to know how far the
continuation value can move from the current state. It says nothing about two
sanctions compared with each other. -/
theorem F_dist_le (x s : ℝ) : |p.F x s - x| ≤ |s - x| :=
  Sanctions.dist_le_of_mono_of_diag p.F_mono_x p.F_mono_s p.F_diag x s

/-- **A Lipschitz value read through the transition stays near its reading at the
current state.**

The curvature-free bound the two-sided comparison needs when it wants to know how
far the Sender's continuation term can move away from `V (x)` as the sanction
departs from `x`.

Radial: the bound is against `V (x)`, not between two sanctions. `F` *can*
amplify a sanction difference — see the section header — so this is not a
Lipschitz property of `s ↦ V (F x s)`. -/
theorem lipschitz_comp_F_le {V : ℝ → ℝ} {L : ℝ}
    (hV : ∀ y z, |V y - V z| ≤ L * |y - z|) (x s : ℝ) :
    |V (p.F x s) - V x| ≤ L * |s - x| :=
  Sanctions.lipschitz_comp_le_of_mono_of_diag p.F_mono_x p.F_mono_s p.F_diag
    hV x s

/-- **A monotone value read through the transition stays between its two
readings.** The order companion of `F_mem_uIcc`. -/
theorem monotone_comp_F_mem_uIcc {V : ℝ → ℝ} (hV : Monotone V) (x s : ℝ) :
    V (p.F x s) ∈ Set.uIcc (V x) (V s) :=
  Sanctions.monotone_comp_mem_uIcc_of_mono_of_diag p.F_mono_x p.F_mono_s
    p.F_diag hV x s

end Params

namespace Params.StrictAdjustment

variable {p : Params}

/-- Below-diagonal sanctions strictly lower the next state. -/
lemma F_lt_self_of_s_lt (h : p.StrictAdjustment) {x s : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hsx : s < x) : p.F x s < x :=
  h.1 hx hs hsx

/-- Above-diagonal sanctions strictly raise the next state. -/
lemma self_lt_F_of_lt_s (h : p.StrictAdjustment) {x s : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hxs : x < s) : x < p.F x s :=
  h.2 hx hs hxs

/-- **Zero-sanction descent (D0).** Every positive feasible state falls
strictly when the current sanction is zero. -/
lemma F_zero_lt_self (h : p.StrictAdjustment) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hx0 : 0 < x) : p.F x 0 < x :=
  h.1 hx ⟨le_rfl, zero_le_one⟩ hx0

/-- Full sanction strictly raises every feasible state below one. -/
lemma self_lt_F_one (h : p.StrictAdjustment) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) : x < p.F x 1 :=
  h.2 ⟨hx.1, le_of_lt hx.2⟩ ⟨zero_le_one, le_rfl⟩ hx.2

/-- The general-`F` shock condition at full sanction is a direct
consequence of strict adjustment. -/
lemma hF_top (h : p.StrictAdjustment) :
    ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1 :=
  fun _ hx => h.self_lt_F_one hx

/-- On the feasible square, `F(x,s) = x` holds exactly on the diagonal
`s = x`. Thus a constant sanction has no off-diagonal fixed state. -/
lemma F_eq_self_iff (h : p.StrictAdjustment) {x s : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    p.F x s = x ↔ s = x := by
  constructor
  · intro hFx
    rcases lt_trichotomy s x with hsx | hsx | hxs
    · exact False.elim (ne_of_lt (h.1 hx hs hsx) hFx)
    · exact hsx
    · exact False.elim (ne_of_gt (h.2 hx hs hxs) hFx)
  · intro hsx
    subst s
    exact p.F_diag x

/-- If sanction lies below the state, monotonicity and diagonal fixation
rule out overshooting below the sanction: `s ≤ F(x,s) < x`. -/
lemma between_of_s_lt (h : p.StrictAdjustment) {x s : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hsx : s < x) : s ≤ p.F x s ∧ p.F x s < x := by
  refine ⟨?_, h.1 hx hs hsx⟩
  calc
    s = p.F s s := (p.F_diag s).symm
    _ ≤ p.F x s := p.F_mono_x s (le_of_lt hsx)

/-- If sanction lies above the state, monotonicity and diagonal fixation
rule out overshooting above the sanction: `x < F(x,s) ≤ s`. -/
lemma between_of_x_lt (h : p.StrictAdjustment) {x s : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hxs : x < s) : x < p.F x s ∧ p.F x s ≤ s := by
  refine ⟨h.2 hx hs hxs, ?_⟩
  calc
    p.F x s ≤ p.F s s := p.F_mono_x s (le_of_lt hxs)
    _ = s := p.F_diag s

end Params.StrictAdjustment

/-! ## Design note (2026-05-23)

Earlier drafts of this structure included two strict-concavity fields
(`targetStage_with_σ_strictConcave_in_a` and
`senderStage_strictConcave_in_s`) to deliver unique stage argmaxes
structurally. They were dropped on review when the σ-substituted
Target stage was shown *not* to be strictly concave on `[0, 1]` even
for the bilateral LQ specification — at the σ regime boundaries
(saturated → interior → zero), the substituted derivative jumps
upward, violating concavity even though a unique argmax still exists.

Downstream theorems that need stage-level strict concavity now take
it as a **theorem-parameter hypothesis** at the use site (the
`optimizer_at_zero_from_strictConcave_local_decrease_at_zero` pattern
in `Theory/Basin/Tipping.lean`), where the concavity claim is
specialized to the specific continuation `V` and parametric `a`-slice
the theorem actually needs. This keeps `Params` universal: every
LQ-style instantiation (with smooth or piecewise stage payoffs)
satisfies its hypotheses, and per-theorem concavity claims are
discharged at use-site from the concrete instantiation's structure.

Likewise, `U_T_bdd` / `U_S_bdd` (uniform bounds on the feasible cube)
were dropped on review: continuity on the compact cube `[0,1]³` already
implies boundedness via `IsCompact.image_of_continuousOn`, so the
Banach BCF construction derives the bound locally rather than receiving
it as a postulate. -/

/-! ## The canonical affine transition

**`affineF` is one instance of `F`, never its definition.** The project's
design goal is that the transition stay *general* — affine and non-affine
alike (see Rule 22 in `CLAUDE.md`). `affineF δ` is the affine transition
`x' = (1 − δ)·x + δ·s` that most concrete witnesses in
`Sanctions/Examples/` use to populate the abstract `Params.F` field; the
non-affine witnesses `qbParams` / `niParams` (`quadBumpF`), `lbParams`
(`quadBumpLowF`) and `ratchetParams` (`ratchetF`) populate it
differently. The four lemmas below discharge the four structural
hypotheses on `F` (feasibility, continuity, monotonicity in `x` and in
`s`) for this instance, so a witness need only write `F := affineF δ`
and apply them.

**Scope note for auditors — corrected 2026-08-08.** The previous version
of this note claimed the theory layer consumes `affineF` "only through an
explicit hypothesis `hF : p.F = affineF p.δ`". That is **false**, and the
error mattered: it hid an entire axis of affine dependence from every
audit that trusted it. Affineness enters on *three* independent axes, and
only the first is visible in a theorem signature.

* **Axis 1 — explicit hypothesis.** `hF : p.F = affineF p.δ`, carried by
  the Schur/Perov row-Lipschitz route, the loss-offset cardinal margin
  family, the enrichment variants of the three-goals package, the lock-in
  limit and patience comparative statics, and the shocked persistence
  gate. Greppable, and the only axis the old note covered.
* **Axis 2 — hard-wired in the state recursion, no signature footprint.**
  `lockInStep` and `shockStep` (`Theory/LockIn/LockIn.lean`) and
  `dynamicTopLockInStep` (`Theory/LockIn/DynamicTopLockIn.lean`) write
  `(1 − δ)·x + δ·rule` by hand and never touch `p.F`. Any theorem whose
  conclusion is stated over `dynamicTopLockInPath` / `shockPath` is
  therefore affine-restricted **even though it carries no `hF`**. The
  general-`F` siblings `dynamicTopLockInStepF` / `…PathF` /
  `…SanctionsF` and `shockStepF` / `shockPathF` already exist; prefer
  them in new work.
* **Axis 3 — instantiation.** Every parametric and symbolic family in
  the tree currently sets `F := affineF`, including
  `SymbolicEconomy.toParams`. The genuinely non-affine economies are the
  numeric witnesses listed above.

The incentive layer is uniformly general: `senderDynObjective`,
`targetSanctionObjective`, `joint_T_top_integrand`, `σ_dyn_top`,
`dynamicTopRealizedRule` and `TargetCombinedChordOn` all evaluate
`p.F x s` and nothing else. The split is precisely *incentives general,
state-evolution forked*. -/

/-- The affine transition `x' = (1 − δ)·x + δ·s`. -/
def affineF (δ : ℝ) : ℝ → ℝ → ℝ := fun x s => (1 - δ) * x + δ * s

/-- The affine transition keeps the state in `[0,1]` (convex combination
of `x, s ∈ [0,1]` with weights `1 − δ, δ ≥ 0` summing to `1`). -/
lemma affineF_mem {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      affineF δ x s ∈ Set.Icc (0 : ℝ) 1 := by
  rintro x s ⟨hx0, hx1⟩ ⟨hs0, hs1⟩
  obtain ⟨hδ0, hδ1⟩ := hδ
  simp only [affineF, Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · have a1 : 0 ≤ (1 - δ) * x := mul_nonneg (by linarith) hx0
    have a2 : 0 ≤ δ * s := mul_nonneg (le_of_lt hδ0) hs0
    linarith
  · have a1 : (1 - δ) * x ≤ (1 - δ) * 1 := mul_le_mul_of_nonneg_left hx1 (by linarith)
    have a2 : δ * s ≤ δ * 1 := mul_le_mul_of_nonneg_left hs1 (le_of_lt hδ0)
    nlinarith [a1, a2]

/-- The affine transition is jointly continuous. -/
lemma affineF_continuous (δ : ℝ) :
    Continuous (fun (xs : ℝ × ℝ) => affineF δ xs.1 xs.2) := by
  unfold affineF; fun_prop

/-- The affine transition is non-decreasing in the current state `x`. -/
lemma affineF_mono_x {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ s, Monotone (fun x => affineF δ x s) := by
  intro s x y hxy
  simp only [affineF]
  have h : (1 - δ) * x ≤ (1 - δ) * y :=
    mul_le_mul_of_nonneg_left hxy (by linarith [hδ.2])
  linarith

/-- The affine transition is non-decreasing in the sanction `s`. -/
lemma affineF_mono_s {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ x, Monotone (fun s => affineF δ x s) := by
  intro x s t hst
  simp only [affineF]
  have h : δ * s ≤ δ * t := mul_le_mul_of_nonneg_left hst (le_of_lt hδ.1)
  linarith

/-- The affine transition fixes the diagonal: `(1−δ)x + δx = x`. -/
lemma affineF_diag (δ : ℝ) : ∀ x, affineF δ x x = x := by
  intro x; simp only [affineF]; ring

/-- The affine transition is **strictly above the diagonal at full
sanction**: `x < affineF δ x 1` for every `x < 1`. This is the `hF_top`
hypothesis of the general-`F` shock theorem, discharged from
`0 < δ(1 − x)`, so the affine law instantiates the general-`F`
trajectory headline with no extra assumption. -/
lemma affineF_hF_top {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ x ∈ Set.Ico (0 : ℝ) 1, x < affineF δ x 1 := by
  rintro x ⟨_, hx1⟩
  simp only [affineF]
  nlinarith [mul_pos hδ.1 (show (0 : ℝ) < 1 - x by linarith)]

/-- Every affine partial-adjustment transition with `δ ∈ (0,1)`
satisfies strict directional adjustment. This parametric discharger keeps
affine witnesses one-line specializations rather than witness-specific
proofs. -/
lemma strictAdjustment_of_F_eq_affineF (p : Params) {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hF : p.F = affineF δ) :
    p.StrictAdjustment := by
  rw [Params.StrictAdjustment, hF]
  constructor
  · intro x s _ _ hsx
    simp only [affineF]
    nlinarith [mul_pos hδ.1 (sub_pos.mpr hsx)]
  · intro x s _ _ hxs
    simp only [affineF]
    nlinarith [mul_pos hδ.1 (sub_pos.mpr hxs)]

end AbstractGame
end Sanctions
