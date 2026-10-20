/-
Sanctions/Examples/AffineInstance/LockInShocked.lean

**The affine transition as a worked instance: lock-in comparative statics and
the shocked single-crossing route.**

Thirteen declarations moved out of `Sanctions/Theory/` on 2026-08-22, the last
of the affine tower.

What is here, in English.

* **Discount comparative statics.** That the Sender's dynamic top sanction and
  the dynamic lock-in band are monotone in the Sender's discount factor --- more
  patience, weakly more lock-in.
* **The `V_S`-free sanction floor** and the no-top-gain equilibrium condition
  built on it, which say when the Sender's value function cannot make a top
  sanction attractive.
* **The shocked single-crossing route.** During an exogenous high-sanction
  phase the Sender's objective is strictly monotone (and single-crossing) in the
  sanction under a strong-rally stage condition, the Target's is monotone under
  the loss-offset condition, and the realized top rule inherits monotonicity ---
  including the moving-average shocked variants. Rule 1's shock exception
  applies to these periods: the sanction path is exogenous, so the
  optimal-strategy requirement does not bind during the shock itself. Since
  Round BG (BG2.6) the four Sender gates are instances, at `d := delta`, of the
  general-`F` strong-rally theorems in `Theory/Shocked/ShockedSingleCrossing.lean`.
* **The sigma smart constructors** `ofStrictConcaveUS` and `ofSupermodularUS`.
* **The affine box-shock hysteresis pair** `basin_forward_invariant_under_box_shock`
  and `basin_escape_of_box_shock_wide` (at the end of the file), moved here from
  `Theory/Shocked/ShockedHysteresis.lean` in round BH-6 (BH6.7, 2026-10-07): the
  high basin `[xT, 1]` is absorbing for the affine box-shocked loop
  `clipS((1 − delta)x + delta + eta)` iff `h <= delta(1 - xT)`. Both are now
  instances of the bare-closed-loop theorems of that file, whose `Params` forms
  give the same threshold `h <= d_F(xT) = F(xT, 1) - xT` for every transition.

**Why these are in `Examples/` and not `Theory/`.** Every declaration below
except the box-shock pair carries `hF : p.F = affineF p.delta` in its statement
--- the hypothesis that one unit of sanction moves next period's political state
by exactly `delta`, the same amount at every state and every sanction level.
Under Rule 22 that makes each one affine-restricted by construction, so each is
an *instance*, not part of the general theory. The box-shock pair is
affine-restricted on axis 2 instead: it binds a bare `delta` and writes the
affine loop out, with no `Params` at all.

Nothing is deleted and nothing is weakened: each still type-checks exactly as it
did in `Theory/`, and each still earns its keep as an exhibit of what the affine
law discharges for free. What changed is only where they live, and therefore
what the general theory is allowed to lean on.

Checked before the move (Rule 23, three gates): the citation graph reported no
consumer outside the affine set itself; a textual sweep of `paper/`, `*.md` and
`*.lean` recorded every prose citation, and the paper was synced in the same
round for those it found (Rule 2); and `lake build` is the gate that settles it.
-/

import Sanctions.Examples.AffineInstance.ComplianceTower

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame

namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Round-32 σ-quad-shrunk Params constructor.**

Replaces the three primitive σ-fields (`σ`, `σ_mem`, `σ_isMaxOn_U_S`)
by a single strict-concavity-of-`U_S`-in-`s` on
`[0, 1]` primitive. Round BJ5.1 (2026-10-07): the former input
`σ_continuous_of_strictConcave` (the joint continuity of the Berge
selector) is gone. `σ_continuous` is no longer a `Params` field but the
class `Params.StaticSelectorContinuous`, and on this route it is derived
from strict concavity (`bergeSigma_continuous`, Berge's maximum theorem),
installed as the instance `ofStrictConcaveUS_staticSelectorContinuous`
below; the constructor assumes nothing in its place.

The σ field is auto-built as the Berge-selected unique argmax of
`U_S(x, a, ·)` on `[0, 1]`. Both `σ_mem` and `σ_isMaxOn_U_S` follow
automatically from `Berge.argmax_mem` and `Berge.argmax_isMaxOn`.

Use this constructor for instantiations whose `U_S` is genuinely
strictly concave in `s` (e.g. quadratic loss
`U_S(x, a, s) = -(s - s*(x, a))²`). For linear-in-`s` instantiations
(`jointPositiveParams`, `polyComplianceParams`), strict concavity
fails and the primitive-σ constructor remains the correct route.

⚠ Transition pin: this constructor hard-wires `F := affineF δ`.
It is now the `affineF δ` member of the general family
`Params.ofStrictConcaveUSF` (`Theory/Equilibrium/SigmaParamsRefactor.lean`),
which takes the transition and its five structural obligations as
arguments — so an economy needing a non-affine transition uses that parent
directly rather than building `Params` by hand. -/
noncomputable def ofStrictConcaveUS
    (δ : ℝ) (δ_mem : δ ∈ Set.Ioo (0 : ℝ) 1)
    (β_T : ℝ) (β_T_mem : β_T ∈ Set.Ico (0 : ℝ) 1)
    (β_S : ℝ) (β_S_mem : β_S ∈ Set.Ico (0 : ℝ) 1)
    (U_T : ℝ → ℝ → ℝ → ℝ)
    (U_S : ℝ → ℝ → ℝ → ℝ)
    (U_T_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_T xas.1 xas.2.1 xas.2.2))
    (U_S_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (U_S_strictConcave_in_s :
      ∀ x a : ℝ, StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => U_S x a s)) :
    Sanctions.AbstractGame.Params :=
  ofStrictConcaveUSF δ δ_mem β_T β_T_mem β_S β_S_mem U_T U_S
    U_T_continuous U_S_continuous U_S_strictConcave_in_s
    (affineF δ) (affineF_continuous _)
    (affineF_mono_x δ_mem) (affineF_mono_s δ_mem) (affineF_diag δ)

/-- **Every strictly concave affine Berge economy has a continuous static
selector.** The instance `Params.StaticSelectorContinuous` for the
`ofStrictConcaveUS` family, derived from strict concavity by
`bergeSigma_continuous` (round BJ5.1, 2026-10-07; until then a constructor
input). Affine-restricted, as the constructor is (`F := affineF δ`); the
general-`F` parent is `ofStrictConcaveUSF_staticSelectorContinuous`. Needed as
its own instance because instance search does not unfold the wrapper. -/
instance ofStrictConcaveUS_staticSelectorContinuous
    (δ : ℝ) (δ_mem : δ ∈ Set.Ioo (0 : ℝ) 1)
    (β_T : ℝ) (β_T_mem : β_T ∈ Set.Ico (0 : ℝ) 1)
    (β_S : ℝ) (β_S_mem : β_S ∈ Set.Ico (0 : ℝ) 1)
    (U_T : ℝ → ℝ → ℝ → ℝ)
    (U_S : ℝ → ℝ → ℝ → ℝ)
    (U_T_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_T xas.1 xas.2.1 xas.2.2))
    (U_S_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (U_S_strictConcave_in_s :
      ∀ x a : ℝ, StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => U_S x a s)) :
    (ofStrictConcaveUS δ δ_mem β_T β_T_mem β_S β_S_mem U_T U_S
      U_T_continuous U_S_continuous U_S_strictConcave_in_s).StaticSelectorContinuous :=
  ⟨bergeSigma_continuous U_S_continuous U_S_strictConcave_in_s⟩

/-! ## §4 Round-33 Path-A alternative constructor (BRW 2014 supermodular-only route)

Round 33 sibling of `Params.ofStrictConcaveUS`: builds a `Params`
by **dropping the strict-concavity requirement** in favour of the
BRW 2014 Path-A extremal-selection argument. For the
one-dimensional Sender choice `s ∈ [0, 1]`, BRW's
supermodular + ID + continuity + compactness assumption set
collapses to **continuity alone** for σ-quad existence (the
single-choice specialization makes supermodularity and increasing
differences vacuous on the choice side), and the σ-selector is
the **greatest extremal** of the argmax set rather than its
unique element.

### Why this matters at `polyComplianceParams`

The minimal non-vacuity witness `polyComplianceParams` uses
linear `U_S(x, a, s) = s`. Linear functions are *not* strictly
concave, so Round 32's `Params.ofStrictConcaveUS` does not apply.
But linear `U_S = s` is supermodular (trivially, as a
one-dimensional function), has increasing differences in `(s, a)`
(constant in `a`), is continuous, and is over the compact
interval `[0, 1]` — so the BRW Path-A constructor
`Params.ofSupermodularUS` applies cleanly and auto-discharges
the three σ-fields at `s = 1` (the greatest argmax of the
identity on `[0, 1]`).

### Selector identity

The Round-33 σ-selector is
`bergeGreatestSigma U_S_continuous x a := greatestArgmax (Icc 0 1)
isCompact_Icc ⟨0, _⟩ (fun (xa : ℝ × ℝ) s => U_S xa.1 xa.2 s)
(per-`(x, a)` continuity slice) (x, a)`. For linear `U_S = s`,
this evaluates to the constant `1` (the right endpoint of `[0, 1]`).
This matches `polyComplianceParams.σ ≡ 1` *exactly*, so the
witness's hand-written σ-field and the Path-A-built σ-field are
**def-equal modulo the construction** — Path A provides a derived,
not assumed, σ.
-/

/-- **Round-33 σ-quad-shrunk Params constructor (BRW 2014 Path A —
supermodular-only existence).**

Replaces the three primitive σ-fields (`σ`, `σ_mem`, `σ_isMaxOn_U_S`)
using the BRW 2014 **supermodular-only** extremal
existence argument: no strict concavity, no uniqueness — only
continuity of `U_S(x, a, ·)` on `[0, 1]` (the per-`(x, a)` slice
of the existing `U_S_continuous` field). The σ field is auto-built
as the **greatest** maximizer of `U_S(x, a, ·)` on `[0, 1]`. Both
`σ_mem` and `σ_isMaxOn_U_S` follow automatically from
`greatestArgmax_mem` and `greatestArgmax_isMaxOn`.

### Comparison to `Params.ofStrictConcaveUS` (Round 32)

* **Round 32 (Berge).** Existence input: strict concavity in `s`.
  Selector identity: unique maximizer. Linear-`U_S` case: **fails**
  (strict concavity is not satisfied by `U_S = s`).
* **Round 33 (BRW Path A).** Existence input: continuity in `s`
  (already in `U_S_continuous`). Selector identity: **greatest**
  (extremal) maximizer. Linear-`U_S` case: **handled** — applies
  to `U_S = s` (greatest argmax = `1`).

The Round-33 route is the right choice for any concrete witness
whose Sender stage payoff is **linear** (or merely concave but not
strictly concave) — e.g. `polyComplianceParams` with
`U_S(x, a, s) = s`, where the unique-argmax route fails but the
greatest-argmax route delivers the canonical `σ ≡ 1` selector.

### Continuity scope

Joint continuity of `(x, a) ↦ σ x a` is the Berge
**continuous-selector** half. Until round BJ5.1 (2026-10-07) it was
the `Params` field `σ_continuous`, and this constructor took it as the
input `σ_continuous_of_supermodular`. It is now the class
`Params.StaticSelectorContinuous`, outside `Params`, so the constructor
no longer asks for it: the greatest selector need not be continuous (a
Sender payoff linear in `s` with a state-dependent sign is bang-bang,
and its greatest best response jumps). Where continuity holds, the
instance comes from `ofSupermodularUS_staticSelectorContinuous` below,
which takes the same input the constructor used to take.

### Rule compliance

* **Rule 1.** σ is the Sender's stage **greatest** best response —
  fully equilibrium-derived from the BRW Path-A construction, no
  hand-chosen selector.
* **Rule 3.** Pure discharger / cat-2 weakening: the original 4
  σ-fields are *replaced* by **no new primitive** (the existence
  hypothesis is the existing `U_S_continuous` field, sliced via
  `uS_slice_continuousOn`). The constructor is **opt-in**: existing
  primitive-σ instances retain the primitive-σ shape, and Round-32
  `Params.ofStrictConcaveUS` remains available for strictly-concave
  `U_S`. Rule 3's "stop and confirm" is satisfied because: (i) we
  *narrow* the assumption surface (zero new primitives beyond the
  continuity already required by the abstract game environment),
  (ii) the construction is the canonical BRW 2014 Path A argument
  (Theorem 3.1 + Lemma 5.1) specialized to a single-player
  one-dimensional choice.
* **Rule 5.** Fully parametric over the input data; no
  witness-specific instantiation.
* **Rule 8.** Plain-language docstrings throughout.
* **Rule 9.** RETIRED 2026-06-04; no witness obligation for this
  alternative constructor.
* **Rule 10.** `#print axioms` clean on the new constructor (only
  `propext`, `Classical.choice`, `Quot.sound`).
* **Rule 19.** BRW Path-A external theory lives in
  `Foundations/BalbusReffettWozny.lean`; this `Theory/Equilibrium`
  file is the `Params`-level application layer alongside
  Round-32's strict-concavity wrappers.

⚠ Transition pin: like `ofStrictConcaveUS`, this constructor
hard-wires `F := affineF δ`. An economy needing a non-affine
transition must build `Params` directly (as `qbCertParams` /
`lbParams` do).
-/
noncomputable def ofSupermodularUS
    (δ : ℝ) (δ_mem : δ ∈ Set.Ioo (0 : ℝ) 1)
    (β_T : ℝ) (β_T_mem : β_T ∈ Set.Ico (0 : ℝ) 1)
    (β_S : ℝ) (β_S_mem : β_S ∈ Set.Ico (0 : ℝ) 1)
    (U_T : ℝ → ℝ → ℝ → ℝ)
    (U_S : ℝ → ℝ → ℝ → ℝ)
    (U_T_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_T xas.1 xas.2.1 xas.2.2))
    (U_S_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2)) :
    Sanctions.AbstractGame.Params :=
  ofSupermodularUSF δ δ_mem β_T β_T_mem β_S β_S_mem U_T U_S
    U_T_continuous U_S_continuous
    (affineF δ) (affineF_continuous _)
    (affineF_mono_x δ_mem) (affineF_mono_s δ_mem) (affineF_diag δ)

/-- **A supermodular affine Berge economy has a continuous static selector
when its greatest selector is continuous.** The instance
`Params.StaticSelectorContinuous` for a member of the `ofSupermodularUS`
family, from the joint continuity of the greatest stage best response —
exactly the input `σ_continuous_of_supermodular` the constructor took until
round BJ5.1 (2026-10-07), now asked only by the results that read it (use
with `haveI`). Affine-restricted, as the constructor is (`F := affineF δ`);
the general-`F` parent is `ofSupermodularUSF_staticSelectorContinuous`. -/
theorem ofSupermodularUS_staticSelectorContinuous
    (δ : ℝ) (δ_mem : δ ∈ Set.Ioo (0 : ℝ) 1)
    (β_T : ℝ) (β_T_mem : β_T ∈ Set.Ico (0 : ℝ) 1)
    (β_S : ℝ) (β_S_mem : β_S ∈ Set.Ico (0 : ℝ) 1)
    (U_T : ℝ → ℝ → ℝ → ℝ)
    (U_S : ℝ → ℝ → ℝ → ℝ)
    (U_T_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_T xas.1 xas.2.1 xas.2.2))
    (U_S_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (σ_continuous_of_supermodular :
      Continuous (fun (xa : ℝ × ℝ) =>
        bergeGreatestSigma U_S_continuous xa.1 xa.2)) :
    (ofSupermodularUS δ δ_mem β_T β_T_mem β_S β_S_mem U_T U_S
      U_T_continuous U_S_continuous).StaticSelectorContinuous :=
  ⟨σ_continuous_of_supermodular⟩

end Params

/-- **A more patient Sender's greatest sanction response is weakly
higher (Phase 2; direct effect at fixed continuation and action).**
Across two economies with equal stage payoff and transition speed
but `β_S₁ ≤ β_S₂`: under the user-approved slope-zero hypothesis —
the Sender value weakly increasing on the reachable range
`[lo, 1] ⊇ [(1−δ)x, (1−δ)x + δ]` — the objective difference
`(β₂−β₁)·V_S(F(x,·))` is nondecreasing in the sanction, so the
greatest maximizers are ordered. Affine corollary of the
general-transition sibling `σ_dyn_top_le_of_beta_le_generalF`
(under `hF₁`/`hF₂`/`hδeq` the transitions coincide and the affine
floor `lo ≤ (1−δ)·x` is exactly `lo ≤ p₁.F x 0`). -/
theorem σ_dyn_top_le_of_beta_le
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (hF₁ : p₁.F = Sanctions.AbstractGame.affineF p₁.δ)
    (hF₂ : p₂.F = Sanctions.AbstractGame.affineF p₂.δ)
    (hU : p₁.U_S = p₂.U_S) (hδeq : p₁.δ = p₂.δ)
    (hβ : p₁.β_S ≤ p₂.β_S)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {lo : ℝ}
    (hmonoV : Params.LowerSlopeOnValueOn V_S (Set.Icc lo 1) 0)
    {x a : ℝ} (hx01 : x ∈ Sanctions.I)
    (hlo_le : lo ≤ (1 - p₁.δ) * x) :
    p₁.σ_dyn_top V_S x a ≤ p₂.σ_dyn_top V_S x a := by
  have hFeq : p₁.F = p₂.F := by rw [hF₁, hF₂, hδeq]
  have hlo_le' : lo ≤ p₁.F x 0 := by
    rw [hF₁]
    simpa [Sanctions.AbstractGame.affineF] using hlo_le
  exact σ_dyn_top_le_of_beta_le_generalF p₁ p₂ hFeq hU hβ V_S hmonoV
    hx01 hlo_le'

/-- **Patience deepens lock-in (Phase 2, band corollary).** Across
two economies identical except for Sender patience, under the
approved slope-zero value-monotonicity hypothesis the more patient
economy's lock-in level is weakly higher. Direct effect at fixed
`(V_S, α)`; the equilibrium-feedback channel is recorded open.
Affine corollary of the general-transition sibling
`dynamicTopLockIn_band_le_of_beta_le_generalF`.

Since round BH-2 (2026-10-06, BH2.4) both levels are also exported as
*least* fixed points of their lock-in steps on `[x̄, 1]` (the earlier
statement held trivially at `xs₁ = xs₂ = 1` without them). `hδeq` is
still read here, but only to identify the two affine transitions
(`hFeq`); the general sibling no longer takes it. Affine-restricted
(Rule 22): `hF₁`, `hF₂` fix the transition to the affine law. -/
theorem dynamicTopLockIn_band_le_of_beta_le
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (hF₁ : p₁.F = Sanctions.AbstractGame.affineF p₁.δ)
    (hF₂ : p₂.F = Sanctions.AbstractGame.affineF p₂.δ)
    (hU : p₁.U_S = p₂.U_S) (hδeq : p₁.δ = p₂.δ)
    (hβ : p₁.β_S ≤ p₂.β_S)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar₁ sbar₂ lo : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hlo_le : lo ≤ (1 - p₁.δ) * xbar)
    (hmonoV : Params.LowerSlopeOnValueOn V_S (Set.Icc lo 1) 0)
    (h_level₁ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₁ ≤ p₁.dynamicTopRealizedRule V_S α x)
    (h_level₂ : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      max x sbar₂ ≤ p₂.dynamicTopRealizedRule V_S α x)
    (hmono₁ : MonotoneOn (p₁.dynamicTopRealizedRule V_S α)
      (Set.Icc xbar 1))
    (hmono₂ : MonotoneOn (p₂.dynamicTopRealizedRule V_S α)
      (Set.Icc xbar 1)) :
    ∃ xs₁ ∈ Set.Icc xbar 1, ∃ xs₂ ∈ Set.Icc xbar 1,
      p₁.dynamicTopLockInStep V_S α xs₁ = xs₁ ∧
      p₁.dynamicTopRealizedRule V_S α xs₁ = xs₁ ∧
      p₂.dynamicTopLockInStep V_S α xs₂ = xs₂ ∧
      p₂.dynamicTopRealizedRule V_S α xs₂ = xs₂ ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ), p₁.dynamicTopLockInStep V_S α y = y → xs₁ ≤ y) ∧
      (∀ y ∈ Set.Icc xbar (1 : ℝ), p₂.dynamicTopLockInStep V_S α y = y → xs₂ ≤ y) ∧
      xs₁ ≤ xs₂ := by
  have hFeq : p₁.F = p₂.F := by rw [hF₁, hF₂, hδeq]
  have hlo_le' : lo ≤ p₁.F xbar 0 := by
    rw [hF₁]
    simpa [Sanctions.AbstractGame.affineF] using hlo_le
  exact dynamicTopLockIn_band_le_of_beta_le_generalF p₁ p₂ hFeq hU
    hβ V_S α hxbar_mem hlo_le' hmonoV h_level₁ h_level₂ hmono₁ hmono₂

namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **The Sender's forward-looking objective is non-decreasing up to `c`.**

The Sender's own stage payoff may *fall* in the sanction, at rate at most `cS`
(`h_stage_loss`); if the continuation value rises in the political state at
rate at least `g` (`hV_gain`), and the transition passes a fraction `δ` of the
sanction into next period's state, then the discounted continuation gain
`β_S·g·δ` covers the stage loss `cS` (`h_margin`) and the objective
`s ↦ U_S(x, α x, s) + β_S · V(F(x,s))` is monotone on `[0,c]`.

This is the Sender mirror of the Target-side
`targetSanctionObjective_mono_of_sanction_loss_offset_by_state_value_on`; the
scalars `cS` and `g` are theorem-bound bounds on the *existing* `U_S` and on
the supplied `V`, so no assumption surface is widened. -/
theorem senderDynObjective_monotoneOn_of_sanction_loss_offset
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {α : ℝ → ℝ} {x c cS g : ℝ}
    (hx : x ∈ Sanctions.I) (hc : c ∈ Sanctions.I)
    (h_stage_loss : LowerLossSlopeOn (fun s => p.U_S x (α x) s) (Set.Icc (0:ℝ) c) cS)
    (hV_gain : AbstractGame.Params.LowerSlopeOnValueOn V (Set.Icc (0:ℝ) 1) g)
    (h_margin : cS ≤ p.β_S * g * p.δ) :
    MonotoneOn (fun s => p.senderDynObjective V x (α x) s) (Set.Icc (0:ℝ) c) := by
  intro s₁ hs₁ s₂ hs₂ hle
  have hβ : (0:ℝ) ≤ p.β_S := p.β_S_mem.1
  have hδ : (0:ℝ) < p.δ := p.δ_mem.1
  have hsdiff : (0:ℝ) ≤ s₂ - s₁ := by linarith
  have hs₁I : s₁ ∈ Sanctions.I := ⟨hs₁.1, le_trans hs₁.2 hc.2⟩
  have hs₂I : s₂ ∈ Sanctions.I := ⟨hs₂.1, le_trans hs₂.2 hc.2⟩
  have hstage := h_stage_loss s₁ hs₁ s₂ hs₂ hle
  have hF₁ : p.F x s₁ ∈ Set.Icc (0:ℝ) 1 := p.F_mem _ _ hx hs₁I
  have hF₂ : p.F x s₂ ∈ Set.Icc (0:ℝ) 1 := p.F_mem _ _ hx hs₂I
  have hFle : p.F x s₁ ≤ p.F x s₂ := p.F_mono_s x hle
  have hord : Sanctions.clipS' (p.F x s₁) ≤ Sanctions.clipS' (p.F x s₂) :=
    Sanctions.clipS'_mono hFle
  have hVslope := hV_gain (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
    (by rw [Sanctions.clipS'_val_eq_of_mem hF₁]; exact hF₁)
    (by rw [Sanctions.clipS'_val_eq_of_mem hF₂]; exact hF₂) hord
  have hdF : dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
      = p.δ * (s₂ - s₁) := by
    rw [clipS'_dist_eq_of_mem hF₁ hF₂, hF]
    unfold Sanctions.AbstractGame.affineF
    rw [show (1 - p.δ) * x + p.δ * s₁ - ((1 - p.δ) * x + p.δ * s₂)
          = -(p.δ * (s₂ - s₁)) from by ring, abs_neg]
    exact abs_of_nonneg (mul_nonneg hδ.le hsdiff)
  rw [hdF] at hVslope
  have hVscaled : p.β_S * (g * (p.δ * (s₂ - s₁)))
      ≤ p.β_S * (V (Sanctions.clipS' (p.F x s₂)) - V (Sanctions.clipS' (p.F x s₁))) :=
    mul_le_mul_of_nonneg_left hVslope hβ
  have hmargin_scaled : cS * (s₂ - s₁) ≤ (p.β_S * g * p.δ) * (s₂ - s₁) :=
    mul_le_mul_of_nonneg_right h_margin hsdiff
  show p.U_S x (α x) s₁ + p.β_S * V (Sanctions.clipS' (p.F x s₁))
    ≤ p.U_S x (α x) s₂ + p.β_S * V (Sanctions.clipS' (p.F x s₂))
  nlinarith [hstage, hVscaled, hmargin_scaled]

/-- **`V_S`-free equilibrium sanction floor.**

Not one hypothesis mentions a continuation value.  The inputs are the Sender
stage payoff `U_S`, the discount factor `β_S`, the transition persistence `δ`,
the affine transition law and the Target policy `α`; the conclusion is a floor
on the *greatest forward-looking Sender argmax* against the **constructed**
Sender Bellman fixed point `V_S α hα`.

* `h_state_slope` — the Sender's stage payoff has state chord at least `m`,
  uniformly in the sanction (the sanctioning coalition's political stake in the
  Target's entrenchment);
* `h_sanction_loss` — the Sender's stage payoff falls in its own sanction at
  rate at most `cS` on `[0,c]`;
* `h_margin` — `cS·(1 − β_S·(1 − δ)) ≤ β_S·m·δ`: the stage loss rate is covered
  by the discounted continuation gain rate `β_S · (m / (1 − β_S(1−δ))) · δ`,
  where `m / (1 − β_S(1−δ))` is the Benveniste–Scheinkman closed form for the
  value function's state slope.

**Read the name literally.**  `V_S`-free means no *continuation value* occurs
on the hypothesis side.  It does **not** mean primitive-free: both chord
hypotheses are stated over the composed map `y ↦ U_S(y, α y, s)`, and at a
joint MPE the Target policy `α` is endogenous (derived from `V_T`).  See the
file header for the three things this leaves open, and
`no_top_gain_equilibrium_of_V_S_free_floor_condition` below for the structural
price the condition carries.

Rule 15: `V_S α hα` is the Banach fixed point built in
`Theory/Bellman/BellmanS.lean`; its cone membership is derived, not assumed. -/
theorem V_S_free_sanction_floor
    {α : ℝ → ℝ} (hα : Continuous α)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {m cS x c : ℝ}
    (hx : x ∈ Sanctions.I) (hc : c ∈ Sanctions.I)
    (h_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
    (h_sanction_loss :
      LowerLossSlopeOn (fun s => p.U_S x (α x) s) (Set.Icc (0:ℝ) c) cS)
    (h_margin : cS * (1 - p.β_S * (1 - p.δ)) ≤ p.β_S * m * p.δ) :
    c ≤ p.dynamicTopRealizedRule (p.V_S α hα) α x := by
  have hpos := p.oneMinus_betaS_oneMinusDelta_pos
  have hcone := p.V_S_mem_lowerSlopeCone hα hF h_state_slope
  refine p.realizedRule_ge_of_monotoneOn (p.V_S α hα) α hc ?_
  refine p.senderDynObjective_monotoneOn_of_sanction_loss_offset hF hx hc
    h_sanction_loss hcone ?_
  rw [Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def,
    show p.β_S * (m / (1 - p.β_S * (1 - p.δ))) * p.δ
        = (p.β_S * m * p.δ) / (1 - p.β_S * (1 - p.δ)) from by ring,
    le_div_iff₀ hpos]
  exact h_margin

/-! ### The price: the condition precludes a live Target channel at the top

The two theorems below are the *limitation*, stated as theorems so that it
cannot be lost from a docstring — the discipline of
`Examples/DeterministicStrictEscalation.ni_continuation_channel_inactive` and
`Examples/ContinuationDrivenEscalation.ce_common_interest`. -/

/-- **THE STRUCTURAL PRICE OF THE `V_S`-FREE FLOOR CONDITION, STATED AS A
THEOREM.**

At a non-negative stage state chord `m ≥ 0`, the three hypotheses of
`V_S_free_sanction_floor` — the stage state chord `m`, the stage sanction-loss
rate `cS` at the top state (required here for the equilibrium action and for
one deviation `E.α 1 + t`), and the margin
`cS·(1 − β_S(1−δ)) ≤ β_S·m·δ` — discharge **every** hypothesis of the in-tree
`AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain`
(`Theory/Equilibrium/AbsorbingTopObstruction.lean`) at
`(m := g, κ := δ, c := cS)`, where `g = m / (1 − β_S(1−δ))` is the derived
value slope.  Hence **no** feedback Stackelberg equilibrium at which the Target
strictly gains at the top state (`hgain`) can satisfy the floor condition.

This is not the remark "the condition says nothing about Target optimality".
It is an **active structural preclusion**: the condition is *incompatible* with
a live Target strategic channel at the absorbing top state.  It is the same
phenomenon as the `ratchet_dichotomy` in `AbsorbingTopObstruction.lean`,
recurring one level up — a sanction floor strong enough to pin the corner makes
the successor state stop responding to the Target's action, which frees the
Target's action and destroys the very optimality the equilibrium asserts.

**Scope, stated precisely.**  Two limits belong with this theorem and must not be
dropped when it is cited.

First, `h_loss1` is an **off-policy** input: it bounds the sanction loss at the
top state for the deviation action `E.α 1 + t`, not merely along the equilibrium
policy.  The `V_S`-free floor condition does not supply it.  So this is not "the
floor condition precludes such equilibria" — it is "the floor condition together
with an off-policy loss bound precludes them."

Second, the theorem is **vacuous at both witness economies of
`Examples/SenderConeWitness.lean`**: `hgain` — the Target strictly gaining at the
top — is unsatisfiable at `wParams` and at `qParams`.  It therefore does **not**
explain why those witnesses have `U_S` independent of the Target's action
(`w_not_a_game`, `q_not_a_game`); an earlier docstring claimed it did, which was
wrong.  Whether that degeneracy is forced is an open question, not a corollary
of this theorem. -/
theorem no_top_gain_equilibrium_of_V_S_free_floor_condition
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {m cS t : ℝ} (hm : 0 ≤ m)
    (h_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (E.α y₂) s - p.U_S y₁ (E.α y₁) s)
    (h_loss0 : LowerLossSlopeOn (fun s => p.U_S 1 (E.α 1) s) (Set.Icc (0:ℝ) 1) cS)
    (h_loss1 : LowerLossSlopeOn (fun s => p.U_S 1 (E.α 1 + t) s) (Set.Icc (0:ℝ) 1) cS)
    (h_margin : cS * (1 - p.β_S * (1 - p.δ)) ≤ p.β_S * m * p.δ)
    (hdev : E.α 1 + t ∈ Sanctions.I)
    (hgain : p.U_T 1 (E.α 1) 1 < p.U_T 1 (E.α 1 + t) 1) : False := by
  have hpos := p.oneMinus_betaS_oneMinusDelta_pos
  set g : ℝ := Sanctions.StokeyLucas.bellmanLowerSlopeConstant p.β_S (1 - p.δ) m
    with hgdef
  have hg_nn : 0 ≤ g := by
    rw [hgdef, Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def]
    exact div_nonneg hm hpos.le
  have hcone0 := p.V_S_mem_lowerSlopeCone E.hα hF h_state_slope
  have hcone : AbstractGame.Params.LowerSlopeOnValueOn E.V_S (Set.Icc (0:ℝ) 1) g := by
    rw [p.equilibrium_V_S_eq_constructed E]; exact hcone0
  have h1S : (1:ℝ) ∈ (Sanctions.S : Set ℝ) := ⟨zero_le_one, le_refl 1⟩
  refine Sanctions.AbstractGame.AbsorbingTop.no_equilibrium_of_slope_and_top_gain
    p E g p.δ cS t hg_nn ⟨1, h1S⟩ rfl ?_ ?_ ?_ ?_ ?_ hdev hgain
  · -- `hslope`: the equilibrium Sender value rises to the top at rate ≥ g.
    intro y
    have hyle : y ≤ (⟨1, h1S⟩ : ↥(Sanctions.S : Set ℝ)) := y.property.2
    have h := hcone y ⟨1, h1S⟩ y.property h1S hyle
    rwa [dist_eq_sub_of_le hyle] at h
  · -- `htrans`: the affine law drops the successor from the top at rate δ.
    intro s _
    rw [hF]
    unfold Sanctions.AbstractGame.affineF
    ring_nf
    linarith
  · -- `hshade0`: the equilibrium action's static shading gain is ≤ cS·(1−s).
    intro s hs
    have h := h_loss0 s ⟨hs.1, hs.2⟩ 1 ⟨zero_le_one, le_refl 1⟩ hs.2
    simp only at h
    linarith
  · -- `hshade1`: same bound at the deviation action `E.α 1 + t`.
    intro s hs
    have h := h_loss1 s ⟨hs.1, hs.2⟩ 1 ⟨zero_le_one, le_refl 1⟩ hs.2
    simp only at h
    linarith
  · -- `hc`: cS ≤ β_S · g · δ, i.e. exactly the floor condition's margin.
    rw [hgdef, Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def,
      show p.β_S * (m / (1 - p.β_S * (1 - p.δ))) * p.δ
          = (p.β_S * m * p.δ) / (1 - p.β_S * (1 - p.δ)) from by ring,
      le_div_iff₀ hpos]
    exact h_margin

/-! ## Axiom hygiene (Rule 10) -/

end Params

/-! ## The shocked Sender gates as instances of the general-`F` theorems

Round BG (2026-10-06, BG2.6). The four affine Sender gates below are instances, at
the rate `d := δ`, of the general-`F` strong-rally theorems in
`Theory/Shocked/ShockedSingleCrossing.lean`. The only affine input is the exact
sanction chord `Params.abs_sanction_chord_of_affineF`. -/

namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **The affine sanction chord is exact (affine-restricted).** Under the affine law
`F = affineF δ`, raising the sanction from `s₁` to `s₂ ≥ s₁` moves next period's
political state by exactly `δ·(s₂ − s₁)`, at every state:
`|F(x,s₂) − F(x,s₁)| = δ·(s₂ − s₁)`. Its `≤` half is the upper chord at rate
`d := δ` that the general-`F` strong-rally theorems of
`Theory/Shocked/ShockedSingleCrossing.lean` take as `hF_chord`, which is what makes
the affine shocked Sender gates below instances of them. It uses only `hF` and
`0 < δ` (from `δ_mem`). -/
theorem abs_sanction_chord_of_affineF
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) {x s₁ s₂ : ℝ} (hle : s₁ ≤ s₂) :
    |p.F x s₂ - p.F x s₁| = p.δ * (s₂ - s₁) := by
  have h : p.F x s₂ - p.F x s₁ = p.δ * (s₂ - s₁) := by
    rw [hF]; simp only [Sanctions.AbstractGame.affineF]; ring
  rw [h]
  exact abs_of_nonneg (mul_nonneg p.δ_mem.1.le (sub_nonneg.mpr hle))

end Params

namespace ShockedParams

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- **Shocked strong-rally strict monotonicity (the gate, abstract form;
affine-restricted).** On the high basin `[max xT xS, 1]` the shocked Sender objective
`s ↦ U_S(x, α x, s) + β_S · (smear V_S)(clipS'(F x s))` is *strictly increasing* in the
sanction `s`, from the SAME strong-rally primitives as the deterministic case — stage
lower slope `mS` on `[0,1]`, strict margin `β_S · KS · δ < mS`, and
`KS`-Lipschitzness of the *smeared* continuation `sp.smear V_S`.

Round BG (2026-10-06, BG2.6): this is the instance `d := δ` of the general-`F`
theorem `senderDynObjective_shock_strictMonoOn_of_strong_rally_generalF`
(`Theory/Shocked/ShockedSingleCrossing.lean`). The affine law enters only through
the exact sanction chord `Params.abs_sanction_chord_of_affineF`. The binder
`_hKS_nonneg` is kept so the statement is unchanged, but it is no longer used:
`0 ≤ KS` already follows from `h_smear_lip`. -/
theorem senderDynObjective_shock_strictMonoOn_of_strong_rally
    (hF : sp.toParams.F = Sanctions.AbstractGame.affineF sp.toParams.δ)
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS mS KS : ℝ}
    (_hKS_nonneg : 0 ≤ KS)
    (hS_margin : sp.toParams.β_S * KS * sp.toParams.δ < mS)
    (h_smear_lip : Params.ValueLipschitzWith (sp.smear V_S) KS)
    (h_stage_full : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        Params.LowerSlopeOn (fun s => sp.toParams.U_S x (α x) s) (Set.Icc (0 : ℝ) 1) mS) :
    ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
      StrictMonoOn (fun s => sp.toParams.senderDynObjective (sp.smear V_S) x (α x) s)
        Sanctions.I :=
  sp.senderDynObjective_shock_strictMonoOn_of_strong_rally_generalF
    (fun _ _ _ _ _ _ hle => (sp.toParams.abs_sanction_chord_of_affineF hF hle).le)
    hS_margin h_smear_lip h_stage_full

/-- **Shocked single crossing (the gate, `hSC_on`-shaped form; affine-restricted).**
The shocked Sender objective satisfies Milgrom–Shannon `SingleCrossingOn` in
`(sanction; state)` on the basin — the exact shape the persistence certificate's
`hSC_on` field consumes, but with the *smeared* continuation. Obtained from strict
monotonicity via the Interval-Dominance-Order route
(`SingleCrossingOn.of_choice_strictMono`).

Round BG (2026-10-06, BG2.6): the strict monotonicity is now taken from the
general-`F` theorem `senderDynObjective_shock_strictMonoOn_of_strong_rally_generalF`
at `d := δ`, with the exact affine sanction chord
`Params.abs_sanction_chord_of_affineF`. The binder `_hKS_nonneg` is kept so the
statement is unchanged, but it is no longer used: `0 ≤ KS` already follows from
`h_smear_lip`. -/
theorem senderDynObjective_shock_singleCrossingOn_of_strong_rally
    (hF : sp.toParams.F = Sanctions.AbstractGame.affineF sp.toParams.δ)
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS mS KS : ℝ}
    (_hKS_nonneg : 0 ≤ KS)
    (hS_margin : sp.toParams.β_S * KS * sp.toParams.δ < mS)
    (h_smear_lip : Params.ValueLipschitzWith (sp.smear V_S) KS)
    (h_stage_full : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        Params.LowerSlopeOn (fun s => sp.toParams.U_S x (α x) s) (Set.Icc (0 : ℝ) 1) mS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max xT xS) 1)
      (fun s x => sp.toParams.senderDynObjective (sp.smear V_S) x (α x) s) :=
  Sanctions.IntervalDominanceOrder.SingleCrossingOn.of_choice_strictMono (convex_Icc _ _)
    (sp.senderDynObjective_shock_strictMonoOn_of_strong_rally_generalF
      (fun _ _ _ _ _ _ hle => (sp.toParams.abs_sanction_chord_of_affineF hF hle).le)
      hS_margin h_smear_lip h_stage_full)

/-- **Shocked Target persistence / loss-offset monotonicity (Goal-1).** On the basin
high-sanction range `[max x sbar, 1]` the shocked Target dynamic objective
`s ↦ U_T(x, α x, s) + β_T · (smear V_T)(clipS'(F x s))` is *non-decreasing* in the
sanction `s` — the Target prefers to keep sanctions high (the persistence direction)
even under the atomless shock — from the loss-offset margin `β_T · KT · δ ≤ mT` and
`KT`-Lipschitzness of the *smeared* continuation `sp.smear V_T`. Same mechanism as the
Sender gate: the Target engine `targetSanctionObjective_mono_of_stage_lowerSlope_and_V_lipschitz`
applied at `V := sp.smear V_T`, with the smear preserving the Lipschitz constant. -/
theorem targetSanctionObjective_shock_monotoneOn_of_loss_offset
    (hF : sp.toParams.F = Sanctions.AbstractGame.affineF sp.toParams.δ)
    {V_T : SBCF} {α : ℝ → ℝ} {x sbar mT KT : ℝ}
    (hKT_nonneg : 0 ≤ KT)
    (hmargin : sp.toParams.β_T * KT * sp.toParams.δ ≤ mT)
    (h_stage : Params.LowerSlopeOn (fun s => sp.toParams.U_T x (α x) s)
      (Set.Icc (max x sbar) 1) mT)
    (h_smear_lip : Params.ValueLipschitzWith (sp.smear V_T) KT) :
    MonotoneOn (fun s => sp.toParams.targetSanctionObjective (sp.smear V_T) x (α x) s)
      (Set.Icc (max x sbar) 1) :=
  sp.toParams.targetSanctionObjective_mono_of_stage_lowerSlope_and_V_lipschitz
    hF hKT_nonneg hmargin h_stage h_smear_lip

/-- **Shocked dynamic-rule monotonicity (Goal-2 core).** The shocked *dynamic top
realized rule* `x ↦ σ_dyn_top(smear V_S, x, α x)` — the forward-looking Sender's
greatest best-response sanction at the smeared continuation — is *non-decreasing in
the state* on the basin. This is the monotone comparative static that pins the
forward-looking Sender at the high-sanction corner and is the engine of
dynamic-over-myopic dominance. Obtained by feeding the shocked single crossing into
the existing monotone-argmax engine `dynamicTopRealizedRule_mono_of_singleCrossingOn`.
Affine-restricted (it carries `hF`).

Round BG (2026-10-06, BG2.6): the single crossing is now built from the general-`F`
theorem `senderDynObjective_shock_strictMonoOn_of_strong_rally_generalF` at
`d := δ`, with the exact affine sanction chord `Params.abs_sanction_chord_of_affineF`
(the same route as `senderDynObjective_shock_singleCrossingOn_of_strong_rally`). The
binder `_hKS_nonneg` is kept so the statement is unchanged, but it is no longer
used: `0 ≤ KS` already follows from `h_smear_lip`. -/
theorem dynamicTopRealizedRule_shock_monotoneOn_of_strong_rally
    (hF : sp.toParams.F = Sanctions.AbstractGame.affineF sp.toParams.δ)
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS mS KS : ℝ}
    (_hKS_nonneg : 0 ≤ KS)
    (hS_margin : sp.toParams.β_S * KS * sp.toParams.δ < mS)
    (h_smear_lip : Params.ValueLipschitzWith (sp.smear V_S) KS)
    (h_stage_full : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        Params.LowerSlopeOn (fun s => sp.toParams.U_S x (α x) s) (Set.Icc (0 : ℝ) 1) mS) :
    MonotoneOn (sp.toParams.dynamicTopRealizedRule (sp.smear V_S) α)
      (Set.Icc (max xT xS) 1) :=
  sp.toParams.dynamicTopRealizedRule_mono_of_singleCrossingOn
    (Sanctions.IntervalDominanceOrder.SingleCrossingOn.of_choice_strictMono (convex_Icc _ _)
      (sp.senderDynObjective_shock_strictMonoOn_of_strong_rally_generalF
        (fun _ _ _ _ _ _ hle => (sp.toParams.abs_sanction_chord_of_affineF hF hle).le)
        hS_margin h_smear_lip h_stage_full))

end ShockedParams

/-- **Witness gate: shocked single crossing from the BASE value's primitives.** For
the box-kernel shocked model, the shocked Sender single crossing on the basin follows
from the strong-rally primitives stated on the *base* (un-smeared) value `V_S` — the
smear-preservation is discharged internally via
`movAvgShockedParams_smear_valueLipschitz`. This is the headline "single crossing
survives the atomless shock" in a directly usable, witness-instantiable form.
Affine-restricted (it carries `hF`).

Round BG (2026-10-06, BG2.6): this is the instance `d := δ` of the general-`F` gate
`movAvgShockedParams_senderDynObjective_shock_singleCrossingOn_of_strong_rally_generalF`
(`Theory/Shocked/ShockedSingleCrossing.lean`), with the exact affine sanction chord
`Params.abs_sanction_chord_of_affineF`. The binder `_hKS_nonneg` is kept so the
statement is unchanged, but it is no longer used: `0 ≤ KS` already follows from
`hV_S_lip`. -/
theorem movAvgShockedParams_senderDynObjective_shock_singleCrossingOn_of_strong_rally
    (q : Params) {h : ℝ} (hh : 0 < h)
    (hF : q.F = Sanctions.AbstractGame.affineF q.δ)
    {V_S : SBCF} {α : ℝ → ℝ} {xT xS mS KS : ℝ}
    (_hKS_nonneg : 0 ≤ KS)
    (hS_margin : q.β_S * KS * q.δ < mS)
    (hV_S_lip : Params.ValueLipschitzWith V_S KS)
    (h_stage_full : ∀ x ∈ Set.Icc (max xT xS) (1 : ℝ),
        Params.LowerSlopeOn (fun s => q.U_S x (α x) s) (Set.Icc (0 : ℝ) 1) mS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max xT xS) 1)
      (fun s x => q.senderDynObjective ((movAvgShockedParams q hh).smear V_S) x (α x) s) :=
  movAvgShockedParams_senderDynObjective_shock_singleCrossingOn_of_strong_rally_generalF q hh
    (fun _ _ _ _ _ _ hle => (q.abs_sanction_chord_of_affineF hF hle).le)
    hS_margin hV_S_lip h_stage_full

/-- **Witness Goal-1: shocked Target persistence from the BASE value's primitives.**
For the box-kernel shocked model, the shocked Target objective is non-decreasing in
the sanction on the basin (Target prefers to keep sanctions high — persistence) from
the loss-offset margin stated on the *base* (un-smeared) continuation `V_T`; the
smear-preservation is discharged internally. -/
theorem movAvgShockedParams_targetSanctionObjective_shock_monotoneOn_of_loss_offset
    (q : Params) {h : ℝ} (hh : 0 < h)
    (hF : q.F = Sanctions.AbstractGame.affineF q.δ)
    {V_T : SBCF} {α : ℝ → ℝ} {x sbar mT KT : ℝ}
    (hKT_nonneg : 0 ≤ KT)
    (hmargin : q.β_T * KT * q.δ ≤ mT)
    (h_stage : Params.LowerSlopeOn (fun s => q.U_T x (α x) s) (Set.Icc (max x sbar) 1) mT)
    (hV_T_lip : Params.ValueLipschitzWith V_T KT) :
    MonotoneOn
      (fun s => q.targetSanctionObjective ((movAvgShockedParams q hh).smear V_T) x (α x) s)
      (Set.Icc (max x sbar) 1) :=
  (movAvgShockedParams q hh).targetSanctionObjective_shock_monotoneOn_of_loss_offset
    hF hKT_nonneg hmargin h_stage
    (movAvgShockedParams_smear_valueLipschitz q hh hKT_nonneg hV_T_lip)

/-! ### The affine box-shock hysteresis pair (moved from `Theory/`, BH6.7)

Both theorems bind a bare `{δ : ℝ}` and write the saturated-basin closed loop as
`x ↦ (1−δ)x + δ`, the affine law at full sanction; they take no `Params`. They
are the instances `G := fun y => (1 − δ)·y + δ` of the bare-loop theorems
`basin_forward_invariant_of_closedLoop` and `basin_escape_of_closedLoop`
(`Theory/Shocked/ShockedHysteresis.lean`), whose `Params` forms
(`Params.basin_forward_invariant_iff_le_fullShockDrift`) give the threshold
`h ≤ d_F(xT) = F(xT, 1) − xT` for every transition; at the affine law
`d_F(xT) = δ·(1 − xT)`. Because the bare-loop theorems never mention `Params`,
these instances keep their validity at `δ = 1`. -/

/-- **Basin forward-invariance under the atomless box shock, affine instance.**
With the saturated basin closed loop `F(x, 1) = (1−δ)x + δ` and a box shock of
half-width `h`, if the shock budget `h ≤ δ·(1 − xT)` holds, then every basin state
`x ∈ [xT, 1]` maps under every realised shock `η ∈ [−h, h]` back into the basin:
the post-shock state `clipS((1−δ)x + δ + η)` lies in `[xT, 1]`. Hence the high
basin is absorbing for the noisy dynamics — the support of the next-state law
never escapes `[xT, 1]`.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** The loop is the affine law at a
bare `δ`. Since BH6.7 (2026-10-07) an instance of the general
`basin_forward_invariant_of_closedLoop` at `G := fun y => (1 − δ)·y + δ`:
`δ ≤ 1` makes that loop monotone, and the budget `δ·(1 − xT)` is its drift at the
floor. Moved here from `Theory/Shocked/ShockedHysteresis.lean`. The binder
`_hxT0` is kept so the statement is unchanged, but it is no longer used: the
clip already caps the state at `0`. -/
theorem basin_forward_invariant_under_box_shock
    {δ xT x η h : ℝ}
    (hδ1 : δ ≤ 1)
    (_hxT0 : 0 ≤ xT) (hxT1 : xT ≤ 1)
    (hx : xT ≤ x)
    (hη : |η| ≤ h)
    (hbudget : h ≤ δ * (1 - xT)) :
    xT ≤ Sanctions.clipS ((1 - δ) * x + δ + η)
      ∧ Sanctions.clipS ((1 - δ) * x + δ + η) ≤ 1 := by
  have hmono : (1 - δ) * xT + δ ≤ (1 - δ) * x + δ := by
    nlinarith [mul_le_mul_of_nonneg_left hx (sub_nonneg.2 hδ1)]
  have hdrift : h ≤ ((1 - δ) * xT + δ) - xT := by nlinarith [hbudget]
  exact basin_forward_invariant_of_closedLoop (G := fun y => (1 - δ) * y + δ)
    hxT1 hmono (abs_le.mp hη).1 hdrift

/-- **Basin escape in the wash-out regime, affine instance (the sharp complement
of Goal-3).** When the shock half-width strictly exceeds the budget,
`δ·(1 − xT) < h`, the worst-case down-shock `η = −h` from the basin floor `xT`
lands strictly below the watershed: `clipS((1−δ)·xT + δ − h) < xT`. Hence the
basin `[xT, 1]` is **not** forward-invariant — above the threshold the
high-sanction region leaks.

**⚠ AFFINE-RESTRICTED — axis 2 (Rule 22).** The loop is the affine law at a
bare `δ`. Since BH6.7 (2026-10-07) an instance of the general
`basin_escape_of_closedLoop` at `G := fun y => (1 − δ)·y + δ`. Moved here from
`Theory/Shocked/ShockedHysteresis.lean`. The binder `_hxT1` is kept so the
statement is unchanged, but it is no longer used: the escape reads nothing
about the floor beyond `0 < xT`. -/
theorem basin_escape_of_box_shock_wide
    {δ xT h : ℝ}
    (hxT0 : 0 < xT) (_hxT1 : xT ≤ 1)
    (hwide : δ * (1 - xT) < h) :
    Sanctions.clipS ((1 - δ) * xT + δ + (-h)) < xT := by
  have hw : ((1 - δ) * xT + δ) - xT < h := by nlinarith [hwide]
  exact basin_escape_of_closedLoop (G := fun y => (1 - δ) * y + δ) hxT0 hw

end AbstractGame

end

end Sanctions
