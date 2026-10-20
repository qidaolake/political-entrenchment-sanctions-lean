/-
Sanctions/Foundations/Curtat.lean

**Model-specific row-Lipschitz constants for a coupled Bellman operator
pair, using the invariant-carrier strategy of Curtat (1996).**

This module is the generic, pure-algebra version of the
operator-Lipschitz formula used in
`Theory/Bellman/OperatorRowLipschitz.lean`. It does **not** mention
the project's `AbstractGame.Params`; instead it works over abstract
pseudometric carriers `XT, XS` and exposes the row-Lipschitz tuple
`(β_T_row, L_TS, L_ST, β_S_row)` and the strict-margin Schur
inequalities as a pair of `structure`s (`CurtatPrimitiveLipschitzData`
holding the six primitive scalars; `CurtatRowLipschitzConstants` holding
the four derived scalars and their non-negativity + Schur margins).

**Model-specific accounting and the Curtat anchor.** For a coupled
Bellman pair `(T_T, T_S)` whose pointwise integrand admits primitive
C¹ partial-derivative bounds in the state, the leader action, and
the σ-mediated state-transition, the standard fixed-form
operator-Lipschitz coefficient on a value-class carrier is

**Methodological anchor (Bertsekas 2012, "Weighted Sup-Norm
Contractions in Dynamic Programming",
`PaperRefer/MathTheory/WeightedSupNormContractionsDP-Bertsekas-2012.md`).**
The asymmetric carrier `valLipBall R_T K_T × valLipBall R_S K_S` used
throughout `Theory/Bellman/InvariantLipBall.lean` is exactly an
instance of Bertsekas 2012 §2's weighted sup-norm contraction
framework: the joint operator `T(V_T, V_S) := (T_T V_T, T_S V_S)`
is a contraction in the weighted sup-norm
`‖(V_T, V_S)‖_w := max(‖V_T‖∞ / R_T, ‖V_S‖∞ / R_S)`. Bertsekas
2012 Proposition 2.1 (the Banach contraction theorem in weighted
sup-norm) is the abstract dynamic-programming theorem from which the
row-Lipschitz Schur-margin construction below specialises by reading off
the asymmetric `K_T ≠ K_S` row constants from the primitive payoff
Lipschitz scalars. The present closed form is the *specialisation* to
bilateral Stackelberg-Bellman systems;
Bertsekas 2012 is the *underlying weighted-contraction framework*
applicable to arbitrary multi-operator dynamic-programming systems.

**Canonical MDP-side anchor (Puterman 1994, *Markov Decision Processes*,
`BookRefer/Markov Decision Processes Discrete Stochastic Dynamic
Programming (Martin L. Puterman) 1994.md`).** Chapter 5
(Infinite-Horizon Models: Foundations) and Chapter 6 (Discounted
Markov Decision Problems) give the canonical Banach-fixed-point
treatment of the discounted Bellman operator under continuous-state
MDP assumptions. The single-operator setting of Puterman Ch. 6 is the
direct one-sided ancestor of our two-sided `T(V_T, V_S)`; the
Bertsekas 2012 weighted-sup-norm framework above is what extends
Puterman's single-operator contraction to the asymmetric two-operator
case. Citing the two anchors together gives the reader both the
canonical MDP-theory entry (Puterman Ch. 5-6) and the multi-operator
generalisation (Bertsekas 2012) on which our `joint_MPE_existence_from_Schur`
ultimately rests.

**Historical ancestors (Round-1.6 literature pass).** Two further
anchors document the historical lineage of the weighted-sup-norm
contraction framework and the row-Lipschitz Schur-margin construction:

* **Denardo 1967** *Contraction Mappings in the Theory Underlying
  Dynamic Programming*, SIAM Review 9(2) — the original abstract
  formulation that introduces the "contraction + monotonicity +
  N-stage contraction" trinity from which every later weighted-sup-
  norm theorem descends. See
  `PaperRefer/MathTheory/ContractionMappingsDP-Denardo-1967.md`.
* **Bertsekas-Tsitsiklis 1996** *Neuro-Dynamic Programming*
  Athena Scientific, Ch. 2 Proposition 2.2 (weighted-max-norm
  pseudo-contraction theorem). See `BookRefer/NDP.md` (markdown) /
  `BookRefer/NDP.pdf`. The proposition 2.2 contraction inequality is
  pointwise the abstract template that the closed form below
  specialises to bilateral Stackelberg-Bellman systems.

**Modern Lipschitz-MPE existence references (Round-1.6 pass).** The
project's joint-MPE existence chain via the Curtat Schur margin
sits alongside a family of alternative Lipschitz-MPE existence
routes that do not pass through a Schur margin. These are documented
for completeness; the `RaadWoznyAlternative` Lipschitz-non-expansion
route below is a candidate alternative for closing the joint
non-vacuity gap identified in the JET-referee Round 1 paper
revision:

* **Balbus-Reffett-Woźny 2012** *Stationary Markovian equilibrium
  in altruistic stochastic OLG models with limited commitment*, JME
  (`PaperRefer/MathTheory/StationaryMarkovianAltruisticOLG-BalbusReffettWozny-2012.md`).
* **Balbus-Reffett-Woźny 2013 JEDC** *A constructive geometrical
  approach to the uniqueness of Markov stationary equilibrium*
  (`PaperRefer/MathTheory/MarkovEquilibriumIntergenerationalAltruism-BalbusReffettWozny-2013.md`).
* **Balbus-Reffett-Woźny 2013 JET** (already in
  `Foundations/BalbusReffettWozny.lean`).
* **Balbus-Reffett-Woźny** *Dynamic Games in Macroeconomics*,
  Handbook of Dynamic Game Theory chapter
  (`PaperRefer/MathTheory/DynamicGamesInMacroeconomics-BalbusReffettWozny-monograph.md`)
  — the 50-page survey unifying the BRW family for macro
  applications.
* **Raad-Woźny 2019** *Lipschitz recursive equilibrium with a
  minimal state space and heterogeneous agents*, JME
  (`PaperRefer/MathTheory/LipschitzRecursiveEquilibrium-RaadWozny-2019.md`).
  Provides Schauder-on-Lipschitz-ball existence under
  Lipschitz-non-expansion of the fixed-point operator; does **not**
  require a Schur margin.

```
β_T_row = β_T              -- own-discount of the Target row
L_TS    = L_σ · (L_U + β_T · K_V · δ)
                          -- σ-mediated V_S → V_T coupling
                          -- L_σ: σ_dyn Lipschitz in V_S
                          -- L_U: stage payoff Lipschitz in state s
                          -- K_V: carrier value Lipschitz in state
                          -- δ : transition weight on the inner state
L_ST    = L_U_a · L_α_VT  -- α-mediated V_T → V_S coupling
                          -- L_U_a: Sender stage payoff Lipschitz in
                          --        the leader action a
                          -- L_α_VT: leader α Lipschitz in V_T
β_S_row = L_U_a · L_α_VS + β_S
                          -- direct β_S contraction plus α-mediated
                          -- V_S-dependence
```

These are the blockwise continuation-value Lipschitz constants obtained
from the present two-row Bellman operator. Curtat's Theorem 4.5
motivates the invariant compact set of state-Lipschitz continuation
values, but its proof does not print this model-specific Schur matrix.
Here the constants are *derived* from the six **primitive**
payoff/policy-Lipschitz scalars
`(L_σ, L_U, K_V, L_α_VT, L_α_VS, L_U_a)` together with the ambient
model parameters `(β_T, β_S, δ)`.

**Rule 19 placement.** The closed-form formula is generic math content
(not project-specific), so it lives in `Foundations/`. The
`Params`-level constructor that consumed a
`CurtatPrimitiveLipschitzData` and discharged the certificate's four
row-Lipschitz scalars + two operator Props belonged to the
resistance-action certificate family, which was **deleted on
2026-08-17** as unreachable; see the header of
`Theory/Certificates/RegularEconomy.lean`. The closed form itself is
unaffected and remains available to any consumer.

**Rule 3 status.** Pure cat-2 weakening: a `CurtatPrimitiveLipschitzData`
bundles **six existing primitive Lipschitz constants** that were
already being supplied separately; the wrapper just packages them and
re-exports the four operator-Lipschitz scalars as derived defs. No new
`Params` field, no new content-level Prop. The `L_α_VT, L_α_VS`
constants are inputs to the closed form, not outputs; at the `Params`
level they are DISCHARGED by the R31/R32 dischargers
`alphaOnLipschitzOn_of_IFT_chord_form` and
`alphaOnLipschitzOn_of_C2_Hessian_lower_bound` (both in
`Theory/Certificates/RegularEconomy.lean`), whose FOC / chord-form
strong-concavity / cross-Lipschitz inputs remain theorem parameters.

## What this module exports

* `CurtatPrimitiveLipschitzData β_T β_S δ` — the six primitive
  payoff-Lipschitz scalars plus the ambient `(β_T, β_S, δ)` values.
  Non-negativity of all six primitive scalars and `δ ≥ 0` is built in.

* `CurtatRowLipschitzConstants` — the four derived row-Lipschitz
  scalars `(β_T_row, β_S_row, L_TS, L_ST)`, plus non-negativity, plus
  the Schur strict-margin inequalities `β_T_row + L_TS < 1` and
  `β_S_row + L_ST < 1`.

* `CurtatPrimitiveLipschitzData.toRow` — the closed-form constructor:
  from primitive Lipschitz data plus the two Schur margins, produce
  the row-Lipschitz constants. This is the one-line statement that
  the `Params`-level constructor in
  `Theory/Certificates/RegularEconomy.lean` consumes.
-/

import Sanctions.Foundations.Basic
import Sanctions.Foundations.StokeyLucas

namespace Sanctions
namespace Foundations
namespace Curtat

/-- **Primitive payoff-Lipschitz data for the two-row closed form.**

Bundles the six primitive scalars `(L_σ, L_U, K_V, L_U_a, L_α_VT,
L_α_VS)` used to derive the operator-Lipschitz closed form, together
with the ambient discount/transition data `(β_T, β_S, δ)`.
Non-negativity of every scalar is built in.

**Plain-language gloss of each field:**

* `L_σ` — Lipschitz constant of the dynamic Sender selector `σ_dyn`
  in the Sender value function `V_S` (under the BCF metric). The σ
  selector lifts continuously in `V_S` because the Sender stage
  objective is parameter-continuous; the rate at which it does so
  is `L_σ`.
* `L_U` — Lipschitz constant of the Target stage payoff `U_T(x, a, s)`
  in the sanction level `s`. (`L_U_a` plays the analogous role for
  the Sender payoff `U_S` in the leader action `a`.)
* `K_V` — Uniform Lipschitz constant of carrier value functions in
  the state. Used inside the discounted continuation term
  `β_T · K_V · δ`.
* `L_U_a` — Lipschitz constant of the Sender stage payoff `U_S`
  in the leader action `a`. The α-mediated coupling propagates
  through `U_S(x, α V W x, s)` with rate `L_U_a · L_α_*`.
* `L_α_VT, L_α_VS` — Lipschitz constants of the equilibrium leader
  selector `α_on` in `V_T` and `V_S` respectively (IFT-style; treated
  as primitives at this stage).
* `β_T, β_S` — Target / Sender discount factors.
* `δ` — Transition weight on the inner state argument
  `x' = (1-δ) x + δ s`.
-/
structure CurtatPrimitiveLipschitzData (β_T β_S δ : ℝ) where
  /-- σ_dyn-Lipschitz constant in V_S. -/
  L_σ : ℝ
  /-- Target stage payoff Lipschitz constant in state. -/
  L_U : ℝ
  /-- Carrier value Lipschitz constant. -/
  K_V : ℝ
  /-- Sender stage payoff Lipschitz constant in the leader action. -/
  L_U_a : ℝ
  /-- α_on Lipschitz constant in V_T. -/
  L_α_VT : ℝ
  /-- α_on Lipschitz constant in V_S. -/
  L_α_VS : ℝ
  hL_σ_nn : 0 ≤ L_σ
  hL_U_nn : 0 ≤ L_U
  hK_V_nn : 0 ≤ K_V
  hL_U_a_nn : 0 ≤ L_U_a
  hL_α_VT_nn : 0 ≤ L_α_VT
  hL_α_VS_nn : 0 ≤ L_α_VS
  hβ_T_nn : 0 ≤ β_T
  hβ_S_nn : 0 ≤ β_S
  hδ_nn : 0 ≤ δ

/-- **Derived row-Lipschitz constants for the joint Bellman operator
pair.** The four
scalars `(β_T_row, L_TS, L_ST, β_S_row)` are the coefficients in the
row-form

```
dist (T_T (V, W)) (T_T (V', W')) ≤ β_T_row · dist V V' + L_TS · dist W W'
dist (T_S (V, W)) (T_S (V', W')) ≤ L_ST · dist V V' + β_S_row · dist W W'
```

and the strict Schur margins `β_T_row + L_TS < 1`,
`β_S_row + L_ST < 1` are the standard sufficient conditions for the
joint operator to be a strict contraction in the product metric, by
either the Perron row-sum / max-row-sum argument or by the explicit
weighted-norm Banach iteration. -/
structure CurtatRowLipschitzConstants where
  β_T_row : ℝ
  β_S_row : ℝ
  L_TS : ℝ
  L_ST : ℝ
  hβ_T_row_nn : 0 ≤ β_T_row
  hβ_S_row_nn : 0 ≤ β_S_row
  hL_TS_nn : 0 ≤ L_TS
  hL_ST_nn : 0 ≤ L_ST
  /-- Schur strict-margin inequality, Target row. -/
  hsuff_T : β_T_row + L_TS < 1
  /-- Schur strict-margin inequality, Sender row. -/
  hsuff_S : β_S_row + L_ST < 1

namespace CurtatPrimitiveLipschitzData

variable {β_T β_S δ : ℝ}

/-- **Closed-form Target-row Lipschitz coefficient `β_T_row`.**
The own-`V_T` row-Lipschitz coefficient of the joint Target Bellman is
the Target discount factor `β_T`. -/
def β_T_row (_C : CurtatPrimitiveLipschitzData β_T β_S δ) : ℝ := β_T

/-- **Closed-form `V_S → V_T` cross-coefficient `L_TS`.**
This is the `σ_dyn`-Lipschitz modulus in `V_S` times the combined
`V_S` contribution `L_U + β_T · K_V · δ` (stage Lipschitz in state
plus discounted carrier-value Lipschitz). -/
def L_TS (C : CurtatPrimitiveLipschitzData β_T β_S δ) : ℝ :=
  C.L_σ * (C.L_U + β_T * C.K_V * δ)

/-- **Closed-form `V_T → V_S` cross-coefficient `L_ST`.**
This is the Sender stage-payoff Lipschitz modulus in the leader action
times the leader-policy Lipschitz modulus in `V_T`. -/
def L_ST (C : CurtatPrimitiveLipschitzData β_T β_S δ) : ℝ :=
  C.L_U_a * C.L_α_VT

/-- **Closed-form Sender-row Lipschitz coefficient `β_S_row`.**
For the present Sender Bellman row, this is the direct sup-norm
continuation coefficient `β_S` plus the α-mediated `V_S` dependence
`L_U_a · L_α_VS`. -/
def β_S_row (C : CurtatPrimitiveLipschitzData β_T β_S δ) : ℝ :=
  C.L_U_a * C.L_α_VS + β_S

/-- Non-negativity of the Target-row Lipschitz coefficient. -/
lemma β_T_row_nonneg (C : CurtatPrimitiveLipschitzData β_T β_S δ) :
    0 ≤ C.β_T_row := C.hβ_T_nn

/-- Non-negativity of the `V_S → V_T` cross-coefficient. -/
lemma L_TS_nonneg (C : CurtatPrimitiveLipschitzData β_T β_S δ) :
    0 ≤ C.L_TS := by
  unfold L_TS
  apply mul_nonneg C.hL_σ_nn
  have h₁ : 0 ≤ β_T * C.K_V * δ :=
    mul_nonneg (mul_nonneg C.hβ_T_nn C.hK_V_nn) C.hδ_nn
  linarith [C.hL_U_nn]

/-- Non-negativity of the `V_T → V_S` cross-coefficient. -/
lemma L_ST_nonneg (C : CurtatPrimitiveLipschitzData β_T β_S δ) :
    0 ≤ C.L_ST :=
  mul_nonneg C.hL_U_a_nn C.hL_α_VT_nn

/-- Non-negativity of the Sender-row Lipschitz coefficient. -/
lemma β_S_row_nonneg (C : CurtatPrimitiveLipschitzData β_T β_S δ) :
    0 ≤ C.β_S_row := by
  unfold β_S_row
  exact add_nonneg (mul_nonneg C.hL_U_a_nn C.hL_α_VS_nn) C.hβ_S_nn

/-- **Closed-form constructor for the operator row-Lipschitz constants.**

From the six primitive payoff-Lipschitz scalars in `C` plus the two
Schur strict-margin inequalities

* `β_T + L_σ · (L_U + β_T · K_V · δ) < 1`     (Target row)
* `(L_U_a · L_α_VS + β_S) + L_U_a · L_α_VT < 1` (Sender row)

produce the row-Lipschitz constants `(β_T_row, β_S_row, L_TS, L_ST)`
with their non-negativity and Schur margins, packaged as a
`CurtatRowLipschitzConstants`.

This is the generic Foundations-level lemma. The Params-level
discharge (turning each row-Lipschitz constant into a *proved*
operator-Lipschitz bound on the project's joint Bellman pair) lives
in `Theory/Certificates/RegularEconomy.lean` and consumes this
constructor as its closed-form input. Curtat 1996 Theorem 4.5 supplies
the broader invariant-set strategy; the displayed two-row constants
are specific to this Bellman operator. -/
def toRow (C : CurtatPrimitiveLipschitzData β_T β_S δ)
    (hsuff_T : C.β_T_row + C.L_TS < 1)
    (hsuff_S : C.β_S_row + C.L_ST < 1) :
    CurtatRowLipschitzConstants where
  β_T_row := C.β_T_row
  β_S_row := C.β_S_row
  L_TS := C.L_TS
  L_ST := C.L_ST
  hβ_T_row_nn := C.β_T_row_nonneg
  hβ_S_row_nn := C.β_S_row_nonneg
  hL_TS_nn := C.L_TS_nonneg
  hL_ST_nn := C.L_ST_nonneg
  hsuff_T := hsuff_T
  hsuff_S := hsuff_S

/-! ## Round 44 — Affine Curtat compatibility primitives under uniform
    strict concavity of `U_S` in `s`

User-approved Rule-3 trade (2026-06-05): adopt strict concavity of
the Sender stage payoff `U_S` in the sanction `s` as a project-wide
C² structural assumption. The economic content is **diminishing
returns to sanctioning** — each additional unit of sanction extracts
less marginal coercive value. This is the canonical sanctions-
economics assumption (Kaempfer-Lowenberg 1988 implicit; Eaton 1992
explicit; satisfied by every standard polynomial / logarithmic /
exponential sanction-cost model).

Under uniform strict concavity in `s` with modulus `c_σ > 0`, two
Curtat primitives are auto-derived:

For the affine transition, the following two Curtat primitives have
closed forms:

* `K_V` (uniform carrier value Lipschitz) — affine closed form
  `max(L_U_S/(1-β_S(1-δ)), L_U_T/(1-β_T(1-δ)))` via the R25 Hinderer 4.2(c)
  envelope on the Sender carrier and its R27 analog on the Target
  carrier.

* `L_σ` (Sender selector Lipschitz in `V_S`) — closed form
  `β_S · K_V_Sender / c_σ` via the implicit-function theorem, where
  `K_V_Sender = L_U_S/(1-β_S(1-δ))` is the Sender carrier value
  Lipschitz. Analog of R31's `L_α_VT := K_T_IFT / c`.

The affine reduced primitive surface is `(L_U_T, L_U_a, L_α_VT, L_α_VS,
L_U_S, c_σ)` — six scalars instead of Curtat's original six
`(L_σ, L_U, K_V, L_U_a, L_α_VT, L_α_VS)`, but two of the original
(L_σ, K_V) become derived rather than primitive. Plus the existing
`L_U_S` is reused from \Cref{ass:sender_pref}. Net cognitive load
reduction: the user no longer separately verifies `L_σ` and `K_V`;
they are determined by the structural primitives.

The user can either supply `c_σ` as a numeric scalar directly (with
the `0 < c_σ` positivity proof) or derive it from a strict-concavity
assumption via the companion Foundations lemma
`Sanctions.StokeyLucas.cube_inf_pos_unitCube_of_continuous_pos`
(R44 Foundations). -/

/-- **R44 closed-form Sender carrier value Lipschitz.** Equals the
    R25 closed-form constant (Hinderer 4.2(c)) `L_U_S / (1 − β_S · (1 − δ))` specialized
    to the affine transition modulus `γ_F = 1 − δ`.  General
    transitions use their separately established state modulus. -/
noncomputable def K_V_Sender_canonical (β_S δ L_U_S : ℝ) : ℝ :=
  Sanctions.StokeyLucas.bellmanLipConstant β_S (1 - δ) L_U_S

/-- **R44 affine closed-form Target carrier value Lipschitz.** Same
    affine envelope on the Target side:
    `L_U_T / (1 − β_T · (1 − δ))`. -/
noncomputable def K_V_Target_canonical (β_T δ L_U_T : ℝ) : ℝ :=
  Sanctions.StokeyLucas.bellmanLipConstant β_T (1 - δ) L_U_T

/-- **R44 closed-form uniform carrier value Lipschitz**, the max
    over the Sender and Target sides. Replaces Curtat's `K_V`
    primitive under the L_U_T trade. -/
noncomputable def K_V_canonical (β_T β_S δ L_U_S L_U_T : ℝ) : ℝ :=
  max (K_V_Sender_canonical β_S δ L_U_S) (K_V_Target_canonical β_T δ L_U_T)

/-- **R44 closed-form Sender selector Lipschitz in `V_S` via IFT.**
    Under strict concavity of `U_S` in `s` with modulus `c_σ > 0`,
    `L_σ := β_S · K_V_Sender / c_σ` (analog of R31's
    `L_α_VT := K_T_IFT / c`). -/
noncomputable def L_sigma_canonical (β_S δ L_U_S c_σ : ℝ) : ℝ :=
  β_S * K_V_Sender_canonical β_S δ L_U_S / c_σ

/-- **R44 helper: positivity of the canonical Sender K_V closed form
    under Params-style constraints.** Under `β_S ∈ [0, 1)`,
    `δ ∈ (0, 1)`, the denominator `1 − β_S · (1 − δ) > 0`, so
    `K_V_Sender = L_U_S / (1 − β_S · (1 − δ)) ≥ 0` from
    `L_U_S ≥ 0`. -/
lemma K_V_Sender_canonical_nonneg
    {β_S δ L_U_S : ℝ}
    (hβ_S_nn : 0 ≤ β_S) (hβ_S_lt : β_S < 1)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hL_U_S_nn : 0 ≤ L_U_S) :
    0 ≤ K_V_Sender_canonical β_S δ L_U_S := by
  unfold K_V_Sender_canonical Sanctions.StokeyLucas.bellmanLipConstant
  have h_one_sub_delta_le_one : 1 - δ ≤ 1 := by linarith
  have h_prod_le : β_S * (1 - δ) ≤ β_S := by
    have h_one_sub_delta_nn : 0 ≤ 1 - δ := by linarith
    calc β_S * (1 - δ) ≤ β_S * 1 := by gcongr
      _ = β_S := mul_one _
  have h_denom_pos : 0 < 1 - β_S * (1 - δ) := by linarith
  exact div_nonneg hL_U_S_nn (le_of_lt h_denom_pos)

/-- **R44 helper: positivity of the canonical Target K_V closed
    form.** Same pattern on the Target side. -/
lemma K_V_Target_canonical_nonneg
    {β_T δ L_U_T : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_T_lt : β_T < 1)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hL_U_T_nn : 0 ≤ L_U_T) :
    0 ≤ K_V_Target_canonical β_T δ L_U_T := by
  unfold K_V_Target_canonical Sanctions.StokeyLucas.bellmanLipConstant
  have h_one_sub_delta_le_one : 1 - δ ≤ 1 := by linarith
  have h_prod_le : β_T * (1 - δ) ≤ β_T := by
    have h_one_sub_delta_nn : 0 ≤ 1 - δ := by linarith
    calc β_T * (1 - δ) ≤ β_T * 1 := by gcongr
      _ = β_T := mul_one _
  have h_denom_pos : 0 < 1 - β_T * (1 - δ) := by linarith
  exact div_nonneg hL_U_T_nn (le_of_lt h_denom_pos)

/-- **R44 helper: non-negativity of the canonical K_V max.** -/
lemma K_V_canonical_nonneg
    {β_T β_S δ L_U_S L_U_T : ℝ}
    (_hβ_T_nn : 0 ≤ β_T) (_hβ_T_lt : β_T < 1)
    (hβ_S_nn : 0 ≤ β_S) (hβ_S_lt : β_S < 1)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hL_U_S_nn : 0 ≤ L_U_S) (_hL_U_T_nn : 0 ≤ L_U_T) :
    0 ≤ K_V_canonical β_T β_S δ L_U_S L_U_T := by
  unfold K_V_canonical
  exact le_max_of_le_left
    (K_V_Sender_canonical_nonneg hβ_S_nn hβ_S_lt hδ_pos hδ_lt hL_U_S_nn)

/-- **R44 helper: non-negativity of the canonical L_σ closed form.**
    `L_σ = β_S · K_V_Sender / c_σ ≥ 0` from `β_S ≥ 0`,
    `K_V_Sender ≥ 0`, and `c_σ > 0`. -/
lemma L_sigma_canonical_nonneg
    {β_S δ L_U_S c_σ : ℝ}
    (hβ_S_nn : 0 ≤ β_S) (hβ_S_lt : β_S < 1)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hL_U_S_nn : 0 ≤ L_U_S)
    (hc_σ_pos : 0 < c_σ) :
    0 ≤ L_sigma_canonical β_S δ L_U_S c_σ := by
  unfold L_sigma_canonical
  have hKV_nn :=
    K_V_Sender_canonical_nonneg hβ_S_nn hβ_S_lt hδ_pos hδ_lt hL_U_S_nn
  have h_num_nn : 0 ≤ β_S * K_V_Sender_canonical β_S δ L_U_S :=
    mul_nonneg hβ_S_nn hKV_nn
  exact div_nonneg h_num_nn (le_of_lt hc_σ_pos)

/-- **R44 canonical constructor.** Builds a
    `CurtatPrimitiveLipschitzData` from a reduced primitive set
    that eliminates `L_σ` and `K_V` via closed-form derivation.

    The user supplies:

    * `L_U_T` — Target stage payoff Lipschitz in `s` (renamed from
      Curtat's `L_U` for symmetry with `L_U_S`).
    * `L_U_a` — action-coordinate Lipschitz (unchanged).
    * `L_α_VT, L_α_VS` — α-selector Lipschitz constants in `V_T, V_S`
      (R31-derivable from IFT chord-form; here taken as inputs).
    * `L_U_S` — Sender stage payoff Lipschitz in `s` (already on the
      `\Cref{ass:sender_pref}` surface).
    * `c_σ > 0` — strong-concavity modulus of `U_S` in `s` (Rule-3
      trade: the new structural primitive; auto-derivable from a
      uniform-strict-concavity hypothesis via the Foundations
      lemma `cube_inf_pos_unitCube_of_continuous_pos`).

    The derived values are:

    * `L_σ := β_S · K_V_Sender / c_σ` (IFT closed form).
    * `K_V := max(L_U_S/(1-β_S(1-δ)), L_U_T/(1-β_T(1-δ)))` (R25 + R27
      envelope closed form).

    Net cognitive load reduction: user no longer separately verifies
    `L_σ` and `K_V`; they are auto-computed from the more
    fundamental primitives `(L_U_S, L_U_T, c_σ)`. -/
noncomputable def ofCanonical
    {β_T β_S δ : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_T_lt : β_T < 1)
    (hβ_S_nn : 0 ≤ β_S) (hβ_S_lt : β_S < 1)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (L_U_T : ℝ) (hL_U_T_nn : 0 ≤ L_U_T)
    (L_U_a : ℝ) (hL_U_a_nn : 0 ≤ L_U_a)
    (L_α_VT : ℝ) (hL_α_VT_nn : 0 ≤ L_α_VT)
    (L_α_VS : ℝ) (hL_α_VS_nn : 0 ≤ L_α_VS)
    (L_U_S : ℝ) (hL_U_S_nn : 0 ≤ L_U_S)
    (c_σ : ℝ) (hc_σ_pos : 0 < c_σ) :
    CurtatPrimitiveLipschitzData β_T β_S δ where
  L_σ := L_sigma_canonical β_S δ L_U_S c_σ
  L_U := L_U_T
  K_V := K_V_canonical β_T β_S δ L_U_S L_U_T
  L_U_a := L_U_a
  L_α_VT := L_α_VT
  L_α_VS := L_α_VS
  hL_σ_nn :=
    L_sigma_canonical_nonneg hβ_S_nn hβ_S_lt hδ_pos hδ_lt
      hL_U_S_nn hc_σ_pos
  hL_U_nn := hL_U_T_nn
  hK_V_nn :=
    K_V_canonical_nonneg hβ_T_nn hβ_T_lt hβ_S_nn hβ_S_lt hδ_pos hδ_lt
      hL_U_S_nn hL_U_T_nn
  hL_U_a_nn := hL_U_a_nn
  hL_α_VT_nn := hL_α_VT_nn
  hL_α_VS_nn := hL_α_VS_nn
  hβ_T_nn := hβ_T_nn
  hβ_S_nn := hβ_S_nn
  hδ_nn := le_of_lt hδ_pos

end CurtatPrimitiveLipschitzData

/-- **Sanity lemma: the two-row closed form is invariant under
re-bundling.** Reads off the four derived coefficients from `toRow`
in the obvious way; useful for downstream proofs that prefer working
with the bundled `CurtatRowLipschitzConstants` instead of the
underlying primitive data. -/
@[simp] lemma toRow_β_T_row {β_T β_S δ : ℝ}
    (C : CurtatPrimitiveLipschitzData β_T β_S δ)
    (hT : C.β_T_row + C.L_TS < 1) (hS : C.β_S_row + C.L_ST < 1) :
    (C.toRow hT hS).β_T_row = β_T := rfl

@[simp] lemma toRow_L_TS {β_T β_S δ : ℝ}
    (C : CurtatPrimitiveLipschitzData β_T β_S δ)
    (hT : C.β_T_row + C.L_TS < 1) (hS : C.β_S_row + C.L_ST < 1) :
    (C.toRow hT hS).L_TS = C.L_σ * (C.L_U + β_T * C.K_V * δ) := rfl

@[simp] lemma toRow_L_ST {β_T β_S δ : ℝ}
    (C : CurtatPrimitiveLipschitzData β_T β_S δ)
    (hT : C.β_T_row + C.L_TS < 1) (hS : C.β_S_row + C.L_ST < 1) :
    (C.toRow hT hS).L_ST = C.L_U_a * C.L_α_VT := rfl

@[simp] lemma toRow_β_S_row {β_T β_S δ : ℝ}
    (C : CurtatPrimitiveLipschitzData β_T β_S δ)
    (hT : C.β_T_row + C.L_TS < 1) (hS : C.β_S_row + C.L_ST < 1) :
    (C.toRow hT hS).β_S_row = C.L_U_a * C.L_α_VS + β_S := rfl

end Curtat
end Foundations
end Sanctions
