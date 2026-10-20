/-
Sanctions/Examples/ClosedLoopInvariantLaw.lean

**The invariant law of the ENDOGENOUS (equilibrium-driven) state chain, and
the honest uniqueness boundary.**

`Foundations/ClosedLoopBoxTransfer.lean` supplies the drift-generic engine:
the box-noise chain `x' = clipS'(g(x) + η)` has an invariant probability law
for every continuous drift `g` (Krylov–Bogolyubov), and — conditionally, when
`Lip(g) < 1` — a unique, geometrically attracting one (dualKR). This file
does the project wiring:

* **`equilibrium_closedLoop_exists_invariant`** — at any shocked
  feedback-Stackelberg TOP equilibrium whose realized-sanction rule
  `s_real(x) = σ_dyn_top (smear V_S) x (α x)` is continuous (the standing
  `hσc` continuity input that the conditional shocked wrappers
  `coupledSchur_exists_equilibrium` and `lowDelta_purified_existence`, and the
  separate mechanism-witness construction, already consume — NOT re-derived
  here), the equilibrium closed-loop drift
  `g(x) = F(x, s_real(x))` is continuous and the **endogenous** political
  state chain has a stationary long-run law. This is the equilibrium-driven
  counterpart of the exogenous wash-out law (headline row 15,
  `boxTransfer_existsUnique_invariant_attracting`, whose chain holds the
  sanction constant); Bressan–Jiang distributional self-consistency is
  automatic for the per-state TOP concept (the policies are μ-blind), so the
  pair (TOP equilibrium, this invariant law) IS the degenerate-reading
  distributional object (see `docs/archive/workflow-scratch/w4_dist_memo_source.md`, Reading D).

* **Non-vacuity** — `p3_closedLoop_exists_invariant` instantiates the engine
  at an explicit, genuinely state-dependent continuous rule: the P3 myopic
  realized-sanction form `s_real(x) = clip((9/8)·x − 1/12)` (= the Rule-1
  coupled static Sender best response `mwσ x 0`,
  `p3RealizedRule_eq_mwσ_zero`; optimality certificate `mwσ_isMaxOn`) under
  the P3 transition `F = affineF (1/5)`. The drift
  `(4/5)·x + (1/5)·clip((9/8)x − 1/12)` is NOT of the constant-sanction box
  form, so the closed-loop generalization is exercised for real.

* **The honest uniqueness boundary, the arithmetic** —
  `closedLoop_dualKR_route_blocked`: at the witness realized-sanction slope
  `L_s = 9/8`, the affine estimate of the closed-loop drift Lipschitz factor
  is exactly `(1−δ) + δ·(9/8) = 1 + δ/8 > 1` for every `δ > 0` (hence for
  every `δ ∈ (0,1)`), with exact deficit `δ/8` (`41/40` at `δ = 1/5`,
  `801/800` at `δ = 1/100`). So this estimate cannot deliver the conditional
  contraction hypothesis `L_g < 1` of `closedLoopBoxTransfer_unique_invariant`;
  that the hypothesis itself FAILS at the P3 witness rule is the next bullet
  (`affineP3ClosedLoopDrift_lipConst_ge`). This is the same
  `27/20` vs `6/5` frontier that refuted the distributional concept
  (Wave-4 declination): `L_s < 1 ⟺ |∂²U_S/∂s∂x| < |∂²U_S/∂s²|`, i.e.
  `27/20 < 6/5`, false by exactly `3/20` — and the violating rally term IS
  the paper's mechanism. Existence stands unconditionally; uniqueness /
  attraction of the endogenous law is honestly open at these witnesses.

* **The boundary as a refutation of the hypothesis** (round BH-2, item
  BH2.11) — `affineP3ClosedLoopDrift_lipConst_ge`: for every `δ ≥ 0`, every
  Lipschitz constant of the affine drift `x ↦ (1−δ)x + δ·s_real(x)` at the
  P3 rule is at least `1 + δ/8`, and `p3ClosedLoopDrift_lipConst_ge`: the P3
  drift has none below `41/40`. Both are instances of the general-`F` lemma
  `closedLoop_lipConst_ge_of_diagonal_crossing`
  (`Foundations/ClosedLoopBoxTransfer.lean`): the rule crosses the diagonal at
  `2/3` and rises above it at excess slope `1/8`. Unlike the arithmetic of
  `closedLoop_dualKR_route_blocked`, these refute the bound `hgL` itself: the
  conditional contraction hypothesis `L_g < 1` provably FAILS at the P3
  witness rule under every affine transition. No equilibrium realized-sanction
  drift (`equilibriumDrift`) is checked against it.

Rule-1: the realized rule in the headline is equilibrium-derived (the
equilibrium's own σ_dyn_top response at the equilibrium leader policy); the
non-vacuity rule carries its optimality certificate (`mwσ_isMaxOn`). Rule-3:
no new assumptions — `hσc` is the standing theorem-level continuity input of
the shocked existence layer, not a new primitive.
-/

import Sanctions.Foundations.ClosedLoopBoxTransfer
import Sanctions.Theory.Shocked.ShockedEquilibrium
import Sanctions.Examples.MechanismWitness

namespace Sanctions
namespace Examples

open MeasureTheory AbstractGame BoundedContinuousFunction

noncomputable section

/-! ## The equilibrium realized-sanction rule and closed-loop drift -/

/-- **Equilibrium realized-sanction rule** of a shocked feedback-Stackelberg
TOP equilibrium: the shocked Sender response `σ_dyn_top (smear V_S)`
evaluated at the equilibrium leader policy, `s_real(x) = σ(x, α(x))`. Both
ingredients are the equilibrium's own optimizers (Rule 1): `σ_dyn_top` is the
greatest dynamic-argmax selector of the smeared Sender objective, and `α` is
the leader argmax (`E.α_opt_shock`). -/
noncomputable def realizedSanctionRule (sp : AbstractGame.ShockedParams)
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop) :
    ↥(Sanctions.S : Set ℝ) → ℝ :=
  fun x => sp.toParams.σ_dyn_top (sp.smear E.V_S) x.val (E.α x.val)

/-- Continuity of the realized-sanction rule, from the standing `hσc`
continuity input (joint continuity of the shocked Sender selector — exactly
what the constructed shocked existence theorems consume) and the
equilibrium's own leader-policy continuity `E.hα`. -/
theorem realizedSanctionRule_continuous (sp : AbstractGame.ShockedParams)
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (hσc : Continuous (fun xa : ℝ × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear E.V_S) xa.1 xa.2)) :
    Continuous (realizedSanctionRule sp E) :=
  hσc.comp (continuous_subtype_val.prodMk (E.hα.comp continuous_subtype_val))

/-- **Equilibrium closed-loop drift**: the pre-noise next state under the
equilibrium realized-sanction rule, `g(x) = F(x, s_real(x))`. The endogenous
chain is `x' = clipS'(g(x) + η)`, i.e. `closedLoopBoxTransfer` at this
drift. -/
noncomputable def equilibriumDrift (sp : AbstractGame.ShockedParams)
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop) :
    ↥(Sanctions.S : Set ℝ) → ℝ :=
  fun x => sp.toParams.F x.val (realizedSanctionRule sp E x)

/-- The equilibrium closed-loop drift is continuous (transition continuity
`F_continuous` composed with the continuous realized rule). -/
theorem equilibriumDrift_continuous (sp : AbstractGame.ShockedParams)
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (hσc : Continuous (fun xa : ℝ × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear E.V_S) xa.1 xa.2)) :
    Continuous (equilibriumDrift sp E) :=
  sp.toParams.F_continuous.comp
    (continuous_subtype_val.prodMk (realizedSanctionRule_continuous sp E hσc))

/-! ## The endogenous invariant law -/

/-- **The equilibrium-driven political state has a stationary long-run
law.** At any shocked feedback-Stackelberg TOP equilibrium with continuous
realized-sanction rule (the standing `hσc` input of the constructed shocked
existence theorems), the ENDOGENOUS closed-loop chain
`x' = clipS'(F(x, s_real(x)) + η)` admits an invariant probability law —
Krylov–Bogolyubov at the equilibrium drift, no restriction on the drift's
slope. This is the endogenous counterpart of the exogenous wash-out law
(headline row 15): there the sanction is held constant; here it is the
equilibrium's own realized response. Uniqueness/attraction is NOT claimed.
At the strong-rally witness rule (the P3 myopic rule `clip((9/8)x − 1/12)`, a
static best response rather than this theorem's equilibrium drift) the `L < 1`
hypothesis of the dualKR route provably fails
(`affineP3ClosedLoopDrift_lipConst_ge`, `p3ClosedLoopDrift_lipConst_ge`;
`closedLoop_dualKR_route_blocked` is the arithmetic of the affine estimate);
whether it holds at this equilibrium's own drift is not decided here. -/
theorem equilibrium_closedLoop_exists_invariant (sp : AbstractGame.ShockedParams)
    (E : sp.ShockedFeedbackStackelbergEquilibriumTop)
    (hσc : Continuous (fun xa : ℝ × ℝ =>
      sp.toParams.σ_dyn_top (sp.smear E.V_S) xa.1 xa.2))
    (h : ℝ) (hh : 0 < h) :
    ∃ μ : Measure ↥(Sanctions.S : Set ℝ),
      IsProbabilityMeasure μ ∧ closedLoopBoxTransfer (equilibriumDrift sp E) h μ = μ :=
  closedLoopBoxTransfer_exists_invariant (equilibriumDrift sp E)
    (equilibriumDrift_continuous sp E hσc) h hh

/-! ## Non-vacuity at an explicit state-dependent rule (P3 myopic form) -/

/-- The **P3 myopic realized-sanction rule** `s_real(x) = clip((9/8)·x − 1/12)`
— an explicit affine-clip, genuinely state-dependent continuous rule (the
myopic realized form of the P3 Sender response at leader action `0`; see
`p3RealizedRule_eq_mwσ_zero` for the Rule-1 tie to the optimality-certified
selector `mwσ`). -/
noncomputable def p3RealizedRule : ↥(Sanctions.S : Set ℝ) → ℝ :=
  fun x => Sanctions.clipS ((9 / 8) * x.val - 1 / 12)

/-- The explicit affine-clip rule IS the P3 static Sender best response at
leader action `0`: `p3RealizedRule x = mwσ x 0`, whose optimality certificate
is `mwσ_isMaxOn` (it maximizes `mwU_S x 0` on `[0,1]`). -/
theorem p3RealizedRule_eq_mwσ_zero (x : ↥(Sanctions.S : Set ℝ)) :
    p3RealizedRule x = mwσ x.val 0 := by
  unfold p3RealizedRule mwσ Sanctions.clipS
  norm_num

theorem p3RealizedRule_continuous : Continuous p3RealizedRule := by
  unfold p3RealizedRule
  exact Sanctions.clipS_continuous.comp (by fun_prop)

/-- The **P3 closed-loop drift** at the myopic realized rule:
`g(x) = F(x, clip((9/8)x − 1/12)) = (4/5)·x + (1/5)·clip((9/8)x − 1/12)`
(the P3 transition is `affineF (1/5)`). Genuinely state-dependent: not of
the constant-sanction box form. -/
noncomputable def p3ClosedLoopDrift : ↥(Sanctions.S : Set ℝ) → ℝ :=
  fun x => mechanismWitnessParams.F x.val (p3RealizedRule x)

theorem p3ClosedLoopDrift_continuous : Continuous p3ClosedLoopDrift :=
  mechanismWitnessParams.F_continuous.comp
    (continuous_subtype_val.prodMk p3RealizedRule_continuous)

/-- **Non-vacuity of the closed-loop engine at a genuinely state-dependent
drift**: the P3 box-noise chain driven by the explicit myopic realized rule
`clip((9/8)x − 1/12)` has an invariant probability law, for every noise
half-width `h > 0`. (Uniqueness is exactly what the dualKR route cannot
deliver here: `p3ClosedLoopDrift_lipConst_ge` below shows the drift has no
Lipschitz constant below `41/40`.) -/
theorem p3_closedLoop_exists_invariant (h : ℝ) (hh : 0 < h) :
    ∃ μ : Measure ↥(Sanctions.S : Set ℝ),
      IsProbabilityMeasure μ ∧ closedLoopBoxTransfer p3ClosedLoopDrift h μ = μ :=
  closedLoopBoxTransfer_exists_invariant p3ClosedLoopDrift
    p3ClosedLoopDrift_continuous h hh

/-- The rule is genuinely state-dependent: it takes distinct values at the
states `1/2` and `1` (`23/48` vs `1`). -/
example :
    p3RealizedRule ⟨1 / 2, by norm_num [Sanctions.S, Sanctions.I]⟩ = 23 / 48 ∧
    p3RealizedRule ⟨1, by norm_num [Sanctions.S, Sanctions.I]⟩ = 1 := by
  constructor <;> · unfold p3RealizedRule Sanctions.clipS; norm_num

/-! ## The honest uniqueness boundary -/

/-- **The affine estimate cannot open the dualKR uniqueness route at the
strong-rally witness slope (the arithmetic).** At the witness realized-sanction
slope `L_s = 9/8` (the myopic
frontier value shared by the P3 and low-δ economies; the dynamic slopes are
measured LARGER, so the violation is a fortiori), the closed-loop drift
Lipschitz factor under the affine transition is **exactly**
`(1−δ) + δ·(9/8) = 1 + δ/8`, which exceeds `1` for every `δ > 0` — so this
estimate cannot deliver the `L_g < 1` hypothesis of
`closedLoopBoxTransfer_unique_invariant` /
`closedLoopBoxTransfer_existsUnique_invariant_attracting`, with exact deficit
`δ/8`. This is the same `27/20` vs `6/5` frontier that refuted the
distributional concept (register: Wave-4 declinations): the violating rally
cross-partial is the paper's mechanism term, so this is a permanent
obstruction at the mechanism-active family, not a tuning problem. Existence
of the endogenous invariant law stands (`equilibrium_closedLoop_exists_invariant`);
its uniqueness/attraction is honestly open.

Scope (round BH-2, item BH2.11): this statement is arithmetic about the affine
estimate `(1−δ) + δ·L_s`; it does not by itself show that the drift fails the
Lipschitz bound. The refutation of the bound itself is
`affineP3ClosedLoopDrift_lipConst_ge` and `p3ClosedLoopDrift_lipConst_ge` below,
through the general-`F` lemma `closedLoop_lipConst_ge_of_diagonal_crossing`. -/
theorem closedLoop_dualKR_route_blocked {δ : ℝ} (hδ0 : 0 < δ) :
    ((1 - δ) + δ * (9 / 8) = 1 + δ / 8)
      ∧ (1 < (1 - δ) + δ * (9 / 8))
      ∧ ¬((1 - δ) + δ * (9 / 8) < 1) :=
  ⟨by ring, by linarith, fun hcon => absurd hcon (by linarith)⟩

/-- Exact factor values at the two witness economies: `41/40` at the P3
discount `δ = 1/5` and `801/800` at the low-δ window `δ = 1/100` — both
strictly above the contraction frontier `1`. -/
example : ((1 : ℝ) - 1 / 5) + (1 / 5) * (9 / 8) = 41 / 40 := by norm_num
example : ((1 : ℝ) - 1 / 100) + (1 / 100) * (9 / 8) = 801 / 800 := by norm_num
example : (1 : ℝ) < 41 / 40 ∧ (1 : ℝ) < 801 / 800 := by norm_num

/-- **At the P3 rule, the affine closed loop genuinely fails the contraction
hypothesis.** Affine-restricted (a witness-level certificate: the transition is
`affineF δ` and the rule is the explicit P3 rule `clip((9/8)x − 1/12)`). For
every `δ ≥ 0`, every Lipschitz constant `L` of the drift
`x ↦ affineF δ x (p3RealizedRule x)` on `↥S` satisfies `1 + δ/8 ≤ L`. The rule
crosses the diagonal at `x* = 2/3` and lies above it at excess slope `1/8` (here
at `y = 5/6`), and the affine law fixes the diagonal with sanction chord `δ`, so
the general-`F` lemma `closedLoop_lipConst_ge_of_diagonal_crossing` applies.
This turns `closedLoop_dualKR_route_blocked` from arithmetic into a refutation
of the bound `hgL`: the `L < 1` route of
`closedLoopBoxTransfer_existsUnique_invariant_attracting` is closed at this rule
under every affine transition `affineF δ`, `δ ≥ 0`, including `affineF (1/5)`
(P3) and `affineF (1/100)` (low-δ); other rules are not covered. -/
theorem affineP3ClosedLoopDrift_lipConst_ge {δ L : ℝ} (hδ0 : 0 ≤ δ)
    (hgL : ∀ x y : ↥(Sanctions.S : Set ℝ),
      |AbstractGame.affineF δ x.val (p3RealizedRule x)
        - AbstractGame.affineF δ y.val (p3RealizedRule y)| ≤ L * dist x y) :
    1 + δ / 8 ≤ L := by
  have hchord : TransitionChords.SanctionLowerChord (AbstractGame.affineF δ) δ := by
    intro x s₁ s₂ _ _ _ _
    unfold AbstractGame.affineF
    linarith
  have h := closedLoop_lipConst_ge_of_diagonal_crossing (F := AbstractGame.affineF δ)
    (R := p3RealizedRule) (d := δ) (k := 1 / 8)
    (xs := ⟨2 / 3, by norm_num [Sanctions.S, Sanctions.I]⟩)
    (y := ⟨5 / 6, by norm_num [Sanctions.S, Sanctions.I]⟩)
    (fun x _ => AbstractGame.affineF_diag δ x) hδ0 hchord (by norm_num) (by norm_num)
    (by unfold p3RealizedRule Sanctions.clipS; norm_num)
    (by unfold p3RealizedRule Sanctions.clipS; norm_num)
    (by unfold p3RealizedRule Sanctions.clipS; norm_num) hgL
  linarith

/-- **The P3 closed-loop drift has no Lipschitz constant below `41/40`.**
Affine-restricted (the P3 transition is `affineF (1/5)`): the `δ = 1/5` instance
of `affineP3ClosedLoopDrift_lipConst_ge`. So the conditional uniqueness route
provably cannot apply to the non-vacuity chain of
`p3_closedLoop_exists_invariant`; only its existence half does. -/
theorem p3ClosedLoopDrift_lipConst_ge {L : ℝ}
    (hgL : ∀ x y : ↥(Sanctions.S : Set ℝ),
      |p3ClosedLoopDrift x - p3ClosedLoopDrift y| ≤ L * dist x y) :
    41 / 40 ≤ L := by
  have h := affineP3ClosedLoopDrift_lipConst_ge (δ := 1 / 5) (by norm_num) hgL
  linarith

end

end Examples
end Sanctions
