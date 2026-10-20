/-
Sanctions/Theory/Bellman/C1BellmanSystem.lean

**iter 21 (audit-37 Step 4): `C1BellmanSystem` — tying the C¹ Bellman
operator to the BCF Bellman operators.**

**PARTIALLY UNFROZEN (2026-07-12; supersedes the 2026-07-04 A6 freeze
for the witness layer only).** The *witness* layer now carries
paper-facing load: `Examples/C1WitnessEnvelope.lean` inhabits `C1Val`,
`ValueClass_C1`, `ValueClass_C1Complete` and `C1BellmanSystem` at the
two pinned exact Bellman fixed points (eeCert, fourGroup), and the
paper's shadow-price passage cites the resulting equilibrium slopes.
At those witnesses the completeness field is *proved*
(`eeC1Class_complete` / `fgcC1Class_complete` — a singleton carrier is
trivially complete) and `T = id`, so the `c1distPair`-fixed point is a
genuine fixed point: no assumed-completeness postulate and no
pseudo-metric artefact enters any shipped result. No headline row
fences the C¹ layer.

The *abstract* layer STAYS FROZEN: each general form (the
`SmoothSanctionClass` IFT Prop fields, an abstract
`ValueClass_C1Complete` derivation, general-`F` RZS-style statements)
would need new differentiability hypotheses (Rule 3). Both structural
deficiencies persist at abstract generality: `c1distPair` is a
pseudo-metric (`V'` stored on all of `ℝ`), and completeness
(`ValueClass_C1Complete`) is consumed per-certificate, not derived. Revival order if ever needed: (1) the within-set
uniform-limits-of-derivatives theorem (a mathlib gap, not an analytic
one — `Foundations/` candidate), (2) the `V'`-domain refactor,
(3) asymmetric duplication only once a consumer exists.

The audit-37 critique observes that `ValueClass_C1` (iter 17) takes
the joint Bellman operator `T : carrier → carrier` as an
*unconstrained* parametric field. To prevent the user from supplying
an arbitrary T (which would break Rule 1 — strategies must be
equilibrium-derived), this iter adds a structure that *constrains* T
to be the C¹ analog of the BCF joint Bellman maps:

* The BCF projection of `(T z).val.1` equals the BCF joint Target
  Bellman value `sSup (joint_T_top_integrand z.val.1.V z.val.2.V x ·)`.
* The BCF projection of `(T z).val.2` equals the BCF Sender Bellman
  value `bellmanS_BCF (α_on_C1 z.val.1 z.val.2) (α_cont) z.val.2.V`.
* `α_on_C1 V_T V_S x` is a continuous leader joint-Bellman argmax
  (a.k.a. `α_opt_top`-equivalent on `Sanctions.S`).

With these constraints, the `c1distPair`-fixed point of T (existence
from iter 20 under completeness) projects to a legitimate
`FeedbackStackelbergEquilibriumTop` via the lift theorem
`C1BellmanSystem.feedbackStackelbergEquilibriumTop_of_c1distPair_fixedPoint`.

This is the audit's recommended "true C¹-to-BCF lift" — replacing the
opaque extraction primitive with a theorem.

## P9 partial unfreeze (2026-07-12) — Rule-13 statement-change disclosure

**Cat-(2) carrier-localization of the three α-side Prop fields.**
`α_cont` / `α_mem` / `α_isMaxOn` previously quantified over ALL pairs
`V_T V_S : C1Val K_d`; they now quantify over `z : carrier`
(evaluating `α_on_C1` at `z.val.1`, `z.val.2`). Precedent: audit-49
Item 5 (`StandardComplianceLocalCertificateC1`, whose own fields are
already carrier-local on `D_C1.carrier`).

*Justification.* The lift theorem
`feedbackStackelbergEquilibriumTop_of_c1distPair_fixedPoint` consumes
the three fields only at the produced fixed point `z`, so the
localized form is exactly what the construction uses; the previous
∀-pairs form imposed obligations on `α_on_C1` at value pairs never
visited by any theorem — a strictly wider requirement on suppliers of
the structure than any consumer needs.

*Consumers verified before the change (2026-07-12).*
`Legacy/JETBridgeC1System.lean` consumes only the lift / existence
theorems, whose signatures are unchanged;
`Certificates/StandardComplianceLocalC1.lean` applies the α fields
only at the produced `z` (its proof body adapts the applications
`z.val.1 z.val.2 ↦ z` mechanically; no statement changes). No other
consumer exists. The change *weakens* the obligations on suppliers of
`C1BellmanSystem` (fewer requirements — a pure Cat-2 weakening on the
supplier side) and weakens no downstream theorem: every theorem
consuming the structure retains its exact statement.

## Rule compliance

**Rule 1.** The lift theorem's output equilibrium uses
equilibrium-derived strategies (the leader policy is `α_on_C1`, a
joint-Bellman argmax field; the Sender response is `σ_dyn_top`
through `bellmanS_BCF` Bellman fixed point).

**Rule 3.** `C1BellmanSystem` extends `ValueClass_C1` with structural
constraints that *tighten* the parametric T (no broader assumption
surface). Categorically a refinement of iter 17, not a new primitive.

**Rule 5.** Fully parametric.
-/

import Sanctions.Theory.Bellman.ValueClassC1
import Sanctions.Theory.Basin.JointPreferenceBasin

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame

/-- **C¹ Bellman system.** Extends `ValueClass_C1` with structural
constraints linking the parametric C¹ joint Bellman operator `T` to
the BCF joint Target Bellman value (`joint_T_top_integrand`'s sSup) +
the BCF Sender Bellman value (`bellmanS_BCF`).

Adds:
* `α_on_C1` — a leader joint-Bellman argmax field, continuous in `x`.
* `α_isMaxOn` — `α_on_C1` is the joint Target argmax.
* `T_value_eq_target` — the BCF projection of the Target component of
  `T z` equals the BCF Bellman value at `(z.val.1.V, z.val.2.V)`.
* `T_value_eq_sender` — the BCF projection of the Sender component of
  `T z` equals `bellmanS_BCF (α_on_C1 z.1 z.2) z.val.2.V`. -/
structure C1BellmanSystem (p : AbstractGame.Params) (K_d : ℝ)
    extends ValueClass_C1 K_d where
  /-- Leader joint-Bellman argmax field. -/
  α_on_C1 : C1Val K_d → C1Val K_d → ℝ → ℝ
  /-- α is continuous (required for `bellmanS_BCF` compatibility).
  Carrier-localized (P9 unfreeze, 2026-07-12): quantified over
  `z : carrier` rather than over all `C1Val` pairs. -/
  α_cont : ∀ z : carrier, Continuous (α_on_C1 z.val.1 z.val.2)
  /-- α is feasible at feasible states (carrier-localized). -/
  α_mem :
    ∀ z : carrier, ∀ x ∈ Sanctions.S,
      α_on_C1 z.val.1 z.val.2 x ∈ Sanctions.I
  /-- α attains the joint Target argmax on `Sanctions.S`
  (carrier-localized). -/
  α_isMaxOn :
    ∀ z : carrier, ∀ x ∈ Sanctions.S,
      IsMaxOn
        (fun a => p.joint_T_top_integrand z.val.1.V z.val.2.V x a)
        Sanctions.I
        (α_on_C1 z.val.1 z.val.2 x)
  /-- The Target component of `T z` (after BCF projection) equals the
  BCF joint Target Bellman value. -/
  T_value_eq_target :
    ∀ z : carrier, ∀ x : ↥(Sanctions.S : Set ℝ),
      (T z).val.1.V x =
        sSup ((fun a => p.joint_T_top_integrand z.val.1.V z.val.2.V x.val a)
                '' Sanctions.I)
  /-- The Sender component of `T z` (after BCF projection) equals the
  BCF Sender Bellman value applied to `α_on_C1 z.1 z.2`. -/
  T_value_eq_sender :
    ∀ z : carrier,
      (T z).val.2.V =
        p.bellmanS_BCF (α_on_C1 z.val.1 z.val.2)
          (α_cont z) z.val.2.V

namespace C1BellmanSystem

variable {p : AbstractGame.Params} {K_d : ℝ}

/-! ## c1distPair = 0 ⇒ BCF value equality

`c1distPair (T z).val z.val = 0` decomposes as `dist V_1 V_1' = 0` +
`sSup_S |V_1.V' - V_1'.V'| = 0` + the same for the Sender side.
The BCF dist = 0 gives literal BCF equality. -/

/-- **BCF projection of c1distPair = 0**: if `c1distPair a b = 0`,
the BCF values of both components are equal. -/
theorem bcf_eq_of_c1distPair_zero (hK_d_nn : 0 ≤ K_d)
    {a b : C1Val K_d × C1Val K_d}
    (h : C1Val.c1distPair a b = 0) :
    a.1.V = b.1.V ∧ a.2.V = b.2.V := by
  -- c1distPair a b = c1dist a.1 b.1 + c1dist a.2 b.2 = 0
  have h_unfold : C1Val.c1dist a.1 b.1 + C1Val.c1dist a.2 b.2 = 0 := h
  have h1_nn : 0 ≤ C1Val.c1dist a.1 b.1 := C1Val.c1dist_nonneg hK_d_nn _ _
  have h2_nn : 0 ≤ C1Val.c1dist a.2 b.2 := C1Val.c1dist_nonneg hK_d_nn _ _
  have h1_zero : C1Val.c1dist a.1 b.1 = 0 := by linarith
  have h2_zero : C1Val.c1dist a.2 b.2 = 0 := by linarith
  -- c1dist = BCF dist + sSup-on-S deriv diff; both ≥ 0; both = 0.
  have h1_bcf_nn : (0 : ℝ) ≤ dist a.1.V b.1.V := _root_.dist_nonneg
  have h1_sup_nn : 0 ≤
      sSup ((fun x => |a.1.V' x - b.1.V' x|) '' Sanctions.S) := by
    apply le_csSup_of_le
      (C1Val.deriv_diff_image_bddAbove hK_d_nn a.1 b.1)
      ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
    exact abs_nonneg _
  have h1_bcf_zero : dist a.1.V b.1.V = 0 := by
    have : dist a.1.V b.1.V +
        sSup ((fun x => |a.1.V' x - b.1.V' x|) '' Sanctions.S) = 0 := h1_zero
    linarith
  have h2_bcf_nn : (0 : ℝ) ≤ dist a.2.V b.2.V := _root_.dist_nonneg
  have h2_sup_nn : 0 ≤
      sSup ((fun x => |a.2.V' x - b.2.V' x|) '' Sanctions.S) := by
    apply le_csSup_of_le
      (C1Val.deriv_diff_image_bddAbove hK_d_nn a.2 b.2)
      ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
    exact abs_nonneg _
  have h2_bcf_zero : dist a.2.V b.2.V = 0 := by
    have : dist a.2.V b.2.V +
        sSup ((fun x => |a.2.V' x - b.2.V' x|) '' Sanctions.S) = 0 := h2_zero
    linarith
  exact ⟨(dist_eq_zero.mp h1_bcf_zero), (dist_eq_zero.mp h2_bcf_zero)⟩

/-! ## C¹-to-BCF lift: `FeedbackStackelbergEquilibriumTop` from a
`c1distPair`-fixed point -/

/-- **The audit-37 "true C¹-to-BCF lift".** From a `c1distPair`-fixed
point `z` of `D.T` in `D.carrier`, construct a
`FeedbackStackelbergEquilibriumTop` for `p`. Data-bearing definition
(not a Prop): the produced equilibrium structure's fields are derived
from `z`, `D.α_on_C1`, and `D.α_cont`. -/
noncomputable def feedbackStackelbergEquilibriumTop_of_c1distPair_fixedPoint
    (hK_d_nn : 0 ≤ K_d)
    (D : C1BellmanSystem p K_d) (z : D.carrier)
    (hfix : C1Val.c1distPair (D.T z).val z.val = 0) :
    p.FeedbackStackelbergEquilibriumTop := by
  -- Extract BCF value equality from the c1distPair-fixed-point condition.
  obtain ⟨hVT_eq, hVS_eq⟩ := bcf_eq_of_c1distPair_zero hK_d_nn hfix
  -- BCF Target value V_T : ↥S →ᵇ ℝ.
  let V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ := z.val.1.V
  let V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ := z.val.2.V
  let α : ℝ → ℝ := D.α_on_C1 z.val.1 z.val.2
  -- All FeedbackStackelbergEquilibriumTop fields.
  refine
    { V_T := V_T
      V_S := V_S
      α := α
      hα := D.α_cont z
      α_mem := ?_
      V_S_fix := ?_
      V_T_fix_top := ?_
      α_opt_top := ?_ }
  · -- α_mem : ∀ x ∈ S, α x ∈ I
    intro x hx
    exact D.α_mem z x hx
  · -- V_S_fix : V_S = bellmanS_BCF α hα V_S
    -- From T_value_eq_sender: (T z).val.2.V = bellmanS_BCF α hα V_S.
    -- From hVS_eq: (T z).val.2.V = V_S.
    show V_S = p.bellmanS_BCF α (D.α_cont z) V_S
    have h_T_sender :
        (D.T z).val.2.V =
          p.bellmanS_BCF α (D.α_cont z) V_S :=
      D.T_value_eq_sender z
    -- Combine: V_S = (T z).val.2.V (from hVS_eq.symm) = bellmanS_BCF α hα V_S.
    rw [← h_T_sender, hVS_eq]
  · -- V_T_fix_top : ∀ x : ↥S, V_T x = sSup (joint_T_top_integrand V_T V_S x ·)
    intro x
    -- From T_value_eq_target: (T z).val.1.V x = sSup (...)
    have h_T_target := D.T_value_eq_target z x
    -- From hVT_eq: V_T x = (T z).val.1.V x.
    have h_apply : (D.T z).val.1.V x = V_T x := by rw [hVT_eq]
    rw [← h_apply]; exact h_T_target
  · -- α_opt_top : ∀ x ∈ S, IsMaxOn (joint_T_top_integrand V_T V_S x ·) I (α x)
    intro x hx
    exact D.α_isMaxOn z x hx

/-- **Convenience corollary**: existence of `FeedbackStackelbergEquilibriumTop`
from a `C1BellmanSystem` + completeness. Combines iter 20
(`exists_c1distPair_fixedPoint`) with the iter-21 lift. -/
theorem feedbackStackelbergEquilibriumTop_of_complete
    (hK_d_nn : 0 ≤ K_d)
    (D : C1BellmanSystem p K_d)
    (hComplete : ValueClass_C1Complete D.toValueClass_C1) :
    Nonempty p.FeedbackStackelbergEquilibriumTop := by
  obtain ⟨z, hfix⟩ :=
    D.toValueClass_C1.exists_c1distPair_fixedPoint hK_d_nn hComplete
  exact ⟨D.feedbackStackelbergEquilibriumTop_of_c1distPair_fixedPoint
          hK_d_nn z hfix⟩

end C1BellmanSystem

end AbstractGame

end -- noncomputable section

end Sanctions
