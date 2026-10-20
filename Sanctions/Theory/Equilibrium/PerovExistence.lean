/-
Sanctions/Theory/Equilibrium/PerovExistence.lean

**Round E1: Schur-margin (Perov) existence on the heterogeneous
carrier — row-sum conditions retired at the existence layer.**

The legacy heterogeneous Banach step
(`ValueClass2.exists_fixedPoint_in_carrier`) consumes the row-sum
conditions `β_T + L_TS < 1` and `β_S + L_ST < 1`. This file provides
the strictly-weaker **Schur-margin** versions: the two diagonal row
coefficients `β_T, β_S` of the operator bounds — free reals in the
theorem statements, equal to the `Params` discounts only in the
canonical instantiation `β := p.β_*`, where `β_* < 1` is
`Params.β_*_mem` — with `β_T < 1`, `β_S < 1`, plus

  `L_TS · L_ST < (1 − β_T) · (1 − β_S)`

are required. Since round BJ1.1 (2026-10-07) the three existence and
uniqueness roots carry no sign condition on the four coefficients: a negative
coefficient forces a carrier to be a single point, and the Perov step handles
that case itself. With the signs, the Target bound `β_T < 1` would follow from
the rest (`Foundations.Perov.lt_one_of_schur_margin`, round BG1.1); without
them it is needed, and dropping both is false.
Substituting the discounts in one application does not
make them the definition of the coefficients in every certificate. The engine is the Foundations Perov 2×2 fixed point
(`Sanctions.Foundations.Perov.perov2_existsUnique_fixedPoint`): the
Schur margin produces explicit Perron weights under which the joint
subtype operator is a single-modulus contraction in the weighted max
metric, and an elementary geometric iteration delivers the fixed
point — entirely on the asymmetric subtype carrier, with no rescaling
out of the carrier (the obstruction that blocked the ambient-space
weighted trick in Round 2.1).

Literature: Perov 1964 via Toda 2021/2023; weighted-max-norm
reduction per Bertsekas-Tsitsiklis (NDP §2); identified as the
canonical refactor by the 2026-06-11 enhancement sweep (T9).

## Rule compliance

**Rule 3** ✓ — no new assumption surface: the Schur margin is weaker
than the row sums it replaces; the diagonal bounds `β_* < 1` are on
free operator-row coefficients and restate `Params.β_*_mem` at the
canonical instantiation. **Rule 5** ✓ — fully parametric. **Rule 13** ✓ —
since round BG1.2 (2026-10-06) the Schur fixed point
`ValueClass2.exists_fixedPoint_in_carrier_schur` lives in
`Theory/Bellman/InvariantValueClass2.lean` (same name), the row-sum theorems
there are its corollaries, and the equilibrium construction is the single
`ValueClass2.exists_feedbackStackelbergTop_of_jointFixedPoint`; every
statement in this file is unchanged. **Rule 19** ✓ — the generic fixed-point
content lives in `Foundations/PerovContraction.lean`; this file is
Params-level wiring. **Rule 22** ✓ — general in `F`: the transition enters only
through the Bellman operators of `p`.
-/

import Sanctions.Theory.Bellman.InvariantValueClass2
import Sanctions.Foundations.PerovContraction
import Sanctions.Theory.Equilibrium.CertifiedEquilibria

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params
namespace ValueClass2

variable {p : Sanctions.AbstractGame.Params} (D : p.ValueClass2)

/-! The Schur-margin fixed point `exists_fixedPoint_in_carrier_schur` moved to
`Theory/Bellman/InvariantValueClass2.lean` under the same name (round BG1.2,
2026-10-06), so that the row-sum existence theorem there is its corollary
without an import cycle. Its first diagonal bound `β_T < 1` was dropped in the
same move (round BG1.1): the signs, `β_S < 1` and the Schur margin imply it.

### Sign-free Perov step (round BJ1.1, 2026-10-07)

The three thm:existence roots below (census rows 30, 31 and 79) no longer
assume that the four operator-row coefficients `β_T, β_S, L_TS, L_ST` are
non-negative. A negative coefficient is not an economic restriction to be
ruled out: it can only occur when one carrier is a single point. If `β_T < 0`
or `L_ST < 0`, the row bound at a fixed Sender value (`W = W'`) reads
`0 ≤ dist ≤ (negative) · dist V V'`, which forces `V = V'`, so the Target
carrier is a subsingleton; symmetrically, `L_TS < 0` or `β_S < 0` makes the
Sender carrier a subsingleton. On a subsingleton carrier the row bounds hold
again with non-negative coefficients (`0` on the collapsed row, `max β 0` on
the other diagonal), and the Perov engine applies unchanged. In exchange both
diagonal bounds `β_T < 1` and `β_S < 1` are assumed: without the signs the
Target bound no longer follows from the Schur margin, and dropping both the
signs and `β_T < 1` is false. -/

/-! ## Uniqueness within the carrier (Round R-UNIQ)

The Perov engine `perov2_existsUnique_fixedPoint` delivers `∃!`, but the
existence theorems above discard the uniqueness half. The three results
below surface it at the equilibrium level: within the carrier value
class, the joint Bellman fixed point is unique, any top-selector
feedback Stackelberg equilibrium with carrier values and selector
coincidence IS that fixed point, and hence any two such equilibria
coincide — value functions and policy alike. This is the machine-checked
form of the paper's "uniqueness holds within the carrier value class"
claim: the equilibrium is pinned uniquely within the chosen carrier and
selector class. This theorem makes no global equilibrium-uniqueness
claim. The project's bistability results concern state-path selection
under a single equilibrium and neither establish nor refute multiple
equilibria. No new assumptions: the hypotheses are identical to the
existence theorem's. -/

/-- **Schur-margin fixed-point uniqueness on the heterogeneous carrier.**
The `∃!` form of the Perov step: under the row-Lipschitz estimates, both
diagonal bounds and the Schur margin, the joint subtype operator has exactly
one fixed point in `carrier_T × carrier_S`.

Round BJ1.1 (2026-10-07, author-approved re-pin of evidence row 907 and census
row 31): the four sign binders `0 ≤ β_T`, `0 ≤ β_S`, `0 ≤ L_TS`, `0 ≤ L_ST`
are dropped. When a coefficient is negative the corresponding carrier is a
single point and the row bounds are re-stated with non-negative coefficients
before the Perov engine is called (see the section note above). The Target
diagonal bound `hβ_T_lt` is read again: in the case where the Sender carrier
collapses, the Target row alone must contract.

Plain language: within the carrier class there is exactly one joint Bellman
fixed point, and the coefficients in the operator bounds need not be
non-negative for this. General in `F`: the transition enters only through the
Bellman operators of `p`. -/
theorem existsUnique_fixedPoint_in_carrier_schur
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hβ_T_lt : β_T < 1) (hβ_S_lt : β_S < 1)
    (hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S)) :
    ∃! z : D.CarrierT × D.CarrierS,
      (D.jointTargetOp_sub h_inv z, D.jointSenderOp_sub h_inv z) = z := by
  haveI : CompleteSpace D.CarrierT := D.isClosed_T.completeSpace_coe
  haveI : CompleteSpace D.CarrierS := D.isClosed_S.completeSpace_coe
  haveI : Nonempty D.CarrierT := D.nonempty_T.to_subtype
  haveI : Nonempty D.CarrierS := D.nonempty_S.to_subtype
  -- Re-state the two row bounds with non-negative coefficients.
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hX, hY, hd_lt, hS⟩ :
      ∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
        (∀ z z' : D.CarrierT × D.CarrierS,
          dist (D.jointTargetOp_sub h_inv z) (D.jointTargetOp_sub h_inv z')
            ≤ a * dist z.1 z'.1 + b * dist z.2 z'.2) ∧
        (∀ z z' : D.CarrierT × D.CarrierS,
          dist (D.jointSenderOp_sub h_inv z) (D.jointSenderOp_sub h_inv z')
            ≤ c * dist z.1 z'.1 + d * dist z.2 z'.2) ∧
        d < 1 ∧ b * c < (1 - a) * (1 - d) := by
    by_cases hTneg : β_T < 0 ∨ L_ST < 0
    · -- A negative Target-column coefficient: the Target carrier is a point.
      obtain ⟨W₀⟩ := (inferInstance : Nonempty D.CarrierS)
      have hsubT : ∀ V V' : D.CarrierT, V = V' := by
        intro V V'
        apply dist_le_zero.mp
        have hVV := dist_nonneg (x := V) (y := V')
        rcases hTneg with h | h
        · have h1 := hT_T V V' W₀ W₀
          rw [dist_self, mul_zero, add_zero] at h1
          nlinarith [dist_nonneg (x := D.jointTargetOp_sub h_inv (V, W₀))
            (y := D.jointTargetOp_sub h_inv (V', W₀))]
        · have h1 := hT_S V V' W₀ W₀
          rw [dist_self, mul_zero, add_zero] at h1
          nlinarith [dist_nonneg (x := D.jointSenderOp_sub h_inv (V, W₀))
            (y := D.jointSenderOp_sub h_inv (V', W₀))]
      have hdlt : max β_S 0 < 1 := max_lt hβ_S_lt one_pos
      refine ⟨0, 0, 0, max β_S 0, le_rfl, le_rfl, le_rfl, le_max_right _ _,
        ?_, ?_, hdlt, by linarith⟩
      · intro z z'
        rw [hsubT (D.jointTargetOp_sub h_inv z) (D.jointTargetOp_sub h_inv z'),
          dist_self]
        simp
      · rintro ⟨V, W⟩ ⟨V', W'⟩
        obtain rfl := hsubT V V'
        have h1 := hT_S V V W W'
        rw [dist_self, mul_zero, zero_add] at h1
        simp only [dist_self, mul_zero, zero_add]
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
    · obtain ⟨hβT, hLST⟩ := not_or.mp hTneg
      by_cases hSneg : L_TS < 0 ∨ β_S < 0
      · -- A negative Sender-column coefficient: the Sender carrier is a point.
        obtain ⟨V₀⟩ := (inferInstance : Nonempty D.CarrierT)
        have hsubS : ∀ W W' : D.CarrierS, W = W' := by
          intro W W'
          apply dist_le_zero.mp
          have hWW := dist_nonneg (x := W) (y := W')
          rcases hSneg with h | h
          · have h1 := hT_T V₀ V₀ W W'
            rw [dist_self, mul_zero, zero_add] at h1
            nlinarith [dist_nonneg (x := D.jointTargetOp_sub h_inv (V₀, W))
              (y := D.jointTargetOp_sub h_inv (V₀, W'))]
          · have h1 := hT_S V₀ V₀ W W'
            rw [dist_self, mul_zero, zero_add] at h1
            nlinarith [dist_nonneg (x := D.jointSenderOp_sub h_inv (V₀, W))
              (y := D.jointSenderOp_sub h_inv (V₀, W'))]
        have halt : max β_T 0 < 1 := max_lt hβ_T_lt one_pos
        refine ⟨max β_T 0, 0, 0, 0, le_max_right _ _, le_rfl, le_rfl, le_rfl,
          ?_, ?_, one_pos, by linarith⟩
        · rintro ⟨V, W⟩ ⟨V', W'⟩
          obtain rfl := hsubS W W'
          have h1 := hT_T V V' W W
          rw [dist_self, mul_zero, add_zero] at h1
          simp only [dist_self, mul_zero, add_zero]
          exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
        · intro z z'
          rw [hsubS (D.jointSenderOp_sub h_inv z) (D.jointSenderOp_sub h_inv z'),
            dist_self]
          simp
      · -- All four coefficients are non-negative: the bounds as given.
        obtain ⟨hLTS, hβS⟩ := not_or.mp hSneg
        exact ⟨β_T, L_TS, L_ST, β_S, not_lt.mp hβT, not_lt.mp hLTS, not_lt.mp hLST,
          not_lt.mp hβS,
          fun z z' => hT_T z.1 z'.1 z.2 z'.2, fun z z' => hT_S z.1 z'.1 z.2 z'.2,
          hβ_S_lt, hSchur⟩
  exact Sanctions.Foundations.Perov.perov2_existsUnique_fixedPoint
    (T := fun z : D.CarrierT × D.CarrierS =>
      (D.jointTargetOp_sub h_inv z, D.jointSenderOp_sub h_inv z))
    ha hb hc hd hX hY hd_lt hS

/-- **Schur-margin top-selector equilibrium existence with carrier
membership (Round E1).** Identical conclusion to
`exists_feedbackStackelbergTop_from_valueClass2_with_membership`
(a top-selector feedback Stackelberg equilibrium whose value pair
lies in the carriers, with α-coincidence), under the Schur margin in
place of the row sums.

A two-line corollary: the existence half of the sign-free Perov step
`existsUnique_fixedPoint_in_carrier_schur` fed to the single construction
`exists_feedbackStackelbergTop_of_jointFixedPoint`.

Round BJ1.1 (2026-10-07, author-approved re-pin of evidence row 906 and census
row 30): the four sign binders on the operator-row coefficients are dropped,
and the Target diagonal bound `hβ_T_lt` (unused since round BG1.1) is read
again, because without the signs it no longer follows from the Schur margin.
A negative coefficient only occurs when a carrier is a single point, and the
Perov step handles that case by itself.

Plain language: if the joint Bellman operator contracts in the Schur sense on
the two carriers, a top-selector feedback Stackelberg equilibrium exists with
values in the carriers and the carrier's compliance selector as its policy;
the coefficients need not be non-negative. General in `F`. -/
theorem exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hβ_T_lt : β_T < 1) (hβ_S_lt : β_S < 1)
    (hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S)) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop,
      ∃ hVT : E.V_T ∈ D.carrier_T,
      ∃ hVS : E.V_S ∈ D.carrier_S,
        E.α = D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩ :=
  D.exists_feedbackStackelbergTop_of_jointFixedPoint h_inv
    (D.existsUnique_fixedPoint_in_carrier_schur h_inv hT_T hT_S hβ_T_lt
      hβ_S_lt hSchur).exists

/-- **Every Bellman-consistent, selector-coincident carrier value pair is a
joint fixed point (parametric bridge).** Stated over exactly the consumed
data — a carrier value pair `(V_T, V_S)` with membership, a continuous
policy `α` coinciding with the carrier selector `α_on`, and the two Bellman
fixed-point equations (the Sender follower fixed point at `α`, the Target
top-selector fixed point) — with **no** leader-optimality or feasibility
input. So within-carrier uniqueness pins any Bellman-consistent,
selector-coincident carrier value pair, not only full equilibria. The
Sender half is the follower fixed-point condition at the coinciding
policy; the Target half converts the top-selector Bellman equation into
the ordinary joint operator via state-local Sender argmax uniqueness on
the carrier. -/
theorem fixedPoint_of_bellman_fixed_of_selector_coincidence
    (h_inv : D.IsInvariant)
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hVT : V_T ∈ D.carrier_T) (hVS : V_S ∈ D.carrier_S)
    {α : ℝ → ℝ} (hαc : Continuous α)
    (hα : α = D.α_on ⟨V_T, hVT⟩ ⟨V_S, hVS⟩)
    (V_S_fix : V_S = p.bellmanS_BCF α hαc V_S)
    (V_T_fix_top : ∀ x : ↥(Sanctions.S : Set ℝ),
      V_T x = sSup ((fun a => p.joint_T_top_integrand V_T V_S x.val a)
                      '' Sanctions.I)) :
    (D.jointTargetOp_sub h_inv (⟨V_T, hVT⟩, ⟨V_S, hVS⟩),
      D.jointSenderOp_sub h_inv (⟨V_T, hVT⟩, ⟨V_S, hVS⟩))
      = (⟨V_T, hVT⟩, ⟨V_S, hVS⟩) := by
  subst hα
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · -- Target component: the joint Target operator returns `V_T` itself.
    show p.jointTarget_BCF_on_S V_T V_S (D.sender_unique_on V_S hVS) = V_T
    ext x
    have h_apply :=
      p.jointTarget_BCF_on_S_apply V_T V_S (D.sender_unique_on V_S hVS) x
    -- On `S × I`, top integrand ≡ ordinary integrand (compliance-local
    -- uniqueness); the supremum reads them only on `I`.
    have hint :
        (fun a => p.joint_T_top_integrand V_T V_S x.val a) '' Sanctions.I =
          (fun a => p.joint_T_integrand V_T V_S x.val a) '' Sanctions.I :=
      Set.image_congr fun _a ha =>
        p.joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI
          (D.sender_unique_on V_S hVS) x.property ha
    calc (p.jointTarget_BCF_on_S V_T V_S (D.sender_unique_on V_S hVS)) x
        = sSup ((fun a => p.joint_T_integrand V_T V_S x.val a) ''
            Sanctions.I) := h_apply
      _ = sSup ((fun a => p.joint_T_top_integrand V_T V_S x.val a) ''
            Sanctions.I) := by rw [hint]
      _ = V_T x := (V_T_fix_top x).symm
  · -- Sender component: the follower fixed-point condition at the
    -- coinciding policy (continuity proofs agree by proof irrelevance).
    show p.bellmanS_BCF (D.α_on ⟨V_T, hVT⟩ ⟨V_S, hVS⟩)
      (D.α_on_continuous ⟨V_T, hVT⟩ ⟨V_S, hVS⟩) V_S = V_S
    exact V_S_fix.symm

/-- **Every carrier equilibrium is a joint fixed point.** A top-selector
feedback Stackelberg equilibrium whose value pair lies in the carriers
and whose policy coincides with the carrier selector `α_on` is a fixed
point of the joint subtype operator — the converse wiring of
`exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur`.
One-line corollary of the parametric bridge
`fixedPoint_of_bellman_fixed_of_selector_coincidence`, applied at the
equilibrium's own value pair, policy, and two Bellman fixed-point fields
— leader optimality `α_opt_top` and feasibility `α_mem` are not consumed
in this direction. -/
theorem fixedPoint_of_feedbackStackelbergTop_of_selector_coincidence
    (h_inv : D.IsInvariant)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ D.carrier_T) (hVS : E.V_S ∈ D.carrier_S)
    (hα : E.α = D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩) :
    (D.jointTargetOp_sub h_inv (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩),
      D.jointSenderOp_sub h_inv (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩))
      = (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩) :=
  D.fixedPoint_of_bellman_fixed_of_selector_coincidence h_inv hVT hVS
    E.hα hα E.V_S_fix E.V_T_fix_top

/-- **Schur-margin equilibrium uniqueness within the carrier class.**
Any two top-selector feedback Stackelberg equilibria whose value pairs
lie in the carriers and whose policies coincide with the carrier
selector agree in both value functions and in the policy. Combined with
`exists_feedbackStackelbergTop_from_valueClass2_with_membership_schur`,
this pins the equilibrium uniquely within the chosen carrier and
selector class. It makes no global equilibrium-uniqueness claim;
bistability concerns state-path selection under a single equilibrium.
The selector-coincidence binders `hαE`, `hαE'` are needed only for the
off-`S` part of `E.α = E'.α`; without them,
`feedbackStackelbergTop_unique_in_carrier_schur_of_mem` gives the same value
equalities and agreement of the policies on `S` (round BH1.1).

Round BJ1.1 (2026-10-07, author-approved change to census row 79): the four
sign binders on the operator-row coefficients are dropped, as in the sign-free
Perov step `existsUnique_fixedPoint_in_carrier_schur`; both diagonal bounds
stay. General in `F`. -/
theorem feedbackStackelbergTop_unique_in_carrier_schur
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hβ_T_lt : β_T < 1) (hβ_S_lt : β_S < 1)
    (hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S))
    (E E' : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ D.carrier_T) (hVS : E.V_S ∈ D.carrier_S)
    (hVT' : E'.V_T ∈ D.carrier_T) (hVS' : E'.V_S ∈ D.carrier_S)
    (hαE : E.α = D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = D.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α := by
  obtain ⟨z₀, _, huniq⟩ := D.existsUnique_fixedPoint_in_carrier_schur h_inv
    hT_T hT_S hβ_T_lt hβ_S_lt hSchur
  have h1 := huniq (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩)
    (D.fixedPoint_of_feedbackStackelbergTop_of_selector_coincidence
      h_inv E hVT hVS hαE)
  have h2 := huniq (⟨E'.V_T, hVT'⟩, ⟨E'.V_S, hVS'⟩)
    (D.fixedPoint_of_feedbackStackelbergTop_of_selector_coincidence
      h_inv E' hVT' hVS' hαE')
  have hpair := h1.trans h2.symm
  have hT : E.V_T = E'.V_T := congrArg (fun w => (Prod.fst w).val) hpair
  have hS : E.V_S = E'.V_S := congrArg (fun w => (Prod.snd w).val) hpair
  refine ⟨hT, hS, ?_⟩
  have e1 : (⟨E.V_T, hVT⟩ : D.CarrierT) = ⟨E'.V_T, hVT'⟩ := Subtype.ext hT
  have e2 : (⟨E.V_S, hVS⟩ : D.CarrierS) = ⟨E'.V_S, hVS'⟩ := Subtype.ext hS
  rw [hαE, hαE', e1, e2]

/-! ### Uniqueness without selector coincidence (round BH1.1, 2026-10-06)

The results above take the selector coincidence `E.α = D.α_on …` as a
hypothesis. On the state set it is not an assumption. An equilibrium whose two
values lie in the carriers already plays the carrier selector there: its policy
maximises the top integrand (`α_opt_top`), which on `S` is the ordinary joint
integrand because the Sender's argmax is unique on the Sender carrier
(`sender_unique_on`), and the Target's argmax is unique on the carrier pair
(`target_unique_on`), so the two maximisers coincide. Off `S` the policy is
never evaluated by the clamped dynamics and is not pinned, so the siblings below
conclude equality of policies on `S` rather than as functions on `ℝ`. The old
forms stay: each is its sibling plus the off-`S` coincidence, which is what
their `hαE` is still read for. -/

/-- **Every carrier equilibrium plays the carrier selector on the state set
(round BH1.1).** If the two value functions of a top-selector feedback
Stackelberg equilibrium lie in the carriers, its policy agrees with the carrier
selector `α_on` at every feasible state. No selector-coincidence hypothesis:
leader optimality (`α_opt_top`) and feasibility (`α_mem`) of the policy, the
Sender's argmax uniqueness on the Sender carrier and the Target's argmax
uniqueness on the carrier pair force it.

Plain language: once the values are in the carriers, the Target's compliance
choice at every reachable political state is the one the carrier selects; it is
an equilibrium property, not an extra assumption. General in `F`. -/
theorem α_eqOn_α_on_of_feedbackStackelbergTop
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ D.carrier_T) (hVS : E.V_S ∈ D.carrier_S) :
    Set.EqOn E.α (D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩) Sanctions.S := by
  intro x hx
  -- On `S` the top integrand is the ordinary one (state-local Sender uniqueness),
  -- so the equilibrium policy maximises the ordinary joint integrand.
  have hmax : IsMaxOn (fun a => p.joint_T_integrand E.V_T E.V_S x a)
      Sanctions.I (E.α x) := by
    intro a ha
    have h : p.joint_T_top_integrand E.V_T E.V_S x a ≤
        p.joint_T_top_integrand E.V_T E.V_S x (E.α x) := E.α_opt_top x hx ha
    rw [p.joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI
          (D.sender_unique_on E.V_S hVS) hx ha,
        p.joint_T_top_integrand_eq_joint_T_integrand_of_uniqueOnI
          (D.sender_unique_on E.V_S hVS) hx (E.α_mem x hx)] at h
    exact h
  -- The carrier selector maximises it too; Target argmax uniqueness pins both.
  have hu : p.TargetArgmaxUnique E.V_T E.V_S := D.target_unique_on E.V_T hVT E.V_S hVS
  exact hu x hx (E.α x) (D.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩ x) (E.α_mem x hx)
    (D.α_on_mem _ _ x) hmax (D.α_on_isMaxOn ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩ hx)

/-- **A Bellman-consistent carrier value pair whose policy agrees with the
carrier selector on the state set is a joint fixed point (round BH1.1).**
Sibling of `fixedPoint_of_bellman_fixed_of_selector_coincidence` with the
coincidence weakened from equality of functions on `ℝ` to agreement on `S`
(`Set.EqOn … Sanctions.S`). The Target component never reads the policy, and the
Sender Bellman operator evaluates it only at feasible states
(`bellmanS_BCF_congr_on`), so the carrier selector is itself a Sender fixed
point at `V_S`. No leader-optimality or feasibility input. General in `F`. -/
theorem fixedPoint_of_bellman_fixed_of_selector_eqOn
    (h_inv : D.IsInvariant)
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hVT : V_T ∈ D.carrier_T) (hVS : V_S ∈ D.carrier_S)
    {α : ℝ → ℝ} (hαc : Continuous α)
    (hα : Set.EqOn α (D.α_on ⟨V_T, hVT⟩ ⟨V_S, hVS⟩) Sanctions.S)
    (V_S_fix : V_S = p.bellmanS_BCF α hαc V_S)
    (V_T_fix_top : ∀ x : ↥(Sanctions.S : Set ℝ),
      V_T x = sSup ((fun a => p.joint_T_top_integrand V_T V_S x.val a)
                      '' Sanctions.I)) :
    (D.jointTargetOp_sub h_inv (⟨V_T, hVT⟩, ⟨V_S, hVS⟩),
      D.jointSenderOp_sub h_inv (⟨V_T, hVT⟩, ⟨V_S, hVS⟩))
      = (⟨V_T, hVT⟩, ⟨V_S, hVS⟩) :=
  D.fixedPoint_of_bellman_fixed_of_selector_coincidence h_inv hVT hVS
    (D.α_on_continuous _ _) rfl
    (V_S_fix.trans (p.bellmanS_BCF_congr_on hαc (D.α_on_continuous _ _) hα V_S))
    V_T_fix_top

/-- **Every carrier equilibrium is a joint fixed point, with no selector
hypothesis (round BH1.1).** Sibling of
`fixedPoint_of_feedbackStackelbergTop_of_selector_coincidence` without its `hα`:
carrier membership of the two values alone makes the equilibrium's value pair a
fixed point of the joint subtype operator. The policy's agreement with the
carrier selector on `S` is derived (`α_eqOn_α_on_of_feedbackStackelbergTop`);
in this direction leader optimality `α_opt_top` and feasibility `α_mem` are
consumed, to derive it. General in `F`. -/
theorem fixedPoint_of_feedbackStackelbergTop_of_mem
    (h_inv : D.IsInvariant)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ D.carrier_T) (hVS : E.V_S ∈ D.carrier_S) :
    (D.jointTargetOp_sub h_inv (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩),
      D.jointSenderOp_sub h_inv (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩))
      = (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩) :=
  D.fixedPoint_of_bellman_fixed_of_selector_eqOn h_inv hVT hVS E.hα
    (D.α_eqOn_α_on_of_feedbackStackelbergTop E hVT hVS) E.V_S_fix E.V_T_fix_top

/-- **Schur-margin equilibrium uniqueness within the carrier class, with no
selector hypothesis (round BH1.1, 2026-10-06).** Any two top-selector feedback
Stackelberg equilibria whose value pairs lie in the carriers have the same
Target value, the same Sender value, and the same policy at every feasible
state. Sibling of `feedbackStackelbergTop_unique_in_carrier_schur` with its two
selector-coincidence binders `hαE`, `hαE'` dropped, since every carrier
equilibrium already plays the carrier selector on `S`
(`α_eqOn_α_on_of_feedbackStackelbergTop`). The policy conclusion is agreement
on `S`, not equality of functions on `ℝ`: off `S` a policy is never evaluated
and is not pinned. The Target diagonal bound `β_T < 1` is not a binder either;
the cross signs, `β_S < 1` and the Schur margin imply it
(`Foundations.Perov.lt_one_of_schur_margin`, round BG1.1). Since round BJ1.1
(2026-10-07) the Perov step it calls is sign-free, so the two diagonal sign
binders are no longer read, and the closing round of the renovation (2026-10-08,
the author's decision) drops them from the statement.

Plain language: within the carrier class the equilibrium is unique, both as a
pair of value functions and as a compliance policy over every political state
the game can reach. No assumption that the equilibrium uses the carrier's own
selector is needed. It makes no global equilibrium-uniqueness claim;
bistability concerns state-path selection under a single equilibrium. General
in `F`. -/
theorem feedbackStackelbergTop_unique_in_carrier_schur_of_mem
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointTargetOp_sub h_inv (V, W))
            (D.jointTargetOp_sub h_inv (V', W'))
        ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS),
      dist (D.jointSenderOp_sub h_inv (V, W))
            (D.jointSenderOp_sub h_inv (V', W'))
        ≤ L_ST * dist V V' + β_S * dist W W')
    (hβ_S_lt : β_S < 1)
    (hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S))
    (E E' : p.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ D.carrier_T) (hVS : E.V_S ∈ D.carrier_S)
    (hVT' : E'.V_T ∈ D.carrier_T) (hVS' : E'.V_S ∈ D.carrier_S) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ Set.EqOn E.α E'.α Sanctions.S := by
  obtain ⟨z₀, _, huniq⟩ := D.existsUnique_fixedPoint_in_carrier_schur h_inv
    hT_T hT_S
    (Sanctions.Foundations.Perov.lt_one_of_schur_margin hL_TS_nn hL_ST_nn
      hβ_S_lt hSchur)
    hβ_S_lt hSchur
  have h1 := huniq (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩)
    (D.fixedPoint_of_feedbackStackelbergTop_of_mem h_inv E hVT hVS)
  have h2 := huniq (⟨E'.V_T, hVT'⟩, ⟨E'.V_S, hVS'⟩)
    (D.fixedPoint_of_feedbackStackelbergTop_of_mem h_inv E' hVT' hVS')
  have hpair := h1.trans h2.symm
  have hT : E.V_T = E'.V_T := congrArg (fun w => (Prod.fst w).val) hpair
  have hS : E.V_S = E'.V_S := congrArg (fun w => (Prod.snd w).val) hpair
  refine ⟨hT, hS, ?_⟩
  have e1 : (⟨E.V_T, hVT⟩ : D.CarrierT) = ⟨E'.V_T, hVT'⟩ := Subtype.ext hT
  have e2 : (⟨E.V_S, hVS⟩ : D.CarrierS) = ⟨E'.V_S, hVS'⟩ := Subtype.ext hS
  intro x hx
  rw [D.α_eqOn_α_on_of_feedbackStackelbergTop E hVT hVS hx,
    D.α_eqOn_α_on_of_feedbackStackelbergTop E' hVT' hVS' hx, e1, e2]

end ValueClass2
end Params
end AbstractGame

end

end Sanctions
