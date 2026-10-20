/-
Sanctions/Theory/Certificates/ConvexValueRoute.lean

**Route (b) for `hSC_on` (C7 decision, user-approved 2026-06-11):
the nondecreasing-increments / range-local convexity cone.**

`hSC_on` — Milgrom-Shannon single crossing of the Sender's
forward-looking objective `U_S(x, α(x), s) + β_S·V_S(F(x,s))` in
(sanction; state) on the basin — is the one Sender-side dynamic field
the sweep proved is not derivable for free (single crossing is not
sum-closed; the continuation has the needed increasing differences
iff `V_S` is convex along the transition range — Topkis 1998
Thm 2.6.2 at the affine transition `F(x,s) = (1−δ)x + δs`).

Route (b) buys the derivation with a RANGE-LOCAL curvature cone:

  `ValueConvexOnRange V lo` — the Sender value, read along the
  state interval `[lo, 1]` (the basin transition range
  `lo ≤ (1−δ)·x̄`), is convex.

**Economic content** (the reason (b) was chosen over global
convexity): on the post-tipping basin the Sender faces *no
diminishing returns to entrenchment* — each further step of
political hardening is worth weakly more than the last. This is the
increasing-returns lock-in-consolidation mechanism of the
institutional-persistence literature (Pierson 2000; the
consolidation steps of Acemoglu-Robinson), imposed ONLY where that
literature claims it: past the tipping threshold. The contested and
low-basin regions are left entirely free, so the bistability
machinery (R47-48 low-basin duals) is untouched.

**Derivation chain** (`hSC_on_of_carrier_convexOn_range`): the
dynamic objective's chord difference splits into
  stage part  — handled by `SenderStageID` (state propagation at a
                fixed action) + `SenderActionDD` (R28
                compliance-placates sign) + α-antitonicity on the
                basin (E4, available under `SubstitutedTargetDD`),
                exactly the B4 propagation pattern; and
  continuation — handled by the cone: chords of `V_S` of equal
                width `δ(s₂−s₁)` shift weakly up when translated
                right by `(1−δ)(x'−x)` (`chord_shift`).
The sum then has increasing differences, hence single crossing.

**Witness anchor**: any carrier with `ValueLipschitzWith V_S 0`
(constant `V_S` — e.g. the R34 `polyComplianceValueClass2` Sender
carrier `valLipBall 2 0`) lies in the cone with equality
(`ValueConvexOnRange.of_lipschitzWith_zero`), so the route does not
empty the project's inhabited example.

**Honest caveats (recorded)**: (i) the cone fails under genuine
saturation of entrenchment returns strictly inside the basin — if
that is the preferred semantics, keep `hSC_on` as a certificate
field (status quo; three dischargers exist). (ii) Bellman
*preservation* of the cone is CLOSED-NEGATIVE in range-local form
(sweep digest [40]/[130], verified): invariance of "convex on
`[lo, 1]`" needs `V` convex on the strictly larger
`[(1−δ)·lo, 1]`, and iteration expands the requirement to all of
`[0, 1]` — a constructive preservation route forces the global cone
(= route (a), rejected on semantics). The carrier-choice discharge
below is therefore the honest endpoint of the range-local route:
if your carrier lies in the cone (e.g. constant `V_S`), `hSC_on`
is derived; populating non-constant cone carriers would require
the global route-(a) commitment.

Rule 3: the cone is a carrier-choice condition (like the E5 gain
ball), consumed as an explicit hypothesis of the dischargers below —
adopted under the user's explicit route-(b) approval. Rule 13:
additive; the field-form certificate and its three existing
dischargers are untouched.
-/

import Sanctions.Theory.Basin.StageFlipDischargers
import Sanctions.Foundations.Topkis

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame

/-- **The route-(b) cone: range-local convexity of a value function
(Round C7-b).** The value, read along the state interval `[lo, 1]`,
is convex — equivalently (for continuous `V`): equal-width chords
shift weakly upward when translated right. Economic reading: no
diminishing returns to entrenchment on `[lo, 1]`. -/
def ValueConvexOnRange (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (lo : ℝ) : Prop :=
  ConvexOn ℝ (Set.Icc lo (1 : ℝ)) (fun y : ℝ => V (Sanctions.clipS' y))

namespace ValueConvexOnRange

/-- **Equal-width chords shift up (the nondecreasing-increments
form).** For `lo ≤ y₁ ≤ y₂` and a rightward translation `t ≥ 0`
staying below `1`: `V(y₂) − V(y₁) ≤ V(y₂+t) − V(y₁+t)`. This is the
exact inequality the single-crossing comparison consumes. -/
theorem chord_shift {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {lo : ℝ}
    (hV : ValueConvexOnRange V lo) {y₁ y₂ t : ℝ}
    (hy₁lo : lo ≤ y₁) (hy : y₁ ≤ y₂) (ht : 0 ≤ t) (htop : y₂ + t ≤ 1) :
    V (Sanctions.clipS' y₂) - V (Sanctions.clipS' y₁)
      ≤ V (Sanctions.clipS' (y₂ + t)) - V (Sanctions.clipS' (y₁ + t)) := by
  have hV' : ConvexOn ℝ (Set.Icc lo (1 : ℝ))
      (fun y : ℝ => V (Sanctions.clipS' y)) := hV
  rcases lt_or_ge 0 (y₂ - y₁ + t) with htot | htot
  · -- nondegenerate: convex-combination identities at weights t/(w+t).
    have mem₁ : y₁ ∈ Set.Icc lo (1 : ℝ) := ⟨hy₁lo, by linarith⟩
    have mem₂ : y₂ + t ∈ Set.Icc lo (1 : ℝ) := ⟨by linarith, htop⟩
    have hμ_nn : 0 ≤ t / (y₂ - y₁ + t) := div_nonneg ht htot.le
    have hμ_le : t / (y₂ - y₁ + t) ≤ 1 := by
      rw [div_le_one htot]; linarith
    have hb_nn : 0 ≤ 1 - t / (y₂ - y₁ + t) := by linarith
    have hab : t / (y₂ - y₁ + t) + (1 - t / (y₂ - y₁ + t)) = 1 := by ring
    have hba : (1 - t / (y₂ - y₁ + t)) + t / (y₂ - y₁ + t) = 1 := by ring
    have hc₁ := hV'.2 mem₁ mem₂ hμ_nn hb_nn hab
    have hc₂ := hV'.2 mem₁ mem₂ hb_nn hμ_nn hba
    simp only [smul_eq_mul] at hc₁ hc₂
    have hne : y₂ - y₁ + t ≠ 0 := htot.ne'
    have e₁ : t / (y₂ - y₁ + t) * y₁
        + (1 - t / (y₂ - y₁ + t)) * (y₂ + t) = y₂ := by
      field_simp
      ring
    have e₂ : (1 - t / (y₂ - y₁ + t)) * y₁
        + t / (y₂ - y₁ + t) * (y₂ + t) = y₁ + t := by
      field_simp
      ring
    rw [e₁] at hc₁
    rw [e₂] at hc₂
    linarith
  · -- degenerate: zero width and zero shift.
    have h1 : y₂ = y₁ := by linarith
    have h2 : t = 0 := by linarith
    rw [h1, h2]
    simp

/-- **Constant values lie in the cone (witness anchor).** Any value
with zero Lipschitz constant — e.g. the R34 `polyComplianceValueClass2`
Sender carrier — satisfies the cone with equality. -/
theorem of_lipschitzWith_zero
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hV : Params.ValueLipschitzWith V 0) (lo : ℝ) :
    ValueConvexOnRange V lo := by
  have hconst : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ), V y₁ = V y₂ := by
    intro y₁ y₂
    have h := hV y₂ y₁
    rw [zero_mul] at h
    have h0 : V y₁ - V y₂ = 0 :=
      abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    linarith
  constructor
  · exact convex_Icc lo 1
  · intro a _ha b _hb wa wb hwa hwb hab
    simp only [smul_eq_mul]
    rw [hconst (Sanctions.clipS' (wa * a + wb * b)) (Sanctions.clipS' a),
        hconst (Sanctions.clipS' b) (Sanctions.clipS' a)]
    have : wa * V (Sanctions.clipS' a) + wb * V (Sanctions.clipS' a)
        = V (Sanctions.clipS' a) := by rw [← add_mul, hab, one_mul]
    linarith

end ValueConvexOnRange

namespace Params

variable (p : Sanctions.AbstractGame.Params)


/-- **Route (b) at a general transition.** Single crossing of the Sender's
dynamic objective in (sanction; state) on the basin, with the affine law
replaced by an order condition on the transition.

Inputs beyond the affine version's:

* `hF_lo` — the reachable range: on the basin the transition lands at or above
  `lo`, the left endpoint of the convexity range;
* `hF_super` — the transition has increasing differences in state and sanction:
  a higher inherited state weakly widens the effect of a larger sanction on next
  period's state. Under the affine law this holds with equality;
* `hmonoV` — carrier Sender values are non-decreasing along the range. Needed
  only to absorb the extra chord width that a strictly supermodular transition
  creates, which is why the affine argument could omit it.

Everything else is unchanged: stage complementarity, the R28 compliance-placates
sign, α-antitonicity on the basin, and carrier convexity along the range. -/
theorem hSC_on_of_carrier_convexOn_range_generalF
    (D : p.ValueClass2) {xbar lo : ℝ}
    (hxbar_mem : xbar ∈ Sanctions.I)
    (hF_lo : ∀ x ∈ Set.Icc xbar (1 : ℝ), ∀ s ∈ Sanctions.I, lo ≤ p.F x s)
    (hF_super :
      ∀ x ∈ Set.Icc xbar (1 : ℝ), ∀ x' ∈ Set.Icc xbar (1 : ℝ), x ≤ x' →
        ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
          p.F x s₂ - p.F x s₁ ≤ p.F x' s₂ - p.F x' s₁)
    (hID_S : p.SenderStageID) (hDD_a : p.SenderActionDD)
    (hanti : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      AntitoneOn (D.α_on V_T V_S) (Set.Icc xbar 1))
    (hconv : ∀ V_S ∈ D.carrier_S, ValueConvexOnRange V_S lo)
    (hmonoV : ∀ V_S ∈ D.carrier_S,
      MonotoneOn (fun y : ℝ => V_S (Sanctions.clipS' y)) (Set.Icc lo (1 : ℝ))) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc xbar 1)
        (fun s x => p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s) := by
  intro V_T V_S s₁ s₂ x x' hs₁ hs₂ hss hx hx' hxx'
  have hxI : x ∈ Sanctions.I := ⟨le_trans hxbar_mem.1 hx.1, hx.2⟩
  have hx'I : x' ∈ Sanctions.I := ⟨le_trans hxbar_mem.1 hx'.1, hx'.2⟩
  have hαx := D.α_on_mem V_T V_S x
  have hαx' := D.α_on_mem V_T V_S x'
  -- α antitone on the basin: deeper state, weakly less compliance.
  have hα_le : D.α_on V_T V_S x' ≤ D.α_on V_T V_S x :=
    hanti V_T V_S hx hx' hxx'
  have h_action := hDD_a x' hx'I hs₁ hs₂ hss hαx' hαx hα_le
  have h_state := hID_S (D.α_on V_T V_S x) hαx hs₁ hs₂ hss hxI hx'I hxx'
  -- Continuation: the Topkis composition, in place of the affine chord shift.
  have hVconv : ConvexOn ℝ (Set.Icc lo (1 : ℝ))
      (fun y : ℝ => V_S.val (Sanctions.clipS' y)) := hconv V_S.val V_S.2
  have hVmono : MonotoneOn (fun y : ℝ => V_S.val (Sanctions.clipS' y))
      (Set.Icc lo (1 : ℝ)) := hmonoV V_S.val V_S.2
  have hFa : lo ≤ p.F x s₁ := hF_lo x hx s₁ hs₁
  have hab : p.F x s₁ ≤ p.F x s₂ := p.F_mono_s x hss
  have hac : p.F x s₁ ≤ p.F x' s₁ := p.F_mono_x s₁ hxx'
  have hcd : p.F x' s₁ ≤ p.F x' s₂ := p.F_mono_s x' hss
  have hd1 : p.F x' s₂ ≤ 1 := (p.F_mem x' s₂ hx'I hs₂).2
  have hsuper := hF_super x hx x' hx' hxx' s₁ hs₁ s₂ hs₂ hss
  have hcont :
      V_S.val (Sanctions.clipS' (p.F x s₂))
          - V_S.val (Sanctions.clipS' (p.F x s₁))
        ≤ V_S.val (Sanctions.clipS' (p.F x' s₂))
          - V_S.val (Sanctions.clipS' (p.F x' s₁)) :=
    Sanctions.Topkis.chord_le_chord_of_convexOn_monotoneOn
      hVconv hVmono hFa hab hac hsuper hcd hd1
  have hβS : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hcont' := mul_le_mul_of_nonneg_left hcont hβS
  -- Increasing differences of the dynamic objective.
  have hID_total :
      p.senderDynObjective V_S.val x' (D.α_on V_T V_S x') s₂
        - p.senderDynObjective V_S.val x' (D.α_on V_T V_S x') s₁
      ≥ p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s₂
        - p.senderDynObjective V_S.val x (D.α_on V_T V_S x) s₁ := by
    simp only [senderDynObjective]
    linarith
  constructor
  · intro h
    simp only at h ⊢
    linarith
  · intro h
    simp only at h ⊢
    linarith


end Params
end AbstractGame

end

end Sanctions
