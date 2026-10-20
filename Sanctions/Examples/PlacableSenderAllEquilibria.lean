/-
Sanctions/Examples/PlacableSenderAllEquilibria.lean

**On a chord economy, under a general transition: every equilibrium with a
state-nonincreasing Target policy carries the Sender's continuation wedge**
(round AM, 2026-09-22; doc 100 §3, deliverable A, on the user's word; on the
abstract payoffs since round AV, 2026-09-25, doc 104).

`Theory/Equilibrium/CertifiedEquilibria.lean` gives the Sender value of any
top-selector equilibrium a certified lower state slope once the Target policy
satisfies a joint state chord. On a chord economy the chord at slope
`g_S = w_lo/(1 − β_S g_lo)` again reduces to compliance nonincreasing in the
state (`chord_of_antitone`): the stage payoff's state slope is at least `w_lo`
(S2), the transition's lower state chord is `g_lo`, and the only term that can
spoil the chord is the change in compliance, which cannot help the Sender when
a larger concession is never worth more to the Sender in itself
(`ZeroSanctionAntitone`, the pairwise one-sided form of zero-sanction
neutrality, sign-off M2).

With the slope in hand, no carrier membership is needed for the conclusion
that matters: at any Sender value of lower slope `g_S`, every maximiser of the
Sender's objective at state `x` and compliance `a` is at least
`min{(u_lo + r_lo·x − k_hi·a + β_S·g_S·d_lo)/Q̄, 1}`
(`argmax_ge_wedge_of_lowerSlope`): the stage return to a higher sanction is at
least `u_lo + r_lo·x − k_hi·a − Q̄·s` (floor S12, cross rate S8, placation S10u;
`US_sanction_gain_ge`), and the continuation adds at least `β_S·g_S·d_lo` per
unit, the wedge of the manuscript's Sender-side comparison. So **in every
top-selector equilibrium whose Target policy is nonincreasing in the state, the
realised sanction is at least that floor at the policy's compliance, at every
state** (`equilibrium_sanction_ge_wedge_of_antitone`). The constructed defiance
equilibrium's constant policy is in the class.

**Scope (Rule 9).** A quantifier strengthening over the economy's construction,
scoped by the policy class; nothing is said about equilibria whose compliance
rises with entrenchment, and no equilibrium beyond the constructed ones is
asserted to exist. Rule 22: general in the transition, through the chords
`g_lo` and `d_lo` only. On the quadratic–linear family the floor is
`min{(u₀ + r·x − k·a + β_S·g_S·d_lo)/q, 1}`.

**Placation ceiling (renovation item BJ2.2, 2026-10-07).** The upper placation rate
`k_hi` is no longer a field of `ChordEconomy`: both theorems take a placation ceiling
`hPC : E.PlacationCeiling k_hi` and state the floor at that `k_hi`. A relief economy
supplies its own (`ChordEconomyRelief.placationCeiling`).
-/
import Sanctions.Examples.PlacableSenderEquilibrium
import Sanctions.Theory.Equilibrium.CertifiedEquilibria

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-- `w_lo + β_S·g_S·g_lo = g_S`. -/
theorem gS_fix : E.wlo + E.β_S * E.gS * E.glo = E.gS := by
  linear_combination (-1 : ℝ) * E.gS_mul

/-- **The joint state chord holds at slope `g_S` for every state-nonincreasing
policy**, under a general transition with lower state chord `g_lo`, when a
larger concession is never worth more to the Sender in itself. -/
theorem chord_of_antitone (hN : E.ZeroSanctionAntitone) {α : ℝ → ℝ}
    (hanti : AntitoneOn α Sanctions.S) (hαmem : ∀ y ∈ Sanctions.S, α y ∈ Sanctions.I) :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      E.gS * (y₂ - y₁)
        ≤ (E.toParams.U_S y₂ (α y₂) s - E.toParams.U_S y₁ (α y₁) s)
          + E.toParams.β_S * E.gS * (E.toParams.F y₂ s - E.toParams.F y₁ s) := by
  intro s hs y₁ hy₁ y₂ hy₂ hle
  have hα : α y₂ ≤ α y₁ := hanti hy₁ hy₂ hle
  have ha₁ := hαmem y₁ hy₁
  have ha₂ := hαmem y₂ hy₂
  have hband := (E.hbandAll s hs) y₁ hy₁ y₂ hy₂ hle
  -- the concession `α y₁ → α y₂` does not lower the Sender's payoff
  have hcomp : E.U_S y₂ (α y₁) s ≤ E.U_S y₂ (α y₂) s := E.US_antitone hN hy₂ ha₂ ha₁ hα hs
  -- the state slope at the fixed compliance `α y₁`
  have hstate := E.hUS_stateSlope (α y₁) ha₁ s hs y₁ hy₁ y₂ hy₂ hle
  have hβg : 0 ≤ E.β_S * E.gS := mul_nonneg E.hβS0.le E.gS_pos.le
  have hcont := mul_le_mul_of_nonneg_left hband.1 hβg
  have hfix : E.gS * (y₂ - y₁)
      = E.wlo * (y₂ - y₁) + E.β_S * E.gS * (E.glo * (y₂ - y₁)) := by
    linear_combination (-(y₂ - y₁)) * E.gS_fix
  change E.gS * (y₂ - y₁)
    ≤ (E.U_S y₂ (α y₂) s - E.U_S y₁ (α y₁) s) + E.β_S * E.gS * (E.F y₂ s - E.F y₁ s)
  linarith

/-- **Every equilibrium with a state-nonincreasing policy has a Sender value of
lower slope `g_S`**, when a larger concession is never worth more to the Sender
in itself. -/
theorem V_S_lowerSlope_of_antitone (hN : E.ZeroSanctionAntitone)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hanti : AntitoneOn Eq.α Sanctions.S) :
    Params.LowerSlopeOnValueOn Eq.V_S (Icc (0 : ℝ) 1) E.gS :=
  Params.FeedbackStackelbergEquilibriumTop.V_S_lowerSlope_of_policy_chord E.toParams Eq
    (E.chord_of_antitone hN hanti Eq.α_mem)

/-- **Every maximiser of the Sender's objective at a value of lower slope `g_S`
is at least the stage floor plus the continuation wedge**,
`min{(u_lo + r_lo·x − k_hi·a + β_S·g_S·d_lo)/Q̄, 1}`, for any placation ceiling `k_hi`.
General in `F`. Renovation item BJ2.2 (2026-10-07): the ceiling is the hypothesis `hPC`,
no longer a field of the base class. -/
theorem argmax_ge_wedge_of_lowerSlope {khi : ℝ} (hPC : E.PlacationCeiling khi) {V_S : Val}
    (hg : Params.LowerSlopeOnValueOn V_S Sanctions.I E.gS)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) {s : ℝ}
    (hs : s ∈ Sanctions.I)
    (hmax : IsMaxOn (fun s' => E.toParams.U_S x a s'
      + E.toParams.β_S * V_S (Sanctions.clipS' (E.toParams.F x s'))) Sanctions.I s) :
    min ((E.ulo + E.rlo * x - khi * a + E.β_S * E.gS * E.dlo) / E.Qbar) 1 ≤ s := by
  set m := E.ulo + E.rlo * x - khi * a + E.β_S * E.gS * E.dlo with hm
  have hQ := E.Qbar_pos
  rcases le_or_gt m 0 with hmnp | hmpos
  · have : min (m / E.Qbar) 1 ≤ 0 :=
      le_trans (min_le_left _ _) (div_nonpos_of_nonpos_of_nonneg hmnp hQ.le)
    linarith [hs.1]
  set s₀ := min (m / E.Qbar) 1 with hs₀
  have hs₀pos : 0 < s₀ := lt_min (div_pos hmpos hQ) one_pos
  have hs₀le1 : s₀ ≤ 1 := min_le_right _ _
  have hs₀q : E.Qbar * s₀ ≤ m := by
    have := min_le_left (m / E.Qbar) 1
    rw [le_div_iff₀ hQ] at this
    linarith
  by_contra hlt
  have hlt : s < s₀ := not_le.mp hlt
  have hs₀mem : s₀ ∈ Sanctions.I := ⟨hs₀pos.le, hs₀le1⟩
  have hFs : E.toParams.F x s ∈ Sanctions.I := E.F_mem x s hx hs
  have hFs₀ : E.toParams.F x s₀ ∈ Sanctions.I := E.F_mem x s₀ hx hs₀mem
  have hFle : E.toParams.F x s ≤ E.toParams.F x s₀ := E.F_mono_s x hlt.le
  have hle : Sanctions.clipS' (E.toParams.F x s) ≤ Sanctions.clipS' (E.toParams.F x s₀) :=
    Sanctions.clipS'_mono hFle
  have hslope := hg (Sanctions.clipS' (E.toParams.F x s)) (Sanctions.clipS' (E.toParams.F x s₀))
    (by rw [Sanctions.clipS'_val_eq_of_mem hFs]; exact hFs)
    (by rw [Sanctions.clipS'_val_eq_of_mem hFs₀]; exact hFs₀) hle
  have hdist : dist (Sanctions.clipS' (E.toParams.F x s)) (Sanctions.clipS' (E.toParams.F x s₀))
      = E.toParams.F x s₀ - E.toParams.F x s := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hFs,
      Sanctions.clipS'_val_eq_of_mem hFs₀, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hdist] at hslope
  have hchord : E.dlo * (s₀ - s) ≤ E.toParams.F x s₀ - E.toParams.F x s :=
    E.hSlo hx hs hs₀mem hlt.le
  have hobj := hmax hs₀mem
  simp only [Set.mem_setOf_eq] at hobj
  -- the stage gain from `s` to `s₀`
  have hstage := E.US_sanction_gain_ge hPC hx ha hs hs₀mem hlt.le
  have hgap : 0 < s₀ - s := by linarith
  have hkey : 0 < (s₀ - s) * (m - E.Qbar / 2 * (s₀ + s)) := by
    apply mul_pos hgap
    have : E.Qbar / 2 * (s₀ + s) < E.Qbar * s₀ := by nlinarith [hQ]
    linarith
  have hgS := E.gS_pos
  have h1 : E.gS * (E.dlo * (s₀ - s)) ≤ E.gS * (E.toParams.F x s₀ - E.toParams.F x s) :=
    mul_le_mul_of_nonneg_left hchord hgS.le
  have h2 := mul_le_mul_of_nonneg_left (le_trans h1 hslope) E.hβS0.le
  have e : (s₀ - s) * (m - E.Qbar / 2 * (s₀ + s))
      = (s₀ - s) * (E.ulo + E.rlo * x - khi * a - E.Qbar * (s₀ + s) / 2)
        + E.β_S * (E.gS * (E.dlo * (s₀ - s))) := by rw [hm]; ring
  have hobj' : E.U_S x a s₀ + E.β_S * V_S (Sanctions.clipS' (E.F x s₀))
      ≤ E.U_S x a s + E.β_S * V_S (Sanctions.clipS' (E.F x s)) := hobj
  linarith

/-- **In every top-selector equilibrium whose Target policy is nonincreasing in
the state, the realised sanction is at least the stage floor at the policy's
compliance plus the continuation wedge `β_S·g_S·d_lo/Q̄`, at every state**, when
a larger concession is never worth more to the Sender in itself, for any placation
ceiling `k_hi`. General in `F`. A pinned headline; renovation item BJ2.2 (2026-10-07,
approved re-pin): the upper placation rate is the hypothesis `hPC`
(`PlacationCeiling`), no longer a field of the base class, and the floor is stated at
its `k_hi`. -/
theorem equilibrium_sanction_ge_wedge_of_antitone {khi : ℝ} (hPC : E.PlacationCeiling khi)
    (hN : E.ZeroSanctionAntitone)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hanti : AntitoneOn Eq.α Sanctions.S)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    min ((E.ulo + E.rlo * x - khi * Eq.α x + E.β_S * E.gS * E.dlo) / E.Qbar) 1
      ≤ E.toParams.dynamicEquilibriumRule Eq x :=
  E.argmax_ge_wedge_of_lowerSlope hPC (E.V_S_lowerSlope_of_antitone hN Eq hanti) hx
    (Eq.α_mem x hx) (E.toParams.σ_dyn_top_mem_I _ x (Eq.α x))
    (E.toParams.σ_dyn_top_isMaxOn Eq.V_S x (Eq.α x))

/-- The wedge is strictly positive: the floor strictly exceeds the stage floor. -/
theorem continuationWedge_pos : 0 < E.β_S * E.gS * E.dlo / E.Qbar :=
  div_pos (mul_pos (mul_pos E.hβS0 E.gS_pos) E.hdlo0) E.Qbar_pos

end ChordEconomy

end

#print axioms Sanctions.Examples.ChordEconomy.chord_of_antitone
#print axioms Sanctions.Examples.ChordEconomy.V_S_lowerSlope_of_antitone
#print axioms Sanctions.Examples.ChordEconomy.argmax_ge_wedge_of_lowerSlope
#print axioms Sanctions.Examples.ChordEconomy.equilibrium_sanction_ge_wedge_of_antitone

end Examples
end Sanctions
