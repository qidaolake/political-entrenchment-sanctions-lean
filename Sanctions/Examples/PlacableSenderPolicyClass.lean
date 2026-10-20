/-
Sanctions/Examples/PlacableSenderPolicyClass.lean

**Tier 2: a monotone realised rule from conditions on the policy alone** (round
AV, 2026-09-25; doc 104, sign-off M9: the second open item of 2026-09-25, proved
with the class restriction the open-items report stated).

## What is proved

Round AR's uniqueness theorem (`unique_equilibrium_of_monotone_class`)
quantifies over equilibria whose compliance policy is nonincreasing in the state
*and* whose realised sanction rule is nondecreasing in it. Tier 2 derives the
second condition from conditions on the policy.

* **The general form, on every chord economy**
  (`rule_monotoneOn_of_policy_bounds`). Its hypotheses, all of them (the
  outside reader's A2, 2026-09-27, found an earlier summary that listed only
  two): (i) the policy is nonincreasing; (ii) the Sender's stage payoff along it,
  `y ↦ U_S(y, α(y), s)`, is `L`-Lipschitz in the state at every sanction, and
  (iii) `M`-semiconvex, with `L, M ≥ 0`; (iv) the stage has increasing
  differences in (sanction; state) at rate `ρ` at every compliance level; (v) the
  margin `β_S(σ(L,M)·g_hi·d_hi + (K(L) + 2σ(L,M))·M_mix) ≤ ρ`, with
  `K(L) = L/(1 − β_S g_hi)` and `σ(L,M) = (M + β_S K(L) M_cx)/(1 − β_S g_hi²)`;
  and (vi) one-sided zero-sanction neutrality, `ZeroSanctionAntitone` (at zero
  sanction the Sender's payoff is nonincreasing in compliance), which puts the
  Sender's value in the lower-slope part of the policy carrier. Then the
  realised rule is nondecreasing in the state. Under the unrefined loss-offset
  margin the equilibrium is then the constructed defiance equilibrium
  (`unique_equilibrium_of_policy_bounds`). Conditions (ii)–(v) and (vi) are
  hypotheses, not class conditions; the author declined to make them fields of
  the chord economy (doc 107, sign-off Y5).
* **On the quadratic–linear family, from the policy alone**
  (`PlacableEconomyF.rule_monotoneOn_of_concave_policy`,
  `PlacableEconomyF.unique_equilibrium_of_concave_policy`). The three payoff
  inputs are theorems there. The stage along the policy is
  `(r + w + k·L_α)`-Lipschitz when the policy is `L_α`-Lipschitz, and
  `k·M_α`-semiconvex when the policy is `M_α`-semiconcave (the placation term
  is `−k·s·α(y)`); the stage cross rate is exactly `r` at every compliance
  level. The class is the one the open-items report stated and the user
  approved: the policy is (i) nonincreasing, (ii) `L_α`-Lipschitz and (iii)
  `M_α`-semiconcave on `[0,1]`, and (iv) the margin holds at
  `K' = (r + w + k L_α)/(1 − β_S g_hi)` and
  `σ' = (k M_α + β_S K' M_cx)/(1 − β_S g_hi²)`.
* **The flat case** (`PlacableEconomyF.unique_equilibrium_of_concave_policy_flat`).
  With convex state sections and no cross-curvature in the transition
  (`M_cx = M_mix = 0`, true of both pinned members) and a concave policy
  (`M_α = 0`), the margin reads `0 ≤ r`. The only new content is then that the
  policy is nonincreasing, Lipschitz and concave.

## The argument

1. **The equilibrium Sender value lies in a policy carrier** (`carrierPol`):
   lower slope `g_S`, `K(L)`-Lipschitz, `σ(L,M)`-semiconvex through the clip.
   The carrier is closed, nonempty and invariant under the Sender's Bellman
   operator at the policy. The lower slope comes from `chord_of_antitone`; the
   Lipschitz bound from the stage bound and the state chord `g_hi`; the
   semiconvexity from the stage bound, the composition rule and the supremum
   rule. So the operator's unique fixed point, which is the equilibrium's Sender
   value, is in it.
2. **Increasing differences at any fixed compliance.** The stage cross rate `ρ`
   covers the continuation's cross difference, which is bounded below on the
   carrier by `crossDiff_comp_ge_of_semiconvex`. So the greatest response is
   nondecreasing in the state at each fixed compliance (single crossing; no
   uniqueness is needed).
3. **The rule chain.** `R(x₂) = σ(x₂, α(x₂)) ≥ σ(x₂, α(x₁)) ≥ σ(x₁, α(x₁)) = R(x₁)`:
   the first step by decreasing differences in (sanction; compliance) and
   `α(x₂) ≤ α(x₁)`, the second by step 2.

## Scope

* **Why the class conditions sit on the policy.** A convex kink in the policy
  becomes, through the placation term, a concave kink in the Sender's value. The
  Sender then bunches its successor state at the kink, and its response can fall
  with the state. A numeric probe on 2026-09-25 at the pinned Sender constants
  showed this for a steep piecewise-linear nonincreasing policy (the rule fell by
  `0.10`–`0.15`) and for a smooth one with large convex curvature. Those are
  fixed-policy computations, not equilibria: whether a merely nonincreasing
  policy suffices at an actual equilibrium is open, neither proved nor refuted
  (Rules 9D and 11).
* **Narrower than round AR, not a strengthening of it.** The new class is
  contained in AR's, since the theorem produces the rule's monotonicity, so the
  composed uniqueness holds on a narrower class. What it adds is that the class
  is stated in terms of the policy alone.
* **Why the headline form is on the family.** On a general chord economy two of
  the three payoff inputs are not among the rate conditions of doc 104 §2. The
  stage cross rate is bounded below only at defiance (S8), and the stage along a
  policy has no semiconvexity bound, because the conditions say nothing about the
  payoff's curvature in compliance. The general theorem therefore takes both as
  hypotheses, and the quadratic–linear family discharges them. Making them
  conditions of the chord economy would widen its assumption surface (Rule 3);
  that choice is left to the user.
* **Rule 3.** No field. The class conditions are hypotheses on the quantified
  equilibrium (sign-off M9). The carrier constants `K(L)` and `σ(L,M)` are
  derived closed forms, in the pattern of `K_S` and `σ_C`. Rule 22: general in
  the transition, through the chord constants only.
* **Renovation item BJ3.1 (2026-10-07).** The carrier's semiconvexity and the
  increasing-differences step read `M_cx` and `M_mix`, which left the base class, so
  the general theorems are stated on `ChordEconomyTwoSided`; the family's forms are
  unchanged (`toChord` is a relief, hence a two-sided, economy).
-/
import Sanctions.Examples.PlacableSenderUniqueness

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 1. The policy carrier -/

/-- The policy carrier's Lipschitz constant `K(L) = L/(1 − β_S g_hi)`: the
Hinderer closed form at a Lipschitz constant `L` of the stage along the policy. -/
def KSpol (L : ℝ) : ℝ := L / (1 - E.β_S * E.ghi)

theorem KSpol_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ E.KSpol L :=
  div_nonneg hL E.one_sub_βS_ghi_pos.le

/-- The Hinderer identity `L + β_S·K(L)·g_hi = K(L)`. -/
theorem KSpol_fix (L : ℝ) : L + E.β_S * E.KSpol L * E.ghi = E.KSpol L := by
  have h := E.one_sub_βS_ghi_pos.ne'
  unfold KSpol
  field_simp
  ring

/-- A value of nonnegative lower slope is nondecreasing through the clip. -/
theorem clip_monotoneOn_of_lowerSlope (_E : ChordEconomy) {V : Val} {g : ℝ} (hg : 0 ≤ g)
    (hV : Params.LowerSlopeOnValueOn V (Icc (0 : ℝ) 1) g) :
    MonotoneOn (fun z => V (Sanctions.clipS' z)) (Icc (0 : ℝ) 1) := by
  intro z₁ hz₁ z₂ hz₂ hle
  have h := _E.clip_lowerSlope_of hV z₁ hz₁ z₂ hz₂ hle
  have := mul_nonneg hg (sub_nonneg.2 hle)
  change V (Sanctions.clipS' z₁) ≤ V (Sanctions.clipS' z₂)
  linarith

/-- A `K`-Lipschitz value is `K`-Lipschitz through the clip. -/
theorem clip_lip_of (_E : ChordEconomy) {V : Val} {K : ℝ} (hK : 0 ≤ K)
    (hV : Params.ValueLipschitzWith V K) :
    ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1,
      |V (Sanctions.clipS' z₁) - V (Sanctions.clipS' z₂)| ≤ K * |z₁ - z₂| := by
  intro z₁ _ z₂ _
  have h := hV (Sanctions.clipS' z₂) (Sanctions.clipS' z₁)
  have hd : dist (Sanctions.clipS' z₂) (Sanctions.clipS' z₁) ≤ |z₁ - z₂| := by
    have h2 := Sanctions.clipS'_lipschitz_dist z₂ z₁
    rwa [abs_sub_comm] at h2
  exact le_trans h (mul_le_mul_of_nonneg_left hd hK)

/-! ## 2. The Sender's Bellman operator at a policy -/

/-- The Sender Bellman image at a policy, at an attained argmax, with
sup-domination of every feasible sanction (the defiance form is
`bellmanS_spec`). -/
theorem bellmanS_spec_pol {α : ℝ → ℝ} (hα : Continuous α) (V : Val)
    (y : ↥(Sanctions.S : Set ℝ)) :
    ∃ sStar ∈ Sanctions.I,
      E.toParams.bellmanS_BCF α hα V y
        = E.U_S y.val (α y.val) sStar + E.β_S * V (Sanctions.clipS' (E.F y.val sStar))
      ∧ ∀ s ∈ Sanctions.I,
          E.U_S y.val (α y.val) s + E.β_S * V (Sanctions.clipS' (E.F y.val s))
          ≤ E.toParams.bellmanS_BCF α hα V y := by
  have hmax := E.toParams.σ_dyn_isMaxOn V y.val (α y.val)
  have hmem := E.toParams.σ_dyn_mem V y.val (α y.val)
  have heq := WitnessKit.bellmanS_image_of_isMaxOn (p := E.toParams) hα V y hmem hmax
  refine ⟨_, hmem, heq, ?_⟩
  intro s hs
  rw [heq]
  exact hmax hs

/-- The Bellman image at a policy, through the clip, is the greatest value of
the objective over the sanction interval. -/
theorem bellmanS_isGreatest_pol {α : ℝ → ℝ} (hα : Continuous α) (V : Val) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    IsGreatest
      ((fun s => E.U_S x (α x) s + E.β_S * V (Sanctions.clipS' (E.F x s))) '' Icc (0 : ℝ) 1)
      (E.toParams.bellmanS_BCF α hα V (Sanctions.clipS' x)) := by
  obtain ⟨sStar, hsI, heq, hdom⟩ := E.bellmanS_spec_pol hα V (Sanctions.clipS' x)
  have hval : (Sanctions.clipS' x).val = x := Sanctions.clipS'_val_eq_of_mem hx
  refine ⟨⟨sStar, hsI, ?_⟩, ?_⟩
  · rw [heq, hval]
  · rintro _ ⟨s, hs, rfl⟩
    have := hdom s hs
    rw [hval] at this
    exact this

/-- `g_S ≤ K(L)` whenever the stage along a nonincreasing policy is
`L`-Lipschitz: the lower chord at slope `g_S` between the states `0` and `1`
is at most `L + β_S·g_S·g_hi`. -/
theorem gS_le_KSpol (hN : E.ZeroSanctionAntitone) {α : ℝ → ℝ}
    (hanti : AntitoneOn α Sanctions.S) (hαmem : ∀ y ∈ Sanctions.S, α y ∈ Sanctions.I)
    {L : ℝ}
    (hUL : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |E.U_S x₂ (α x₂) s - E.U_S x₁ (α x₁) s| ≤ L * |x₂ - x₁|) :
    E.gS ≤ E.KSpol L := by
  have h0 : (0 : ℝ) ∈ Sanctions.I := zero_mem_I
  have h1 : (1 : ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_rfl⟩
  have hc := E.chord_of_antitone hN hanti hαmem 0 h0 0 h0 1 h1 zero_le_one
  have hU := (abs_le.mp (hUL 0 h0 1 h1 0 h0)).2
  have hband := (E.hbandAll 0 h0) 0 h0 1 h1 zero_le_one
  have hFhi : E.F 1 0 - E.F 0 0 ≤ E.ghi * (1 - 0) := hband.2
  have hβg := mul_nonneg E.hβS0.le E.gS_pos.le
  have hpos := E.one_sub_βS_ghi_pos
  have hcont := mul_le_mul_of_nonneg_left hFhi hβg
  have hkey : E.gS * (1 - E.β_S * E.ghi) ≤ L := by
    change E.gS * (1 - 0) ≤ (E.U_S 1 (α 1) 0 - E.U_S 0 (α 0) 0)
      + E.β_S * E.gS * (E.F 1 0 - E.F 0 0) at hc
    simp only [sub_zero, abs_one, mul_one] at hU
    nlinarith [hc, hU, hcont]
  unfold KSpol
  rw [le_div_iff₀ hpos]
  exact hkey

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-! ### The policy-class carrier, on the two-sided extension (renovation item BJ3.1)

The policy-class carrier's semiconvexity modulus `SigCpol` reads the transition's
state-section semiconvexity `M_cx`, and the increasing-differences step its mixed chord
`M_mix`, so since 2026-10-07 the declarations below are stated on `ChordEconomyTwoSided`;
until then they were on `ChordEconomy`, otherwise unchanged. Each is general in `F`. The
carrier itself (the rest of section 1) comes first, then its Bellman invariance (the rest
of section 2), then section 3. -/

/-- The policy carrier's semiconvexity modulus
`σ(L,M) = (M + β_S K(L) M_cx)/(1 − β_S g_hi²)`: the linear closure at a
semiconvexity modulus `M` of the stage along the policy. -/
def SigCpol (L M : ℝ) : ℝ := (M + E.β_S * E.KSpol L * E.Mcx) / (1 - E.β_S * E.ghi ^ 2)

theorem SigCpol_nonneg {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) : 0 ≤ E.SigCpol L M := by
  unfold SigCpol
  apply div_nonneg
  · have := mul_nonneg (mul_nonneg E.hβS0.le (E.KSpol_nonneg hL)) E.hMcx0
    linarith
  · linarith [E.βS_ghi_sq_lt_one]

/-- The linear closure `M + β_S(σ(L,M)·g_hi² + K(L)·M_cx) = σ(L,M)`. -/
theorem SigCpol_closure (L M : ℝ) :
    M + E.β_S * (E.SigCpol L M * E.ghi ^ 2 + E.KSpol L * E.Mcx) ≤ E.SigCpol L M := by
  have hpos : 0 < 1 - E.β_S * E.ghi ^ 2 := by linarith [E.βS_ghi_sq_lt_one]
  apply le_of_eq
  unfold SigCpol
  field_simp
  ring

/-- **The policy carrier**: lower slope `g_S` on `[0,1]`, `K(L)`-Lipschitz, and
`σ(L,M)`-semiconvex through the clip. There is no sup-norm clause and no
semiconcave clause; neither is read below. -/
def carrierPol (L M : ℝ) : Set Val :=
  {V : Val | Params.LowerSlopeOnValueOn V (Icc (0 : ℝ) 1) E.gS ∧
    Params.ValueLipschitzWith V (E.KSpol L) ∧
    SemiconvexOnSet (fun z => V (Sanctions.clipS' z)) (Icc (0 : ℝ) 1) (E.SigCpol L M)}

theorem carrierPol_isClosed (L M : ℝ) : IsClosed (E.carrierPol L M) := by
  unfold carrierPol
  exact (Params.lowerSlopeOnValueOn_isClosed _ _).inter
    ((Params.valueLipschitz_isClosed _).inter (semiconvexClause_isClosed _))

theorem carrierPol_nonempty {L M : ℝ} (hgL : E.gS ≤ E.KSpol L) (hσ : 0 ≤ E.SigCpol L M) :
    (E.carrierPol L M).Nonempty := by
  have h := SymbolicEconomyF.affineBCF_mem_gainBall_cone E.gS_pos.le hgL E.gS_le_MS
  exact ⟨affineBCF E.gS, h.2.2, h.2.1, affineBCF_clip_semiconvex hσ⟩

/-! ### The policy carrier under the Sender's Bellman operator at a policy

The rest of section 2, on the two-sided extension. -/

/-- **The policy carrier is Bellman-invariant at a nonincreasing policy** whose
stage is `L`-Lipschitz and `M`-semiconvex in the state, when a larger concession
is never worth more to the Sender in itself. -/
theorem bellmanS_pol_mem (hN : E.ZeroSanctionAntitone) {α : ℝ → ℝ} (hα : Continuous α)
    (hanti : AntitoneOn α Sanctions.S) (hαmem : ∀ y ∈ Sanctions.S, α y ∈ Sanctions.I)
    {L M : ℝ} (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hUL : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |E.U_S x₂ (α x₂) s - E.U_S x₁ (α x₁) s| ≤ L * |x₂ - x₁|)
    (hUM : ∀ s ∈ Icc (0 : ℝ) 1,
      SemiconvexOnSet (fun y => E.U_S y (α y) s) (Icc (0 : ℝ) 1) M)
    {V : Val} (hV : V ∈ E.carrierPol L M) :
    E.toParams.bellmanS_BCF α hα V ∈ E.carrierPol L M := by
  refine ⟨?_, ?_, ?_⟩
  · -- lower slope: the joint state chord at slope `g_S` along a nonincreasing policy
    exact E.toParams.bellmanS_BCF_preserves_lowerSlopeCone_generalF hα
      (E.chord_of_antitone hN hanti hαmem) hV.1
  · -- Lipschitz: the stage bound `L` and the state chord `g_hi`
    exact E.toParams.bellmanS_BCF_preserves_lipschitz_cone_on hα V (E.KSpol_nonneg hL0)
      hV.2.1 hUL
      (fun x₁ hx₁ x₂ hx₂ s hs => by
        have h := abs_sub_le_of_stateBand E.hglo0 (E.hbandAll s hs) hx₂ hx₁
        simp only at h
        exact h)
      (le_of_eq (E.KSpol_fix L))
  · -- semiconvexity: each state section, then the supremum
    have hK := E.KSpol_nonneg hL0
    have hσ := E.SigCpol_nonneg hL0 hM0
    have hsec : ∀ s ∈ Icc (0 : ℝ) 1,
        SemiconvexOnSet
          (fun x => E.U_S x (α x) s + E.β_S * V (Sanctions.clipS' (E.F x s)))
          (Icc (0 : ℝ) 1) (M + E.β_S * (E.SigCpol L M * E.ghi ^ 2 + E.KSpol L * E.Mcx)) := by
      intro s hs
      have hcomp := semiconvexOnSet_comp_of_stateChord
        (v := fun z => V (Sanctions.clipS' z)) (G := fun y => E.F y s)
        hσ hK E.hglo0 E.hMcx0
        (E.clip_monotoneOn_of_lowerSlope E.gS_pos.le hV.1) (E.clip_lip_of hK hV.2.1) hV.2.2
        (fun y hy => E.F_maps y hy s hs) (E.hbandAll s hs) (E.hFcx s hs)
      exact (hUM s hs).add (hcomp.const_mul E.hβS0.le)
    have hsup := sup_semiconvexOnSet
      (Φ := fun x s => E.U_S x (α x) s + E.β_S * V (Sanctions.clipS' (E.F x s)))
      (v := fun z => E.toParams.bellmanS_BCF α hα V (Sanctions.clipS' z))
      hsec (fun x hx => E.bellmanS_isGreatest_pol hα V hx)
    exact hsup.mono (E.SigCpol_closure L M)

/-- **The equilibrium Sender value lies in the policy carrier**: it is the
unique fixed point of the Sender's Bellman operator at the policy, and the
carrier is closed, nonempty and invariant. -/
theorem equilibrium_V_S_mem_carrierPol (hN : E.ZeroSanctionAntitone)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hanti : AntitoneOn Eq.α Sanctions.S)
    {L M : ℝ} (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hUL : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |E.U_S x₂ (Eq.α x₂) s - E.U_S x₁ (Eq.α x₁) s| ≤ L * |x₂ - x₁|)
    (hUM : ∀ s ∈ Icc (0 : ℝ) 1,
      SemiconvexOnSet (fun y => E.U_S y (Eq.α y) s) (Icc (0 : ℝ) 1) M) :
    Eq.V_S ∈ E.carrierPol L M := by
  have hcontr := E.toParams.bellmanS_BCF_contracting (α := Eq.α) Eq.hα
  obtain ⟨W, hW, hWmem⟩ := StokeyLucas.fixedPoint_mem_of_mapsTo hcontr.1 _ hcontr.2
    (E.carrierPol L M) (E.carrierPol_isClosed L M)
    (E.carrierPol_nonempty (E.gS_le_KSpol hN hanti Eq.α_mem hUL) (E.SigCpol_nonneg hL0 hM0))
    (fun V hV => E.bellmanS_pol_mem hN Eq.hα hanti Eq.α_mem hL0 hM0 hUL hUM hV)
  have h1 : W = hcontr.fixedPoint := hcontr.fixedPoint_unique hW
  have h2 : Eq.V_S = hcontr.fixedPoint := hcontr.fixedPoint_unique Eq.V_S_fix.symm
  rw [h2, ← h1]
  exact hWmem

/-! ## 3. Increasing differences at a fixed compliance, and the rule -/

/-- **Increasing differences of the Sender's objective at a fixed compliance**,
at every value of the policy carrier: the stage cross rate `ρ` at that
compliance covers the continuation's cross difference. -/
theorem senderObj_increasingDifferences_pol {L M ρ : ℝ} (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    {V : Val} (hV : V ∈ E.carrierPol L M) {a : ℝ}
    (hρ : ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ s' ∈ Icc (0 : ℝ) 1, x ≤ x' → s ≤ s' →
        ρ * ((x' - x) * (s' - s)) ≤ (E.U_S x' a s' - E.U_S x' a s) - (E.U_S x a s' - E.U_S x a s))
    (hmargin : E.β_S * (E.SigCpol L M * E.ghi * E.dhi
      + (E.KSpol L + 2 * E.SigCpol L M) * E.Mmix) ≤ ρ) :
    Sanctions.MilgromShannon.IncreasingDifferencesOn Sanctions.I Sanctions.S
      (fun s x => E.toParams.U_S x a s
        + E.toParams.β_S * V (Sanctions.clipS' (E.toParams.F x s))) := by
  intro s s' x x' hs hs' hss' hx hx' hxx'
  have hK := E.KSpol_nonneg hL0
  have hcont := crossDiff_comp_ge_of_semiconvex
    (v := fun z => V (Sanctions.clipS' z)) (F := E.F)
    (E.SigCpol_nonneg hL0 hM0) E.hglo0 E.hdlo0.le (E.clip_lip_of hK hV.2.1) hV.2.2
    E.F_maps E.hbandAll E.hSlo E.hShi E.hFmix hx hx' hs hs' hxx' hss'
  simp only at hcont
  have hstage := hρ x hx x' hx' s hs s' hs' hxx' hss'
  have hdx : 0 ≤ x' - x := by linarith
  have hds : 0 ≤ s' - s := by linarith
  have hP : 0 ≤ (x' - x) * (s' - s) := mul_nonneg hdx hds
  have h1 := mul_le_mul_of_nonneg_left hcont E.hβS0.le
  have h2 := mul_le_mul_of_nonneg_right hmargin hP
  change E.U_S x a s' + E.β_S * V (Sanctions.clipS' (E.F x s'))
      - (E.U_S x a s + E.β_S * V (Sanctions.clipS' (E.F x s)))
    ≤ E.U_S x' a s' + E.β_S * V (Sanctions.clipS' (E.F x' s'))
      - (E.U_S x' a s + E.β_S * V (Sanctions.clipS' (E.F x' s)))
  nlinarith [h1, h2, hstage]

/-- **Tier 2, general form: the realised rule is nondecreasing in the state**
at every equilibrium whose policy is nonincreasing, when the stage along the
policy is `L`-Lipschitz and `M`-semiconvex in the state, the stage has
increasing differences at rate `ρ` at every compliance level, and the margin
`β_S(σ(L,M)·g_hi·d_hi + (K(L) + 2σ(L,M))·M_mix) ≤ ρ` holds. -/
theorem rule_monotoneOn_of_policy_bounds (hN : E.ZeroSanctionAntitone)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hanti : AntitoneOn Eq.α Sanctions.S)
    {L M ρ : ℝ} (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hUL : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |E.U_S x₂ (Eq.α x₂) s - E.U_S x₁ (Eq.α x₁) s| ≤ L * |x₂ - x₁|)
    (hUM : ∀ s ∈ Icc (0 : ℝ) 1,
      SemiconvexOnSet (fun y => E.U_S y (Eq.α y) s) (Icc (0 : ℝ) 1) M)
    (hρ : ∀ a ∈ Sanctions.I, ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ s' ∈ Icc (0 : ℝ) 1, x ≤ x' → s ≤ s' →
        ρ * ((x' - x) * (s' - s)) ≤ (E.U_S x' a s' - E.U_S x' a s) - (E.U_S x a s' - E.U_S x a s))
    (hmargin : E.β_S * (E.SigCpol L M * E.ghi * E.dhi
      + (E.KSpol L + 2 * E.SigCpol L M) * E.Mmix) ≤ ρ) :
    MonotoneOn (E.rule Eq) Sanctions.S := by
  have hV := E.equilibrium_V_S_mem_carrierPol hN Eq hanti hL0 hM0 hUL hUM
  intro x₁ hx₁ x₂ hx₂ hle
  have ha₁ := Eq.α_mem x₁ hx₁
  have ha₂ := Eq.α_mem x₂ hx₂
  -- at the fixed compliance `α x₁`, the greatest response is nondecreasing in the state
  have hmono := E.toParams.σ_dyn_top_monotoneOn_x_of_singleCrossing' Eq.V_S (Eq.α x₁)
    (Sanctions.MilgromShannon.singleCrossingOn_of_increasingDifferencesOn
      (E.senderObj_increasingDifferences_pol hL0 hM0 hV (hρ (Eq.α x₁) ha₁) hmargin))
  have h1 : E.toParams.σ_dyn_top Eq.V_S x₁ (Eq.α x₁) ≤ E.toParams.σ_dyn_top Eq.V_S x₂ (Eq.α x₁) :=
    hmono hx₁ hx₂ hle
  -- at the state `x₂`, the greatest response is nonincreasing in compliance
  have hanti_a := E.toParams.σ_dyn_top_antitoneOn_a_of_DD Eq.V_S x₂
    (E.stage_decreasingDifferences x₂ hx₂)
  have h2 : E.toParams.σ_dyn_top Eq.V_S x₂ (Eq.α x₁) ≤ E.toParams.σ_dyn_top Eq.V_S x₂ (Eq.α x₂) :=
    hanti_a ha₂ ha₁ (hanti hx₁ hx₂ hle)
  change E.toParams.σ_dyn_top Eq.V_S x₁ (Eq.α x₁) ≤ E.toParams.σ_dyn_top Eq.V_S x₂ (Eq.α x₂)
  exact h1.trans h2

/-- **Tier 2 composed with round AR, general form**: under the unrefined
loss-offset margin, every equilibrium of the policy class is the constructed
defiance equilibrium. -/
theorem unique_equilibrium_of_policy_bounds (hTM : E.LossOffset₀) (hN : E.ZeroSanctionAntitone)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hanti : AntitoneOn Eq.α Sanctions.S)
    {L M ρ : ℝ} (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hUL : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |E.U_S x₂ (Eq.α x₂) s - E.U_S x₁ (Eq.α x₁) s| ≤ L * |x₂ - x₁|)
    (hUM : ∀ s ∈ Icc (0 : ℝ) 1,
      SemiconvexOnSet (fun y => E.U_S y (Eq.α y) s) (Icc (0 : ℝ) 1) M)
    (hρ : ∀ a ∈ Sanctions.I, ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ s' ∈ Icc (0 : ℝ) 1, x ≤ x' → s ≤ s' →
        ρ * ((x' - x) * (s' - s)) ≤ (E.U_S x' a s' - E.U_S x' a s) - (E.U_S x a s' - E.U_S x a s))
    (hmargin : E.β_S * (E.SigCpol L M * E.ghi * E.dhi
      + (E.KSpol L + 2 * E.SigCpol L M) * E.Mmix) ≤ ρ) :
    (∀ x ∈ Sanctions.I, Eq.α x = 0) ∧ Eq.V_S = E.VSstar ∧ Eq.V_T = E.VTdef ∧
    ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = E.responsePath E.VSstar x :=
  E.unique_equilibrium_of_monotone_class hTM Eq hanti
    (E.rule_monotoneOn_of_policy_bounds hN Eq hanti hL0 hM0 hUL hUM hρ hmargin)

end ChordEconomyTwoSided

/-! ## 4. The quadratic–linear family: the class stated on the policy alone -/

namespace PlacableEconomyF

variable (E : PlacableEconomyF)

/-- On the family, the stage along an `L_α`-Lipschitz policy is
`(r + w + k·L_α)`-Lipschitz in the state at every sanction in `[0,1]`. -/
theorem stage_policy_lipschitz {α : ℝ → ℝ} {Lα : ℝ}
    (hlip : ∀ y₁ ∈ Sanctions.I, ∀ y₂ ∈ Sanctions.I, |α y₂ - α y₁| ≤ Lα * |y₂ - y₁|) :
    ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |E.toChord.U_S x₂ (α x₂) s - E.toChord.U_S x₁ (α x₁) s|
        ≤ (E.r + E.w + E.k * Lα) * |x₂ - x₁| := by
  intro x₁ hx₁ x₂ hx₂ s hs
  have hα := hlip x₁ hx₁ x₂ hx₂
  have hd := abs_nonneg (x₂ - x₁)
  have hid : E.toChord.U_S x₂ (α x₂) s - E.toChord.U_S x₁ (α x₁) s
      = s * (E.r * (x₂ - x₁)) - (E.k * s) * (α x₂ - α x₁) + E.w * (x₂ - x₁) := by
    change symU_S E.q E.u₀ E.k E.r E.w x₂ (α x₂) s - symU_S E.q E.u₀ E.k E.r E.w x₁ (α x₁) s = _
    unfold symU_S
    ring
  rw [hid]
  have hks : 0 ≤ E.k * s := mul_nonneg E.hk.le hs.1
  have h1 : |s * (E.r * (x₂ - x₁))| ≤ E.r * |x₂ - x₁| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hs.1, abs_of_nonneg E.hr]
    have := mul_le_mul_of_nonneg_right hs.2 (mul_nonneg E.hr hd)
    linarith
  have h2 : |(E.k * s) * (α x₂ - α x₁)| ≤ E.k * (Lα * |x₂ - x₁|) := by
    rw [abs_mul, abs_of_nonneg hks]
    have hks1 : E.k * s ≤ E.k := by
      have := mul_le_mul_of_nonneg_left hs.2 E.hk.le
      linarith
    have hLd : 0 ≤ Lα * |x₂ - x₁| := le_trans (abs_nonneg _) hα
    calc E.k * s * |α x₂ - α x₁| ≤ E.k * s * (Lα * |x₂ - x₁|) :=
          mul_le_mul_of_nonneg_left hα hks
      _ ≤ E.k * (Lα * |x₂ - x₁|) := mul_le_mul_of_nonneg_right hks1 hLd
  have h3 : |E.w * (x₂ - x₁)| = E.w * |x₂ - x₁| := by
    rw [abs_mul, abs_of_pos E.hw]
  calc |s * (E.r * (x₂ - x₁)) - (E.k * s) * (α x₂ - α x₁) + E.w * (x₂ - x₁)|
      ≤ |s * (E.r * (x₂ - x₁))| + |(E.k * s) * (α x₂ - α x₁)| + |E.w * (x₂ - x₁)| := by
        have := abs_add_le (s * (E.r * (x₂ - x₁)) - (E.k * s) * (α x₂ - α x₁)) (E.w * (x₂ - x₁))
        have := abs_sub (s * (E.r * (x₂ - x₁))) ((E.k * s) * (α x₂ - α x₁))
        linarith
    _ ≤ E.r * |x₂ - x₁| + E.k * (Lα * |x₂ - x₁|) + E.w * |x₂ - x₁| := by linarith
    _ = (E.r + E.w + E.k * Lα) * |x₂ - x₁| := by ring

/-- On the family, the stage along an `M_α`-semiconcave policy is
`k·M_α`-semiconvex in the state at every sanction in `[0,1]`: the placation
term is `−k·s·α(y)` and the rest is affine in the state. -/
theorem stage_policy_semiconvex {α : ℝ → ℝ} {Mα : ℝ} (hMα : 0 ≤ Mα)
    (hsc : SemiconcaveOnSet α (Icc (0 : ℝ) 1) Mα) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      SemiconvexOnSet (fun y => E.toChord.U_S y (α y) s) (Icc (0 : ℝ) 1) (E.k * Mα) := by
  intro s hs y₁ hy₁ y₂ hy₂ t ht0 ht1
  have hα := hsc y₁ hy₁ y₂ hy₂ t ht0 ht1
  have hid : E.toChord.U_S (t * y₁ + (1 - t) * y₂) (α (t * y₁ + (1 - t) * y₂)) s
      - (t * E.toChord.U_S y₁ (α y₁) s + (1 - t) * E.toChord.U_S y₂ (α y₂) s)
      = (E.k * s) * (t * α y₁ + (1 - t) * α y₂ - α (t * y₁ + (1 - t) * y₂)) := by
    change symU_S E.q E.u₀ E.k E.r E.w (t * y₁ + (1 - t) * y₂) (α (t * y₁ + (1 - t) * y₂)) s
      - (t * symU_S E.q E.u₀ E.k E.r E.w y₁ (α y₁) s
        + (1 - t) * symU_S E.q E.u₀ E.k E.r E.w y₂ (α y₂) s) = _
    unfold symU_S
    ring
  simp only
  rw [hid]
  have hks : 0 ≤ E.k * s := mul_nonneg E.hk.le hs.1
  have hks1 : E.k * s ≤ E.k := by
    have := mul_le_mul_of_nonneg_left hs.2 E.hk.le
    linarith
  have hP : 0 ≤ t * (1 - t) * (y₁ - y₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  have hB : 0 ≤ Mα / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2) :=
    mul_nonneg (by linarith) hP
  calc E.k * s * (t * α y₁ + (1 - t) * α y₂ - α (t * y₁ + (1 - t) * y₂))
      ≤ E.k * s * (Mα / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2)) :=
        mul_le_mul_of_nonneg_left hα hks
    _ ≤ E.k * (Mα / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2)) :=
        mul_le_mul_of_nonneg_right hks1 hB
    _ = E.k * Mα / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2) := by ring

/-- On the family, the stage cross rate in (sanction; state) is exactly `r` at
every compliance level. -/
theorem stage_crossRate_eq (a : ℝ) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      x ≤ x' → s ≤ s' →
        E.r * ((x' - x) * (s' - s))
          ≤ (E.toChord.U_S x' a s' - E.toChord.U_S x' a s)
            - (E.toChord.U_S x a s' - E.toChord.U_S x a s) := by
  intro x _ x' _ s _ s' _ _ _
  apply le_of_eq
  change E.r * ((x' - x) * (s' - s))
    = (symU_S E.q E.u₀ E.k E.r E.w x' a s' - symU_S E.q E.u₀ E.k E.r E.w x' a s)
      - (symU_S E.q E.u₀ E.k E.r E.w x a s' - symU_S E.q E.u₀ E.k E.r E.w x a s)
  unfold symU_S
  ring

/-- `L_α ≥ 0` for any `L_α`-Lipschitz policy on `[0,1]`. -/
theorem Lα_nonneg_of_lipschitz {α : ℝ → ℝ} {Lα : ℝ}
    (hlip : ∀ y₁ ∈ Sanctions.I, ∀ y₂ ∈ Sanctions.I, |α y₂ - α y₁| ≤ Lα * |y₂ - y₁|) :
    0 ≤ Lα := by
  have h := hlip 0 ChordEconomy.zero_mem_I 1 ⟨zero_le_one, le_rfl⟩
  simp only [sub_zero, abs_one, mul_one] at h
  exact le_trans (abs_nonneg _) h

/-- **Tier 2 on the quadratic–linear family.** Every equilibrium whose policy is
(i) nonincreasing, (ii) `L_α`-Lipschitz and (iii) `M_α`-semiconcave on
`[0,1]` has a realised sanction rule that is nondecreasing in the state, given
(iv) the margin `β_S(σ'·g_hi·d_hi + (K' + 2σ')·M_mix) ≤ r` at
`K' = (r + w + k L_α)/(1 − β_S g_hi)` and
`σ' = (k M_α + β_S K' M_cx)/(1 − β_S g_hi²)`. -/
theorem rule_monotoneOn_of_concave_policy
    (Eq : E.toChord.toParams.FeedbackStackelbergEquilibriumTop)
    (hanti : AntitoneOn Eq.α Sanctions.S) {Lα Mα : ℝ} (hMα : 0 ≤ Mα)
    (hlip : ∀ y₁ ∈ Sanctions.I, ∀ y₂ ∈ Sanctions.I, |Eq.α y₂ - Eq.α y₁| ≤ Lα * |y₂ - y₁|)
    (hsc : SemiconcaveOnSet Eq.α (Icc (0 : ℝ) 1) Mα)
    (hmargin : E.βS * (E.toChord.SigCpol (E.r + E.w + E.k * Lα) (E.k * Mα) * E.ghi * E.dhi
      + (E.toChord.KSpol (E.r + E.w + E.k * Lα)
        + 2 * E.toChord.SigCpol (E.r + E.w + E.k * Lα) (E.k * Mα)) * E.Mmix) ≤ E.r) :
    MonotoneOn (E.toChord.rule Eq) Sanctions.S := by
  have hLα := Lα_nonneg_of_lipschitz hlip
  have hL0 : 0 ≤ E.r + E.w + E.k * Lα := by
    have := mul_nonneg E.hk.le hLα
    linarith [E.hr, E.hw]
  exact E.toChord.rule_monotoneOn_of_policy_bounds E.toChord_zeroSanctionNeutral.antitone Eq
    hanti hL0 (mul_nonneg E.hk.le hMα) (E.stage_policy_lipschitz hlip)
    (E.stage_policy_semiconvex hMα hsc) (fun a _ => E.stage_crossRate_eq a) hmargin

/-- **Tier 2 composed with round AR, on the family**: under the unrefined
loss-offset margin, every equilibrium whose policy is nonincreasing, Lipschitz
and semiconcave (with the margin (iv)) is the constructed defiance equilibrium:
full defiance at every feasible state, the constructed Sender and Target values,
and the constructed response as its rule. -/
theorem unique_equilibrium_of_concave_policy (hTM : E.toChord.LossOffset₀)
    (Eq : E.toChord.toParams.FeedbackStackelbergEquilibriumTop)
    (hanti : AntitoneOn Eq.α Sanctions.S) {Lα Mα : ℝ} (hMα : 0 ≤ Mα)
    (hlip : ∀ y₁ ∈ Sanctions.I, ∀ y₂ ∈ Sanctions.I, |Eq.α y₂ - Eq.α y₁| ≤ Lα * |y₂ - y₁|)
    (hsc : SemiconcaveOnSet Eq.α (Icc (0 : ℝ) 1) Mα)
    (hmargin : E.βS * (E.toChord.SigCpol (E.r + E.w + E.k * Lα) (E.k * Mα) * E.ghi * E.dhi
      + (E.toChord.KSpol (E.r + E.w + E.k * Lα)
        + 2 * E.toChord.SigCpol (E.r + E.w + E.k * Lα) (E.k * Mα)) * E.Mmix) ≤ E.r) :
    (∀ x ∈ Sanctions.I, Eq.α x = 0) ∧ Eq.V_S = E.toChord.VSstar ∧ Eq.V_T = E.toChord.VTdef ∧
    ∀ x ∈ Sanctions.I, E.toChord.toParams.dynamicEquilibriumRule Eq x
      = E.toChord.responsePath E.toChord.VSstar x :=
  E.toChord.unique_equilibrium_of_monotone_class hTM Eq hanti
    (E.rule_monotoneOn_of_concave_policy Eq hanti hMα hlip hsc hmargin)

/-- **The flat case**: with convex state sections and no cross-curvature in the
transition (`M_cx = M_mix = 0`), every equilibrium whose policy is
nonincreasing, Lipschitz and concave is, under the unrefined loss-offset margin,
the constructed defiance equilibrium. The margin (iv) reads `0 ≤ r`. -/
theorem unique_equilibrium_of_concave_policy_flat (hMcx : E.Mcx = 0) (hMmix : E.Mmix = 0)
    (hTM : E.toChord.LossOffset₀)
    (Eq : E.toChord.toParams.FeedbackStackelbergEquilibriumTop)
    (hanti : AntitoneOn Eq.α Sanctions.S) {Lα : ℝ}
    (hlip : ∀ y₁ ∈ Sanctions.I, ∀ y₂ ∈ Sanctions.I, |Eq.α y₂ - Eq.α y₁| ≤ Lα * |y₂ - y₁|)
    (hcc : SemiconcaveOnSet Eq.α (Icc (0 : ℝ) 1) 0) :
    (∀ x ∈ Sanctions.I, Eq.α x = 0) ∧ Eq.V_S = E.toChord.VSstar ∧ Eq.V_T = E.toChord.VTdef ∧
    ∀ x ∈ Sanctions.I, E.toChord.toParams.dynamicEquilibriumRule Eq x
      = E.toChord.responsePath E.toChord.VSstar x := by
  refine E.unique_equilibrium_of_concave_policy hTM Eq hanti le_rfl hlip hcc ?_
  have hS : E.toChord.SigCpol (E.r + E.w + E.k * Lα) (E.k * 0) = 0 := by
    unfold ChordEconomyTwoSided.SigCpol
    have : E.toChord.Mcx = 0 := hMcx
    rw [this]
    simp
  rw [hS, hMmix]
  simpa using E.hr

/-- **The class is inhabited (Rule 9B)**: at the constructed defiance
equilibrium (under the loss-offset margin and the rally margin) the policy is
constant, hence nonincreasing, `0`-Lipschitz and `0`-semiconcave, and the margin
(iv) at `L_α = M_α = 0` is the rally margin. -/
theorem equilibriumTop_mem_concave_policy_class (hTM : E.toChord.LossOffset)
    (hmargin : E.toChord.β_S * (E.toChord.SigC * E.toChord.ghi * E.toChord.dhi
      + (E.toChord.KS + 2 * E.toChord.SigC) * E.toChord.Mmix) ≤ E.toChord.rlo) :
    AntitoneOn (E.toChord.equilibriumTop_of_margin hTM hmargin).α Sanctions.S ∧
    (∀ y₁ ∈ Sanctions.I, ∀ y₂ ∈ Sanctions.I,
      |(E.toChord.equilibriumTop_of_margin hTM hmargin).α y₂
        - (E.toChord.equilibriumTop_of_margin hTM hmargin).α y₁| ≤ 0 * |y₂ - y₁|) ∧
    SemiconcaveOnSet (E.toChord.equilibriumTop_of_margin hTM hmargin).α (Icc (0 : ℝ) 1) 0 ∧
    E.βS * (E.toChord.SigCpol (E.r + E.w + E.k * 0) (E.k * 0) * E.ghi * E.dhi
      + (E.toChord.KSpol (E.r + E.w + E.k * 0)
        + 2 * E.toChord.SigCpol (E.r + E.w + E.k * 0) (E.k * 0)) * E.Mmix) ≤ E.r := by
  refine ⟨fun _ _ _ _ _ => le_rfl, fun y₁ _ y₂ _ => ?_, ?_, ?_⟩
  · change |(0 : ℝ) - 0| ≤ 0 * |y₂ - y₁|
    simp
  · intro y₁ _ y₂ _ t _ _
    change t * 0 + (1 - t) * 0 - 0 ≤ 0 / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2)
    simp
  · have hK : E.toChord.KSpol (E.r + E.w + E.k * 0) = E.toChord.KS := by
      unfold ChordEconomy.KSpol ChordEconomy.KS chKS
      simp only [mul_zero, add_zero]
      rfl
    have hS : E.toChord.SigCpol (E.r + E.w + E.k * 0) (E.k * 0) = E.toChord.SigC := by
      unfold ChordEconomyTwoSided.SigCpol ChordEconomyTwoSided.SigC chSigC
      rw [hK]
      simp only [mul_zero]
      rfl
    rw [hK, hS]
    exact hmargin

end PlacableEconomyF

/-! ## 5. Rule 10 -/

end

#print axioms Sanctions.Examples.ChordEconomyTwoSided.equilibrium_V_S_mem_carrierPol
#print axioms Sanctions.Examples.ChordEconomyTwoSided.rule_monotoneOn_of_policy_bounds
#print axioms Sanctions.Examples.ChordEconomyTwoSided.unique_equilibrium_of_policy_bounds
#print axioms Sanctions.Examples.PlacableEconomyF.rule_monotoneOn_of_concave_policy
#print axioms Sanctions.Examples.PlacableEconomyF.unique_equilibrium_of_concave_policy
#print axioms Sanctions.Examples.PlacableEconomyF.unique_equilibrium_of_concave_policy_flat
#print axioms Sanctions.Examples.PlacableEconomyF.equilibriumTop_mem_concave_policy_class

end Examples
end Sanctions
