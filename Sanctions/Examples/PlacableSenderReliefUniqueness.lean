/-
Sanctions/Examples/PlacableSenderReliefUniqueness.lean

**Uniqueness on the relief side, in the carrier class** (round AV, 2026-09-25;
doc 104, sign-off M9: the open item of 2026-09-25, proved with the class
restriction the open-items report stated).

## What is proved

On the relief side of the bracket — placability, `β_T·γ_T < 1` and
`ℓ_hi·M_tot < k_lo(p_lo − β_T d_hi K_T)` — and under zero-sanction neutrality,
every top-selector feedback Stackelberg equilibrium whose Sender value lies in
the two-sided Sender carrier (`carrierS2`: bounded, `K_S`-Lipschitz, lower slope
`g_S`, `SigV`-semiconcave and `SigC`-semiconvex through the clip) is the relief
equilibrium. The Target complies at the zero level `a*(x)` at every state, the
realised sanction is zero, the Sender's value is `VS01` and the Target's is
`VTrel` (`unique_equilibrium_of_relief_side`). Together with the existence
theorem `reliefEquilibriumTop` (which reads the `K_T^rel` form of the relief
inequality), the relief equilibrium is the only equilibrium of the class
(`reliefEquilibriumTop_unique_in_carrier_class`), witnessed off the affine law
at the `quadDiagF` member (`placableQuadDiagLo_relief_unique_in_carrier_class`).

A smaller statement needs no class and no relief inequality, only placability
and neutrality: every equilibrium whose realised sanction is zero at every state
is the relief equilibrium (`relief_equilibrium_of_zero_rule`).

## The argument

1. **The equilibrium Target value is `K_T`-Lipschitz** whenever the Sender's
   value is in the carrier (`equilibrium_V_T_lipschitz_of_carrier`). Let `D` be
   the largest excess of `V_T(y₂) − V_T(y₁)` over `K_T·|y₂ − y₁|`. Compare the
   Target's optimum at `y₂` with the same compliance `α(y₂)` played at `y₁`:
   optimality is used at both states, so no regularity of the policy is needed.
   The stage moves by at most `L_U·|Δy|` and the successor by at most
   `γ_T·|Δy|`, so the excess is at most `β_T·D`. Hence `D ≤ β_T·D`, and `D ≤ 0`.
2. **At every state the policy is the zero level at the equilibrium's own
   Sender value** (`policy_eq_zeroLevelAt_of_carrier`). Above the zero level,
   compliance buys nothing and costs at least `ℓ_lo` per unit. Below it, raising
   compliance to the zero level avoids a sanction of at least
   `k_lo(a* − a)/M_tot`. Each unit of that sanction is worth at least
   `p_lo − β_T d_hi K_T` net of the continuation (step 1), against a compliance
   cost of at most `ℓ_hi(a* − a)`, so the raise is strictly profitable under the
   relief inequality.
3. **So the realised sanction is zero.** The Sender's value is then the fixed
   point of the zero-sanction operator (`VS01`, by neutrality), and the Target's
   is the fixed point of the relief operator (`VTrel`).

## Scope

* **The class.** The restriction falls on an endogenous object, the
  equilibrium's Sender value, in the way round AR's monotone class restricts the
  policy and the rule. It cannot be AR's class: at the relief equilibrium the
  Target's compliance is the zero level, which rose with the state at the member
  probed on 2026-09-25. That is a numerical observation at one member (Rule 9A),
  not a theorem. Whether the relief side has equilibria whose Sender value lies
  outside the carrier is not settled here. The restriction is not shown to be
  removable, and no refutation of its removability is claimed (Rule 11).
* **The two relief inequalities.** Existence reads the `K_T^rel` form, because
  the constructed Target value's Lipschitz constant uses the zero level's. This
  uniqueness reads the `K_T` form, because an arbitrary equilibrium's Target value
  can only be certified `K_T`-Lipschitz before its policy is known. The corollary
  takes both, and both hold at the members of `PlacableSenderBracketWitnesses`.
* **Rule 3.** No field. The class `Eq.V_S ∈ carrierS2` is a hypothesis on the
  quantified equilibrium, approved with sign-off M9; zero-sanction neutrality is
  a hypothesis of the relief-side theorems only (sign-off M2). Rule 22: general
  in the transition, through the chord constants only.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation item BH3.11 (2026-10-06). Step 1's ingredients and its Lipschitz theorem
(`targetStage_lipschitz_at`, `successor_lipschitz_at`,
`equilibrium_V_T_lipschitz_of_carrier`) are stated on `ChordEconomyRelief`: none of them
reads the semiconvexity of `F`'s sanction section that `ChordEconomyCs` adds. So the
Target value of every equilibrium of the relief class whose Sender value lies in the
two-sided carrier is `K_T`-Lipschitz under `β_T·γ_T < 1` alone. At every full-defiance
equilibrium the two halves of the continuation bracket hold with only what each reads
(`V_T_continuation_upper_of_policy_zero`, `V_T_continuation_lower_of_policy_zero`, through
`values_eq_of_policy_zero`, which is why `PlacableSenderDefianceValues` is imported).
-/
import Sanctions.Examples.PlacableSenderBracketWitnesses
import Sanctions.Examples.PlacableSenderDefianceValues

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave

noncomputable section

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-! ## 1. Stage and successor along the response at a carrier value

Renovation item BH3.11(a) (2026-10-06): sections 1 and 2 are stated on the relief extension
`ChordEconomyRelief`, verbatim. Until then they were on `ChordEconomyCs`, but none of them
reads `Mcs`, `hMcs0` or `hFcs`, the semiconvexity of `F`'s sanction section; callers on
`ChordEconomyCs` reach them through the parent structure. -/

/-- **The Target's stage payoff at a fixed compliance and the response to a
two-sided carrier value is `L_U`-Lipschitz in the state** (the defiance form at
`VSstar` is `targetStage_lipschitz`). On `ChordEconomyRelief` since BH3.11(a): the
sanction-section semiconvexity of `ChordEconomyCs` is not read. General in `F`. -/
theorem targetStage_lipschitz_at {V : Val} (hV : V ∈ E.carrierS2) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) {y₁ y₂ : ℝ} (hy₁ : y₁ ∈ Icc (0 : ℝ) 1)
    (hy₂ : y₂ ∈ Icc (0 : ℝ) 1) :
    |E.U_T y₂ a (E.response V y₂ a) - E.U_T y₁ a (E.response V y₁ a)|
      ≤ E.LUT * |y₂ - y₁| := by
  set R₁ := E.response V y₁ a with hR₁
  set R₂ := E.response V y₂ a with hR₂
  have hR₁m : R₁ ∈ Icc (0 : ℝ) 1 := E.response_mem V y₁ a
  have hR₂m : R₂ ∈ Icc (0 : ℝ) 1 := E.response_mem V y₂ a
  have hRL : |R₂ - R₁| ≤ E.Lresp * |y₂ - y₁| / E.mu := E.response_dist_le_state hV hy₂ hy₁ ha
  -- the sanction leg (T4, T5): pain at most `c` per unit
  have hs := E.UT_sanction_lip hy₂ ha hR₁m hR₂m
  -- the state leg (T7) at the sanction `R₁`
  have hx := E.hUT_stateHi a ha R₁ hR₁m y₁ hy₁ y₂ hy₂
  have hrate := E.vhi_rate_le_max hR₁m
  have hmu := E.mu_pos
  have hx' : |E.U_T y₂ a R₁ - E.U_T y₁ a R₁| ≤ max E.vhi (E.vhi + E.nhi) * |y₂ - y₁| :=
    hx.trans (mul_le_mul_of_nonneg_right hrate (abs_nonneg _))
  have hs' : |E.U_T y₂ a R₂ - E.U_T y₂ a R₁| ≤ E.c * (E.Lresp * |y₂ - y₁| / E.mu) :=
    hs.trans (mul_le_mul_of_nonneg_left hRL E.c_pos.le)
  calc |E.U_T y₂ a R₂ - E.U_T y₁ a R₁|
      = |(E.U_T y₂ a R₂ - E.U_T y₂ a R₁) + (E.U_T y₂ a R₁ - E.U_T y₁ a R₁)| := by ring_nf
    _ ≤ |E.U_T y₂ a R₂ - E.U_T y₂ a R₁| + |E.U_T y₂ a R₁ - E.U_T y₁ a R₁| := abs_add_le _ _
    _ ≤ E.c * (E.Lresp * |y₂ - y₁| / E.mu) + max E.vhi (E.vhi + E.nhi) * |y₂ - y₁| :=
        add_le_add hs' hx'
    _ = E.LUT * |y₂ - y₁| := by unfold LUT; field_simp; ring

/-- **The realised successor at a fixed compliance is `γ_T`-Lipschitz in the
state**, at every two-sided carrier value (the defiance form at `VSstar` is
`successor_lipschitz_sharp`). On `ChordEconomyRelief` since BH3.11(a): the
sanction-section semiconvexity of `ChordEconomyCs` is not read. General in `F`. -/
theorem successor_lipschitz_at {V : Val} (hV : V ∈ E.carrierS2) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |E.F x (E.response V x a) - E.F y (E.response V y a)| ≤ E.LloopSharp * |x - y| := by
  have hρx := E.response_mem V x a
  have hρy := E.response_mem V y a
  have hstate := abs_sub_le_of_stateBand E.hglo0 (E.hbandAll _ hρx) hx hy
  simp only at hstate
  have hsanc := abs_sub_le_of_sanctionChords E.hdlo0.le E.hSlo E.hShi hy hρx hρy
  have hρ := E.response_dist_le_state hV hx hy ha
  have htri := abs_sub_le (E.F x (E.response V x a)) (E.F y (E.response V x a))
    (E.F y (E.response V y a))
  have hmu := E.mu_pos
  have hρ' : E.dhi * |E.response V x a - E.response V y a|
      ≤ E.dhi * (E.Lresp / E.mu * |x - y|) := by
    apply mul_le_mul_of_nonneg_left _ E.dhi_nonneg
    calc |E.response V x a - E.response V y a|
        ≤ (E.Lresp * |x - y|) / E.mu := hρ
      _ = E.Lresp / E.mu * |x - y| := by ring
  unfold LloopSharp
  nlinarith [htri, hstate, hsanc, hρ']

/-! ## 2. The equilibrium Target value is `K_T`-Lipschitz -/

/-- **An equilibrium's Target value is `K_T`-Lipschitz whenever its Sender value
is in the two-sided carrier**, given `β_T·γ_T < 1`. The supremum argument:
optimality at both states, compared at the same compliance, so no regularity of
the policy is used. On `ChordEconomyRelief` since BH3.11(a) (2026-10-06): the
sanction-section semiconvexity of `ChordEconomyCs` is not read, so the Lipschitz clause
holds at every equilibrium of the relief class whose Sender value lies in the carrier,
with no loss-offset margin and no monotone response. General in `F`. -/
theorem equilibrium_V_T_lipschitz_of_carrier (hγ : E.β_T * E.LloopSharp < 1)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hVS : Eq.V_S ∈ E.carrierS2) :
    Params.ValueLipschitzWith Eq.V_T E.KT := by
  have hK := E.KT_nonneg hγ
  set Ex : Set ℝ := Set.range (fun p : ↥(Sanctions.S : Set ℝ) × ↥(Sanctions.S : Set ℝ) =>
    Eq.V_T p.2 - Eq.V_T p.1 - E.KT * |p.2.val - p.1.val|) with hEx
  have hbdd : BddAbove Ex := by
    refine ⟨2 * ‖Eq.V_T‖, ?_⟩
    rintro _ ⟨⟨y₁, y₂⟩, rfl⟩
    have h1 := BoundedContinuousFunction.norm_coe_le_norm Eq.V_T y₁
    have h2 := BoundedContinuousFunction.norm_coe_le_norm Eq.V_T y₂
    rw [Real.norm_eq_abs] at h1 h2
    have h3 := mul_nonneg hK (abs_nonneg (y₂.val - y₁.val))
    have h4 := abs_le.mp h1
    have h5 := abs_le.mp h2
    change Eq.V_T y₂ - Eq.V_T y₁ - E.KT * |y₂.val - y₁.val| ≤ 2 * ‖Eq.V_T‖
    linarith
  have hne : Ex.Nonempty := ⟨_, ⟨(⟨0, zero_mem_I⟩, ⟨0, zero_mem_I⟩), rfl⟩⟩
  set D := sSup Ex with hD
  have hle : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
      Eq.V_T y₂ - Eq.V_T y₁ - E.KT * |y₂.val - y₁.val| ≤ D :=
    fun y₁ y₂ => le_csSup hbdd ⟨(y₁, y₂), rfl⟩
  have hβ := E.hβT0.le
  have hstep : ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
      Eq.V_T y₂ - Eq.V_T y₁ - E.KT * |y₂.val - y₁.val| ≤ E.β_T * D := by
    intro y₁ y₂
    have hy₁ := y₁.property
    have hy₂ := y₂.property
    have haI : Eq.α y₂.val ∈ Sanctions.I := Eq.α_mem y₂.val hy₂
    -- the Target's value at `y₂` is attained at its own compliance
    have h2 := Params.FeedbackStackelbergEquilibriumTop.V_T_eq_at_policy _ Eq y₂
    -- the same compliance at `y₁` is feasible there, hence no better than the optimum
    have h1 : E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S y₁.val (Eq.α y₂.val)
        ≤ Eq.V_T y₁ := by
      rw [Params.FeedbackStackelbergEquilibriumTop.V_T_eq_at_policy _ Eq y₁]
      exact (isMaxOn_iff.mp (Eq.α_opt_top y₁.val hy₁)) _ haI
    rw [E.joint_T_top_integrand_eq hVS.1 _ hy₂, joint_T_integrand_eq] at h2
    rw [E.joint_T_top_integrand_eq hVS.1 _ hy₁, joint_T_integrand_eq] at h1
    set R₁ := E.response Eq.V_S y₁.val (Eq.α y₂.val) with hR₁
    set R₂ := E.response Eq.V_S y₂.val (Eq.α y₂.val) with hR₂
    have hF₁ : E.F y₁.val R₁ ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hy₁ (E.response_mem _ _ _)
    have hF₂ : E.F y₂.val R₂ ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hy₂ (E.response_mem _ _ _)
    have hstage := E.targetStage_lipschitz_at hVS haI hy₁ hy₂
    have hsucc := E.successor_lipschitz_at hVS haI hy₂ hy₁
    have hcont := hle (Sanctions.clipS' (E.F y₁.val R₁)) (Sanctions.clipS' (E.F y₂.val R₂))
    rw [Sanctions.clipS'_val_eq_of_mem hF₁, Sanctions.clipS'_val_eq_of_mem hF₂] at hcont
    have hK' : E.KT * |E.F y₂.val R₂ - E.F y₁.val R₁|
        ≤ E.KT * (E.LloopSharp * |y₂.val - y₁.val|) :=
      mul_le_mul_of_nonneg_left hsucc hK
    have hfix := E.KT_fix hγ
    have habs := (abs_le.mp hstage).2
    have hA : Eq.V_T y₂ - Eq.V_T y₁
        ≤ (E.U_T y₂.val (Eq.α y₂.val) R₂ - E.U_T y₁.val (Eq.α y₂.val) R₁)
          + E.β_T * (Eq.V_T (Sanctions.clipS' (E.F y₂.val R₂))
            - Eq.V_T (Sanctions.clipS' (E.F y₁.val R₁))) := by
      change Eq.V_T y₂ = E.U_T y₂.val (Eq.α y₂.val) R₂
        + E.β_T * Eq.V_T (Sanctions.clipS' (E.F y₂.val R₂)) at h2
      change E.U_T y₁.val (Eq.α y₂.val) R₁ + E.β_T * Eq.V_T (Sanctions.clipS' (E.F y₁.val R₁))
        ≤ Eq.V_T y₁ at h1
      linarith
    have hB : E.β_T * (Eq.V_T (Sanctions.clipS' (E.F y₂.val R₂))
        - Eq.V_T (Sanctions.clipS' (E.F y₁.val R₁)))
        ≤ E.β_T * (E.KT * (E.LloopSharp * |y₂.val - y₁.val|) + D) :=
      mul_le_mul_of_nonneg_left (by linarith) hβ
    have hC : E.LUT * |y₂.val - y₁.val| + E.β_T * (E.KT * (E.LloopSharp * |y₂.val - y₁.val|))
        = E.KT * |y₂.val - y₁.val| := by linear_combination |y₂.val - y₁.val| * hfix
    nlinarith [hA, hB, hC, habs]
  have hDle : D ≤ E.β_T * D :=
    csSup_le hne (by rintro _ ⟨⟨y₁, y₂⟩, rfl⟩; exact hstep y₁ y₂)
  have hβ1 := E.hβT1
  have hD0 : D ≤ 0 := by nlinarith
  have hβD : E.β_T * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ hD0
  intro y₁ y₂
  have hd : dist y₁ y₂ = |y₂.val - y₁.val| := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
  rw [hd]
  have h12 := hstep y₁ y₂
  have h21 := hstep y₂ y₁
  rw [abs_sub_comm y₁.val y₂.val] at h21
  rw [abs_le]
  constructor <;> linarith

/-- **The upper half of the continuation bracket at every full-defiance equilibrium**: if
the Target defies at every state, a higher sanction raises its discounted continuation by
at most `β_T·K_T·d_hi·(s₂ − s₁)`, under `β_T·γ_T < 1` alone. Such an equilibrium has the
defiance-profile Target value (`values_eq_of_policy_zero`), where this is
`VTdef_continuation_upper` (renovation item BH3.11(c), 2026-10-06; the earlier form,
`VTstar_continuation_bracket`, was about the constructed equilibrium under the loss-offset
margin and a monotone response). General in `F`. -/
theorem V_T_continuation_upper_of_policy_zero (hγ : E.β_T * E.LloopSharp < 1)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {y s₁ s₂ : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hs₁ : s₁ ∈ Icc (0 : ℝ) 1)
    (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) (hle : s₁ ≤ s₂) :
    E.β_T * (Eq.V_T (Sanctions.clipS' (E.F y s₂)) - Eq.V_T (Sanctions.clipS' (E.F y s₁)))
      ≤ E.β_T * E.KT * E.dhi * (s₂ - s₁) := by
  rw [(E.values_eq_of_policy_zero Eq hα).2.1]
  exact E.VTdef_continuation_upper hγ hy hs₁ hs₂ hle

/-- **The lower half of the continuation bracket at every full-defiance equilibrium**: if
the Target defies at every state, a higher sanction raises its discounted continuation by
at least `β_T·g·d_lo·(s₂ − s₁)`, for any slope `g ≥ 0` that satisfies the balance under a
monotone response. Such an equilibrium has the defiance-profile Target value
(`values_eq_of_policy_zero`), where this is `VTdef_continuation_lower` (renovation item
BH3.11(c), 2026-10-06). Neither the loop condition nor the loss-offset margin is read.
General in `F`. -/
theorem V_T_continuation_lower_of_policy_zero
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {g : ℝ} (hg : 0 ≤ g)
    (hginv : g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {y s₁ s₂ : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hs₁ : s₁ ∈ Icc (0 : ℝ) 1)
    (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) (hle : s₁ ≤ s₂) :
    E.β_T * g * E.dlo * (s₂ - s₁)
      ≤ E.β_T * (Eq.V_T (Sanctions.clipS' (E.F y s₂))
          - Eq.V_T (Sanctions.clipS' (E.F y s₁))) := by
  rw [(E.values_eq_of_policy_zero Eq hα).2.1]
  exact E.VTdef_continuation_lower hmono hg hginv hy hs₁ hs₂ hle

end ChordEconomyRelief

namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided ChordEconomyRelief

variable (E : ChordEconomyCs)

/-! ## 3. On the relief side the policy is the zero level -/

/-- **Above the zero level, compliance is pure cost**: the response vanishes at
both levels, so the continuation is the same, and compliance costs at least
`ℓ_lo` per unit. At any Target value. -/
theorem joint_lt_of_gt_zeroLevelAt (hP : E.Placable) {V_S : Val} (hV : V_S ∈ E.carrierS)
    (V_T : Val) {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : E.zeroLevelAt V_S x < a)
    (ha1 : a ≤ 1) :
    E.toParams.joint_T_integrand V_T V_S x a
      < E.toParams.joint_T_integrand V_T V_S x (E.zeroLevelAt V_S x) := by
  rw [joint_T_integrand_eq, joint_T_integrand_eq, E.response_zeroLevelAt hP hV hx,
    E.response_eq_zero_of_zeroLevelAt_le hP hV hx ha.le ha1]
  have hzI := E.zeroLevelAt_mem hP hV hx
  have haI : a ∈ Sanctions.I := ⟨by linarith [hzI.1], ha1⟩
  have h := E.hUT_costLo x hx 0 zero_mem_I (E.zeroLevelAt V_S x) hzI a haI ha.le
  have := mul_pos E.hℓlo (by linarith : (0:ℝ) < a - E.zeroLevelAt V_S x)
  change E.U_T x a 0 + E.β_T * V_T (Sanctions.clipS' (E.F x 0))
    < E.U_T x (E.zeroLevelAt V_S x) 0 + E.β_T * V_T (Sanctions.clipS' (E.F x 0))
  linarith

/-- **Below the zero level, raising compliance to it is strictly profitable**,
at any `K`-Lipschitz Target value, when `ℓ_hi·M_tot < k_lo(p_lo − β_T d_hi K)`:
the sanction avoided, at least `k_lo(a* − a)/M_tot`, is worth at least `p_lo`
per unit in pain and costs at most `β_T d_hi K` per unit in continuation, against
a compliance cost of at most `ℓ_hi(a* − a)`. The forms at the constructed values
are `jointRel_lt_of_lt` and the arithmetic of `defiance_not_maxOn_of_relief_side`. -/
theorem joint_lt_of_lt_zeroLevelAt (hInt : E.Interior) (hP : E.Placable) {V_S : Val} (hV : V_S ∈
    E.carrierS2)
    {V_T : Val} {K : ℝ} (hK : 0 ≤ K) (hVT : Params.ValueLipschitzWith V_T K)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * K))
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < E.zeroLevelAt V_S x) :
    E.toParams.joint_T_integrand V_T V_S x a
      < E.toParams.joint_T_integrand V_T V_S x (E.zeroLevelAt V_S x) := by
  rw [joint_T_integrand_eq, joint_T_integrand_eq, E.response_zeroLevelAt hP hV.1 hx]
  set ρ := E.response V_S x a with hρdef
  have hzI := E.zeroLevelAt_mem hP hV.1 hx
  have haI : a ∈ Sanctions.I := ⟨ha0, by linarith [hzI.2]⟩
  have hρlow := E.response_ge_of_lt_zeroLevelAt hInt hP hV hx ha0 ha
  have hρmem := E.response_mem V_S x a
  have hF0 : E.F x 0 ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hx zero_mem_I
  have hFρ : E.F x ρ ∈ Icc (0 : ℝ) 1 := E.F_mem _ _ hx hρmem
  have hchord : E.F x ρ - E.F x 0 ≤ E.dhi * (ρ - 0) :=
    E.hShi hx zero_mem_I hρmem hρmem.1
  have hFmono : E.F x 0 ≤ E.F x ρ := E.F_mono_s x hρmem.1
  have hlip := hVT (Sanctions.clipS' (E.F x 0)) (Sanctions.clipS' (E.F x ρ))
  have hdc : dist (Sanctions.clipS' (E.F x 0)) (Sanctions.clipS' (E.F x ρ))
      = E.F x ρ - E.F x 0 := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hF0,
      Sanctions.clipS'_val_eq_of_mem hFρ, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hdc] at hlip
  have hβ := E.hβT0.le
  have hcont : E.β_T * (V_T (Sanctions.clipS' (E.F x ρ))
      - V_T (Sanctions.clipS' (E.F x 0))) ≤ E.β_T * (K * (E.dhi * ρ)) := by
    apply mul_le_mul_of_nonneg_left _ hβ
    have h1 := (le_abs_self _).trans hlip
    have h2 : K * (E.F x ρ - E.F x 0) ≤ K * (E.dhi * ρ) := by
      apply mul_le_mul_of_nonneg_left _ hK; linarith [hchord]
    linarith
  -- the stage: cost at most `ℓ_hi` per unit of compliance, pain at least `p_lo` per unit
  have hstage := E.UT_sub_ge hx haI hzI hρmem zero_mem_I ha.le hρmem.1
  set Γ := E.plo - E.β_T * E.dhi * K with hΓ
  have hM := E.Mtot_pos
  have hk := E.hklo
  have hΓpos : 0 < Γ := by
    by_contra hcon
    have : E.klo * Γ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (not_lt.mp hcon)
    have : 0 < E.ℓhi * E.Mtot := mul_pos E.ℓhi_pos hM
    linarith
  have hgap : 0 < E.zeroLevelAt V_S x - a := by linarith
  have h1 : E.klo * (E.zeroLevelAt V_S x - a) / E.Mtot * Γ ≤ ρ * Γ :=
    mul_le_mul_of_nonneg_right hρlow hΓpos.le
  have h2 : E.ℓhi * (E.zeroLevelAt V_S x - a)
      < E.klo * (E.zeroLevelAt V_S x - a) / E.Mtot * Γ := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hM]
    have := mul_lt_mul_of_pos_right hrel hgap
    nlinarith [this]
  change E.U_T x a ρ + E.β_T * V_T (Sanctions.clipS' (E.F x ρ))
    < E.U_T x (E.zeroLevelAt V_S x) 0 + E.β_T * V_T (Sanctions.clipS' (E.F x 0))
  nlinarith [h1, h2, hcont, hstage]

/-- **On the relief side, an equilibrium of the carrier class complies at the
zero level of its own Sender value**, at every state. -/
theorem policy_eq_zeroLevelAt_of_carrier (hInt : E.Interior) (hP : E.Placable) (hγ : E.β_T *
    E.LloopSharp < 1)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT))
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hVS : Eq.V_S ∈ E.carrierS2)
    {x : ℝ} (hx : x ∈ Sanctions.I) : Eq.α x = E.zeroLevelAt Eq.V_S x := by
  have hVT := E.equilibrium_V_T_lipschitz_of_carrier hγ Eq hVS
  have hαI := Eq.α_mem x hx
  have hzI := E.zeroLevelAt_mem hP hVS.1 hx
  have hmax : E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S x (E.zeroLevelAt Eq.V_S x)
      ≤ E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S x (Eq.α x) :=
    isMaxOn_iff.mp (Eq.α_opt_top x hx) _ hzI
  rw [E.joint_T_top_integrand_eq hVS.1 _ hx, E.joint_T_top_integrand_eq hVS.1 _ hx] at hmax
  rcases lt_trichotomy (Eq.α x) (E.zeroLevelAt Eq.V_S x) with h | h | h
  · exact absurd hmax (not_le.mpr
      (E.joint_lt_of_lt_zeroLevelAt hInt hP hVS (E.KT_nonneg hγ) hVT hrel hx hαI.1 h))
  · exact h
  · exact absurd hmax (not_le.mpr (E.joint_lt_of_gt_zeroLevelAt hP hVS.1 _ hx h hαI.2))

/-! ## 4. The values, and the uniqueness theorem -/

/-- **An equilibrium that never sanctions has the zero-sanction Sender value**,
under zero-sanction neutrality. No carrier is needed: the top selector attains
the Sender's Bellman supremum unconditionally. -/
theorem V_S_eq_VS01_of_zero_rule (hN : E.ZeroSanctionNeutral)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hrule : ∀ x ∈ Sanctions.I, E.toParams.σ_dyn_top Eq.V_S x (Eq.α x) = 0) :
    Eq.V_S = E.VS01 := by
  have hfix : E.relaxOp Eq.V_S = Eq.V_S := by
    ext y
    rw [relaxOp_apply]
    have hy := y.property
    have hgt : IsGreatest ((fun s => E.toParams.integrandS Eq.α (fun z => Eq.V_S z)
        (y.val, s)) '' Sanctions.I)
        (E.toParams.U_S y.val (Eq.α y.val) (E.toParams.σ_dyn_top Eq.V_S y.val (Eq.α y.val))
          + E.toParams.β_S * Eq.V_S (Sanctions.clipS'
            (E.toParams.F y.val (E.toParams.σ_dyn_top Eq.V_S y.val (Eq.α y.val))))) := by
      refine ⟨⟨_, E.toParams.σ_dyn_top_mem_I Eq.V_S y.val (Eq.α y.val), rfl⟩, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      exact E.toParams.σ_dyn_top_isMaxOn Eq.V_S y.val (Eq.α y.val) hs
    have hsup : Eq.V_S y = sSup ((fun s => E.toParams.integrandS Eq.α (fun z => Eq.V_S z)
        (y.val, s)) '' Sanctions.I) := by
      have h := congrArg (fun V : Val => V y) Eq.V_S_fix
      exact h
    rw [hsup, hgt.csSup_eq, hrule y.val hy, hN y.val hy (Eq.α y.val) (Eq.α_mem y.val hy)]
  have hcontr := E.relaxOp_contracting
  have h1 : Eq.V_S = hcontr.fixedPoint := hcontr.fixedPoint_unique hfix
  have h2 : E.VS01 = hcontr.fixedPoint := hcontr.fixedPoint_unique E.VS01_fix
  rw [h1, h2]

/-- **An equilibrium with the zero-sanction Sender value that complies at the
zero level has the relief-branch Target value.** -/
theorem V_T_eq_VTrel_of_relief_play (hInt : E.Interior) (hP : E.Placable)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hVS : Eq.V_S = E.VS01)
    (hα : ∀ x ∈ Sanctions.I, Eq.α x = E.zeroLevel x) :
    Eq.V_T = E.VTrel hInt hP := by
  have hfix : E.reliefOp hInt hP Eq.V_T = Eq.V_T := by
    ext y
    have hy := y.property
    rw [reliefOp_apply, Params.FeedbackStackelbergEquilibriumTop.V_T_eq_at_policy _ Eq y,
      hα y.val hy, hVS, E.joint_T_top_integrand_eq E.VS01_mem _ hy, joint_T_integrand_eq,
      E.ρ01_zeroLevel hP hy]
  have hcontr := E.reliefOp_contracting hInt hP
  have h1 : Eq.V_T = hcontr.fixedPoint := hcontr.fixedPoint_unique hfix
  have h2 : E.VTrel hInt hP = hcontr.fixedPoint := hcontr.fixedPoint_unique (E.VTrel_fix hInt hP)
  rw [h1, h2]

/-- **Uniqueness on the relief side, in the carrier class.** On the relief side
(placability, `β_T·γ_T < 1` and `ℓ_hi·M_tot < k_lo(p_lo − β_T d_hi K_T)`), under
zero-sanction neutrality, every top-selector equilibrium whose Sender value is
in the two-sided carrier complies at the zero level `a*(x)` at every state,
realises a zero sanction at every state, and has the relief values `VS01` and
`VTrel`. -/
theorem unique_equilibrium_of_relief_side (hInt : E.Interior) (hP : E.Placable) (hγ : E.β_T *
    E.LloopSharp < 1)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT))
    (hN : E.ZeroSanctionNeutral)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hVS : Eq.V_S ∈ E.carrierS2) :
    (∀ x ∈ Sanctions.I, Eq.α x = E.zeroLevel x) ∧ Eq.V_S = E.VS01 ∧ Eq.V_T = E.VTrel hInt hP ∧
    ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = 0 := by
  have hαAt : ∀ x ∈ Sanctions.I, Eq.α x = E.zeroLevelAt Eq.V_S x :=
    fun x hx => E.policy_eq_zeroLevelAt_of_carrier hInt hP hγ hrel Eq hVS hx
  have hrule : ∀ x ∈ Sanctions.I, E.toParams.σ_dyn_top Eq.V_S x (Eq.α x) = 0 := by
    intro x hx
    rw [← E.response_eq_top hVS.1 hx, hαAt x hx, E.response_zeroLevelAt hP hVS.1 hx]
  have hV : Eq.V_S = E.VS01 := E.V_S_eq_VS01_of_zero_rule hN Eq hrule
  have hα : ∀ x ∈ Sanctions.I, Eq.α x = E.zeroLevel x := by
    intro x hx
    rw [hαAt x hx, hV, E.zeroLevelAt_VS01]
  exact ⟨hα, hV, E.V_T_eq_VTrel_of_relief_play hInt hP Eq hV hα, fun x hx => hrule x hx⟩

/-- **The relief equilibrium is the only equilibrium of the carrier class**, on
the relief side, when both forms of the relief inequality hold: existence reads
the `K_T^rel` form, uniqueness the `K_T` form. Its Sender value is in the class,
and every equilibrium of the class has its policy on the state set and its two
values. -/
theorem reliefEquilibriumTop_unique_in_carrier_class (hInt : E.Interior) (hP : E.Placable)
    (hγ : E.β_T * E.LloopSharp < 1)
    (hrelEx : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel))
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT))
    (hN : E.ZeroSanctionNeutral) :
    (E.reliefEquilibriumTop hInt hP hrelEx hN).V_S ∈ E.carrierS2 ∧
    ∀ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, Eq.V_S ∈ E.carrierS2 →
      (∀ x ∈ Sanctions.I, Eq.α x = (E.reliefEquilibriumTop hInt hP hrelEx hN).α x) ∧
      Eq.V_S = (E.reliefEquilibriumTop hInt hP hrelEx hN).V_S ∧
      Eq.V_T = (E.reliefEquilibriumTop hInt hP hrelEx hN).V_T := by
  refine ⟨E.VS01_mem2, fun Eq hVS => ?_⟩
  obtain ⟨hα, hV, hT, -⟩ := E.unique_equilibrium_of_relief_side hInt hP hγ hrel hN Eq hVS
  refine ⟨fun x hx => ?_, hV, hT⟩
  rw [hα x hx, E.reliefEquilibriumTop_α hInt hP hrelEx hN hx]

/-- **An equilibrium that never sanctions is the relief equilibrium**, under
interiority, placability and zero-sanction neutrality alone: no carrier class and
no relief inequality. Its Sender value is the zero-sanction value. The Target complies at
least at the zero level, since the response vanishes at its policy, and at most
there, since compliance above it is pure cost. Its Target value is `VTrel`. -/
theorem relief_equilibrium_of_zero_rule (hInt : E.Interior) (hP : E.Placable) (hN :
    E.ZeroSanctionNeutral)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hzero : ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = 0) :
    (∀ x ∈ Sanctions.I, Eq.α x = E.zeroLevel x) ∧ Eq.V_S = E.VS01 ∧ Eq.V_T = E.VTrel hInt hP := by
  have hV : Eq.V_S = E.VS01 := E.V_S_eq_VS01_of_zero_rule hN Eq hzero
  have hα : ∀ x ∈ Sanctions.I, Eq.α x = E.zeroLevel x := by
    intro x hx
    have hαI := Eq.α_mem x hx
    have hzI := E.zeroLevel_mem hP hx
    -- the response vanishes at the policy, so the policy is in the zero set
    have hresp : E.response E.VS01 x (Eq.α x) = 0 := by
      rw [E.response_eq_top E.VS01_mem hx, ← hV]
      exact hzero x hx
    have hge : E.zeroLevel x ≤ Eq.α x := csInf_le (E.zeroSet_bddBelow x) ⟨hαI, hresp⟩
    rcases eq_or_lt_of_le hge with h | h
    · exact h.symm
    · -- compliance above the zero level is pure cost
      exfalso
      have hmax : E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S x (E.zeroLevel x)
          ≤ E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S x (Eq.α x) :=
        isMaxOn_iff.mp (Eq.α_opt_top x hx) _ hzI
      rw [hV, E.joint_T_top_integrand_eq E.VS01_mem _ hx,
        E.joint_T_top_integrand_eq E.VS01_mem _ hx] at hmax
      have hlt := E.joint_lt_of_gt_zeroLevelAt hP E.VS01_mem Eq.V_T hx h hαI.2
      exact absurd hmax (not_le.mpr hlt)
  exact ⟨hα, hV, E.V_T_eq_VTrel_of_relief_play hInt hP Eq hV hα⟩

end ChordEconomyCs

/-! ## 5. The class is inhabited off the affine law (Rule 9B) -/

/-- **Uniqueness on the relief side, witnessed off the affine law**: at the
`quadDiagF` member with `β_T = 1/8` the relief equilibrium exists, its Sender
value lies in the carrier class, and it is the class's only equilibrium. -/
theorem placableQuadDiagLo_relief_unique_in_carrier_class :
    placableQuadDiagLo_reliefEquilibrium.V_S ∈ quadDiagLoC.carrierS2 ∧
    ∀ Eq : quadDiagLoC.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_S ∈ quadDiagLoC.carrierS2 →
      (∀ x ∈ Sanctions.I, Eq.α x = placableQuadDiagLo_reliefEquilibrium.α x) ∧
      Eq.V_S = placableQuadDiagLo_reliefEquilibrium.V_S ∧
      Eq.V_T = placableQuadDiagLo_reliefEquilibrium.V_T :=
  quadDiagLoC.reliefEquilibriumTop_unique_in_carrier_class quadDiagLoC_interior
      placableQuadDiagLo_placable
    placableQuadDiagLo_γ placableQuadDiagLo_relief_exists placableQuadDiagLo_relief_notdef
    quadDiagLoC_neutral

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.ChordEconomyRelief.equilibrium_V_T_lipschitz_of_carrier
#print axioms Sanctions.Examples.ChordEconomyRelief.V_T_continuation_upper_of_policy_zero
#print axioms Sanctions.Examples.ChordEconomyRelief.V_T_continuation_lower_of_policy_zero
#print axioms Sanctions.Examples.ChordEconomyCs.policy_eq_zeroLevelAt_of_carrier
#print axioms Sanctions.Examples.ChordEconomyCs.unique_equilibrium_of_relief_side
#print axioms Sanctions.Examples.ChordEconomyCs.reliefEquilibriumTop_unique_in_carrier_class
#print axioms Sanctions.Examples.ChordEconomyCs.relief_equilibrium_of_zero_rule
#print axioms Sanctions.Examples.placableQuadDiagLo_relief_unique_in_carrier_class

end Examples
end Sanctions
