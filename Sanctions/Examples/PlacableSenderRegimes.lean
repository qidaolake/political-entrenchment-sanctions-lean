/-
Sanctions/Examples/PlacableSenderRegimes.lean

**The chord economy, part three: the fully myopic equilibrium beside the fully
forward-looking one, and what separates them** (Rung 5, docs 53/55; ported to
`ChordEconomy` in round AV, 2026-09-25, doc 104).

One economy, read at two continuation profiles — both discount factors zero
(`00`), or both as given (`11`). Stage payoffs, feasible sets, and the
transition are identical across the two readings; only continuation
preferences change. Both governments are rational in both readings. What this
file proves, over every chord economy and general in `F`:

1. **Explicit bounds on the forward-looking response** (§1). Every dynamic
   Sender maximiser is capped by the appetite ratio `A/q < 1`
   (`A = u_hi + β_S·K_S·d_hi`): sanctions are interior on the equilibrium path,
   and at defiance the response sits strictly above the stage selector
   `σ(x,0)`, hence strictly above the sanction floor `b = σ(0,0)`.
2. **The myopic equilibrium, constructed** (§2). The myopic Target's unique
   optimum is *partial compliance* `a⁰⁰(x) ∈ (0,1)`, the **least compliance at
   which the stage sanction vanishes** — enough to drive the stage sanction to
   zero, no more. On the quadratic family `a⁰⁰(x) = (u₀ + r·x)/k`; here it is a
   zero level (`Foundations/ZeroLevel`), continuous in the state because the
   stage sanction falls at least at the rate `k_lo/Q̄` below it (placation over
   the curvature ceiling, through the tilt form of the argmax-shift lemma).
   Uniqueness is a strict kink maximum under the stage relief margin
   `ℓ_hi·Q̄ < k_lo·p_lo`. The values are the stage payoffs at zero sanction along
   the policy, `U_S(x, a⁰⁰(x), 0)` and `U_T(x, a⁰⁰(x), 0)`: no condition on how
   compliance enters either payoff at zero sanction is needed here.
3. **Paths** (§3). Under `00` the state washes out geometrically to zero. Under
   `11` the state dominates the wash-in sequence `b(1 − (1 − d_lo)^t)` and
   strictly dominates the myopic path from a common start at every positive
   date; under the rally margin it converges to a steady state at which the
   sanction equals the state, inside `(b, A/q]`.
4. **The capstone** (§4), `myopic_dynamic_equilibrium_separation_generalF`.
5. **The closed loop as a self-map** (§5): its Lipschitz constant in closed
   form and, when it is below one, a unique globally attracting steady state.

**Rule 3.** No new field. **Rule 1.** The myopic policy is derived as the unique
stage argmax of the Target; the myopic Sender selector is the stage selector;
the forward-looking rule is the equilibrium response.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation items BH3.1 and BH3.2 (2026-10-06): the strict wedge, the limit bound
and the whole myopic construction read interiority `A < q` only through its stage
part `u_hi < q` (`uhi_lt_q`), and placability `A ≤ k_lo` only through its stage part
`u_hi < k_lo` (`uhi_lt_k`). The lemmas take these stage forms as the binders `hS`
and `hPs`. The myopic definitions `VS00`, `VT00`, `myopicEquilibriumTop` and
`myopicPath` keep their binders (headline row 35 names them); their stage-form
siblings `VS00s`, `VT00s`, `myopicEquilibriumTopS` and `myopicPathS` are equal to
them by `rfl` (`myopicEquilibriumTop_eq_S`, `myopicPath_eq_S`), and
`myopic_dynamic_equilibrium_separation_generalF_stage` is the stage-form capstone.
Interiority is kept only where the cap `A/q < 1` is read.

Renovation item BH4.1 (2026-10-06): the rally margin
`β_S·(σ_C·g_hi·d_hi + (K_S + 2σ_C)·M_mix) ≤ r_lo` is read on the forward-looking
side only to make the response `responsePath VSstar` nondecreasing on `[0, 1]`
(`responsePath_monotoneOn_of_margin`). The forward-looking path `dynamicPathOf hTM hmono`
and the `_of_response_monotone` lemmas take that nondecreasing response `hmono` in its
place, at the constructed equilibrium `equilibriumTop hTM hmono`. The margin forms
(`dynamicPath`, `dynamicPath_tendsto`, the capstones) keep their statements and are
corollaries at `hmono := responsePath_monotoneOn_of_margin hmargin`; the path bridge
`dynamicPath_eq_dynamicPathOf` is `rfl`. A nondecreasing response is a condition on an
endogenous object, so it is not checkable from the primitives alone; the rally margin is
a sufficient condition for it, and a strictly stronger one
(`exists_member_response_monotone_not_margin`).

Renovation item BJ3.1 (2026-10-07): the rally margin and the response Lipschitz constant
`L_resp` read the two-sided curvature data `τ_x`, `M_cx`, `M_mix`, which left the base
class. So the margin forms (`dynamicPath`, `dynamicRule_eq_responsePath`,
`dynamicRule_mem`, `dynamicPath_tendsto` and the other margin-form path lemmas) and the
closed-loop constants `Lloop`, `LloopSharp` are stated on `ChordEconomyTwoSided`; the
capstones and the closed-loop theorems stay on `ChordEconomyRelief`, which extends it.
Statements are unchanged. The `_of_response_monotone` forms, `dynamicPathOf` and
`closedLoop` keep their classes.
-/
import Sanctions.Examples.PlacableSenderEquilibrium
import Sanctions.Theory.Basin.PrimitiveHighBasin
import Sanctions.Theory.LockIn.RegimePathBounds
import Sanctions.Theory.Mechanism.ZeroDiscountSelector
import Sanctions.Theory.Mechanism.RegimeExistence
import Sanctions.Foundations.IntervalContraction
import Sanctions.Foundations.ZeroLevel
import Sanctions.Foundations.TransitionExtension

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave
  Sanctions.TransitionChords Sanctions.GeometricApproach Sanctions.Mechanism

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 0. The appetite and the cap -/

theorem A_eq : E.A = E.uhi + E.β_S * E.KS * E.dhi := rfl

theorem uhi_lt_A : E.uhi < E.A := by
  rw [A_eq]
  have := mul_pos (mul_pos E.hβS0 E.KS_pos) (lt_of_lt_of_le E.hdlo0 E.hdlo_dhi)
  linarith

theorem A_le_k (hP : E.Placable) : E.A ≤ E.klo := hP

/-- The cap on every dynamic sanction: the appetite ratio `A/q`. -/
def cap : ℝ := E.A / E.q

theorem cap_pos : 0 < E.cap := div_pos E.A_pos E.hq

theorem cap_lt_one (hInt : E.Interior) : E.cap < 1 := by
  unfold cap; rw [div_lt_one E.hq]; exact E.A_lt_q hInt

theorem uhi_lt_k (hP : E.Placable) : E.uhi < E.klo := lt_of_lt_of_le E.uhi_lt_A (E.A_le_k hP)

theorem dlo_le_one : E.dlo ≤ 1 := E.toParams.sanctionLowerChord_le_one E.hSlo

/-! ## 1. Every dynamic Sender maximiser is capped -/

/-- The continuation is `β_S·K_S·d_hi`-Lipschitz in the sanction on the carrier. -/
theorem continuation_lipschitz_s {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) :
    ∀ t ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
      |E.β_S * V (Sanctions.clipS' (E.F x t)) - E.β_S * V (Sanctions.clipS' (E.F x s))|
        ≤ (E.β_S * E.KS * E.dhi) * |t - s| := by
  intro t ht s hs
  rw [← mul_sub, abs_mul, abs_of_nonneg E.hβS0.le]
  have hlip := E.clip_lip hV.1 _ (E.F_mem _ _ hx ht) _ (E.F_mem _ _ hx hs)
  have hch := abs_sub_le_of_sanctionChords E.hdlo0.le E.hSlo E.hShi hx ht hs
  calc E.β_S * |V (Sanctions.clipS' (E.F x t)) - V (Sanctions.clipS' (E.F x s))|
      ≤ E.β_S * (E.KS * (E.dhi * |t - s|)) := by
        apply mul_le_mul_of_nonneg_left _ E.hβS0.le
        exact hlip.trans (mul_le_mul_of_nonneg_left hch E.KS_pos.le)
    _ = E.β_S * E.KS * E.dhi * |t - s| := by ring

/-- **Every dynamic Sender maximiser is at most `A/q`**, at every carrier value,
feasible state, and feasible compliance: the appetite chord (S11 with placation)
and the `β_S·K_S·d_hi`-Lipschitz continuation. -/
theorem dynamicArgmax_le_cap {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) {s : ℝ} (hs : s ∈ Sanctions.I)
    (hmax : IsMaxOn (fun u => E.senderObj V x a u) Sanctions.I s) : s ≤ E.cap := by
  have hmax' : IsMaxOn (fun u => E.U_S x a u + E.β_S * V (Sanctions.clipS' (E.F x u)))
      Sanctions.I s := hmax
  have h := argmax_le_cap_of_chord_slope_lipschitz (g := fun u => E.U_S x a u)
    (h := fun u => E.β_S * V (Sanctions.clipS' (E.F x u))) E.hq
    (by have := E.A_pos; rw [A_eq] at this; linarith)
    (E.stage_chord_slope hx ha) (E.continuation_lipschitz_s hV hx) hs hmax'
  unfold cap
  rw [A_eq]
  exact h

theorem response_le_cap {V : Val} (hV : V ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a : ℝ} (ha : a ∈ Sanctions.I) : E.response V x a ≤ E.cap :=
  E.dynamicArgmax_le_cap hV hx ha (E.response_mem V x a) (E.response_isMaxOn V x a)

/-- **The forward-looking sanction is interior from above**: strictly below one. -/
theorem response_lt_one (hInt : E.Interior) {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) : E.response V x a < 1 :=
  lt_of_le_of_lt (E.response_le_cap hV hx ha) (E.cap_lt_one hInt)

/-- **The pivot-star premise of `thm:persistence` cannot hold on the family at the
top state** (round P, 2026-09-11, doc 84 Q5; the reader's 2026-09-11 package,
document 03 §1). On any basin `[x̄, 1]` the pivot at `x = 1` is `1`, and the star
premise, through the bridge
`senderDynObjective_lt_pivot_of_star_chord_and_V_lipschitz`, makes the full
sanction strictly better than every smaller one in the Sender's dynamic
objective at the equilibrium policy. But every family maximiser is at most
`A/q < 1` (`response_lt_one`), and it is a maximiser, so the full sanction
cannot beat it. Hence, whatever the modulus `K` and the floor `x̄`, the star form
of `thm:persistence` is not the route to persistence on the placable family:
the family's persistence content is the four-cell theorem and the episode
corollary. A Rule-11 refutation of a hypothesis combination, not of any
theorem; the interval-dominance premise is not even needed for it. -/
theorem star_premise_at_one_false (hInt : E.Interior)
    (Est : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS : Est.V_S ∈ E.carrierS) {xbar K : ℝ} (hxbar : xbar ∈ Sanctions.I)
    (hlip : Params.ValueLipschitzWith Est.V_S K)
    (hstar : ∀ x ∈ Set.Icc xbar (1 : ℝ), ∀ s₁ ∈ Set.Ico (0 : ℝ) (max x xbar),
      E.toParams.β_S * K * dist (Sanctions.clipS' (E.toParams.F x s₁))
          (Sanctions.clipS' (E.toParams.F x (max x xbar)))
        < E.toParams.U_S x (Est.α x) (max x xbar) - E.toParams.U_S x (Est.α x) s₁) :
    False := by
  have hone : (1 : ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_rfl⟩
  have h1 : (1 : ℝ) ∈ Set.Icc xbar 1 := ⟨hxbar.2, le_rfl⟩
  have hmax : max (1 : ℝ) xbar = 1 := max_eq_left hxbar.2
  have hα : 0 ≤ Est.α 1 := (Est.α_mem 1 hone).1
  have hs_mem : E.response Est.V_S 1 (Est.α 1) ∈ Sanctions.I := E.response_mem _ _ _
  have hs_lt : E.response Est.V_S 1 (Est.α 1) < 1 :=
    E.response_lt_one hInt hVS hone (Est.α_mem 1 hone)
  have hsIco : E.response Est.V_S 1 (Est.α 1) ∈ Set.Ico (0 : ℝ) (max 1 xbar) := by
    rw [hmax]; exact ⟨hs_mem.1, hs_lt⟩
  have hlt := E.toParams.senderDynObjective_lt_pivot_of_star_chord_and_V_lipschitz
    (hstar 1 h1) hlip _ hsIco
  rw [hmax] at hlt
  have hge := E.response_isMaxOn Est.V_S 1 (Est.α 1) hone
  simp only [Set.mem_setOf_eq] at hge
  unfold Params.senderDynObjective at hlt
  unfold senderObj at hge
  linarith

/-- **The forward-looking sanction at defiance sits strictly above the stage
selector.** Weak dominance is `response_ge_stage`; equality would make the
response a stage maximiser, which the active Sender channel forbids. General in
`F`. Under the stage appetite `u_hi < q` (BH3.1, 2026-10-06: the binder was
interiority `A < q`, read only through `u_hi < q`). -/
theorem responsePath_gt_stage (hS : E.uhi < E.q) {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) : E.σ x 0 < E.responsePath V x := by
  have hge : E.σ x 0 ≤ E.responsePath V x := E.response_ge_stage hV hx 0
  rcases hge.lt_or_eq with h | h
  · exact h
  · exfalso
    have hact := E.sender_channel_active_on_carrier hS hV hx
    have hdyn : IsMaxOn (fun t => E.toParams.U_S x 0 t
        + E.toParams.β_S * E.toParams.senderSanctionContinuation V x t) Sanctions.I
        (E.responsePath V x) := E.response_isMaxOn V x 0
    have hstage : IsMaxOn (fun t => E.toParams.U_S x 0 t) Sanctions.I (E.responsePath V x) := by
      have hσ := E.toParams.σ_isMaxOn_U_S x 0
      rw [h] at hσ
      exact hσ
    exact hact _ (E.responsePath_mem V x) hdyn hstage

/-- The response at defiance is strictly above the sanction floor `b = σ(0,0)`.
General in `F`; under the stage appetite `u_hi < q` (BH3.1: the binder was
interiority `A < q`). -/
theorem responsePath_gt_sfloor (hS : E.uhi < E.q) {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) : E.sfloor < E.responsePath V x :=
  lt_of_le_of_lt (E.sfloor_le hx) (E.responsePath_gt_stage hS hV hx)

/-- The response at defiance is positive: at least the positive sanction floor.
No interiority (round BC: the weak bound `responsePath_ge_sfloor` suffices). -/
theorem responsePath_pos {V : Val} (hV : V ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I) :
    0 < E.responsePath V x :=
  lt_of_lt_of_le E.sfloor_pos (E.responsePath_ge_sfloor hV hx)

theorem responsePath_le_cap {V : Val} (hV : V ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.responsePath V x ≤ E.cap :=
  E.response_le_cap hV hx zero_mem_I

/-- The sanction floor is below the cap. -/
theorem sfloor_le_cap : E.sfloor ≤ E.cap :=
  (E.responsePath_ge_sfloor E.VSstar_mem zero_mem_I).trans
    (E.responsePath_le_cap E.VSstar_mem zero_mem_I)

/-! ## 2. The fully myopic equilibrium, constructed -/

/-- The economy read at the fully myopic profile: both discount factors zero,
everything else the same object. -/
abbrev pM : AbstractGame.Params := E.toParams.withProfile ContinuationProfile.p00

theorem pM_β_S : E.pM.β_S = 0 := rfl
theorem pM_β_T : E.pM.β_T = 0 := rfl

/-! ### The stage sanction as a function of compliance -/

/-- **The stage sanction is antitone in compliance** (Topkis: decreasing
differences in compliance and sanction, S10, and uniqueness of the stage
argmax, S4). -/
theorem stage_σ_antitoneOn {x : ℝ} (hx : x ∈ Sanctions.I) :
    AntitoneOn (fun a => E.σ x a) Sanctions.I := by
  intro a ha a' ha' haa'
  simp only
  by_contra hlt
  have hlt : E.σ x a < E.σ x a' := not_le.mp hlt
  have hs := E.σ_mem x a
  have hs' := E.σ_mem x a'
  have hdd := E.hUS_placLo x hx a ha a' ha' (E.σ x a) hs (E.σ x a') hs' haa' hlt.le
  have hdd0 : 0 ≤ E.klo * ((a' - a) * (E.σ x a' - E.σ x a)) :=
    mul_nonneg E.hklo.le (mul_nonneg (sub_nonneg.2 haa') (sub_nonneg.2 hlt.le))
  have hmx : E.U_S x a' (E.σ x a) ≤ E.U_S x a' (E.σ x a') := (E.σ_isMaxOn_U_S x a') hs
  have hmax' : IsMaxOn (fun t => E.U_S x a t) Sanctions.I (E.σ x a') := by
    intro t ht
    have h1 : E.U_S x a t ≤ E.U_S x a (E.σ x a) := (E.σ_isMaxOn_U_S x a) ht
    change E.U_S x a t ≤ E.U_S x a (E.σ x a')
    linarith
  have := E.stage_argmax_eq hx a hs' hmax'
  linarith

/-- **Where the appetite is below the placation it buys, the stage sanction is
zero**: the marginal return at every sanction is at most `u_hi − k_lo·a ≤ 0`. -/
theorem stage_σ_eq_zero_of_uhi_le {x a : ℝ} (hx : x ∈ Sanctions.I) (ha : a ∈ Sanctions.I)
    (h : E.uhi ≤ E.klo * a) : E.σ x a = 0 := by
  have hmax : IsMaxOn (fun t => E.U_S x a t) Sanctions.I 0 := by
    intro s hs
    change E.U_S x a s ≤ E.U_S x a 0
    have happ := E.hUS_appetite x hx 0 zero_mem_I s hs hs.1
    have hdd := E.hUS_placLo x hx 0 zero_mem_I a ha 0 zero_mem_I s hs ha.1 hs.1
    have h1 : 0 ≤ E.q / 2 * s ^ 2 := by have := E.hq; positivity
    have h2 : s * (E.uhi - E.klo * a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs.1 (by linarith)
    nlinarith [happ, hdd, h1, h2]
  exact (E.stage_argmax_eq hx a zero_mem_I hmax).symm

/-- At full compliance the stage sanction is zero. General in `F`. Under the stage
placability `u_hi < k_lo` (BH3.2, 2026-10-06: the binder was placability
`A ≤ k_lo`, read only through `u_hi < k_lo`): full compliance placates more than the
myopic Sender's appetite for sanction. -/
theorem stage_σ_one (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I) : E.σ x 1 = 0 :=
  E.stage_σ_eq_zero_of_uhi_le hx one_mem_I (by linarith [hPs])

theorem stage_σ_continuous (x : ℝ) : Continuous (fun a => E.σ x a) :=
  E.σ_continuous.comp (continuous_const.prodMk continuous_id)

/-- **The stage relief rate.** Between two compliance levels at which the
stage sanction is positive, extra compliance lowers it by at least
`k_lo·Δa/Q̄`: the stage objective is `Q̄`-semiconvex in the sanction (S5), and
placation (S10) is a tilt of rate `k_lo·Δa`
(`argmax_shift_ge_tilt_of_semiconvex_interior`). General in `F`. Under the stage
appetite `u_hi < q` (BH3.1, 2026-10-06: the binder was interiority `A < q`). -/
theorem stage_σ_shift (hS : E.uhi < E.q) {x : ℝ} (hx : x ∈ Sanctions.I) {a a' : ℝ}
    (ha : a ∈ Sanctions.I)
    (ha' : a' ∈ Sanctions.I) (haa' : a < a') (hint : 0 < E.σ x a') :
    E.klo * (a' - a) / E.Qbar ≤ E.σ x a - E.σ x a' := by
  have h01 : E.σ x a ≤ E.σ x 0 := E.stage_σ_antitoneOn hx zero_mem_I ha ha.1
  have hlt1 : E.σ x 0 < 1 := E.stage_argmax_lt_one hS hx
  have h01' : E.σ x a' ≤ E.σ x 0 := E.stage_σ_antitoneOn hx zero_mem_I ha' ha'.1
  exact Sanctions.SemiconvexArgmaxShift.argmax_shift_ge_tilt_of_semiconvex_interior
    E.Qbar_pos (E.hUS_convex x hx a' ha') (E.hUS_convex x hx a ha) hint (by linarith)
    (E.σ_isMaxOn_U_S x a') (mul_pos E.hklo (by linarith)) (E.σ_mem x a) (by linarith)
    (E.σ_isMaxOn_U_S x a)
    (fun u₁ hu₁ u₂ hu₂ hu => by
      have hdd := E.hUS_placLo x hx a ha a' ha' u₁ hu₁ u₂ hu₂ haa'.le hu
      nlinarith [hdd])

/-! ### The myopic zero level -/

/-- **The myopic zero level** `a⁰⁰(x)`: the least compliance at which the stage
sanction vanishes (`Foundations/ZeroLevel`). -/
def zeroLevel00 (x : ℝ) : ℝ := Sanctions.ZeroLevel.level E.σ x

/-- The myopic zero level is feasible. General in `F`; under the stage placability
`u_hi < k_lo` (BH3.2: the binder was placability `A ≤ k_lo`). -/
theorem zeroLevel00_mem (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.zeroLevel00 x ∈ Sanctions.I :=
  Sanctions.ZeroLevel.level_mem (E.stage_σ_continuous x).continuousOn (E.stage_σ_one hPs hx)

/-- The stage sanction vanishes at the myopic zero level. General in `F`; under the
stage placability `u_hi < k_lo` (BH3.2: the binder was placability `A ≤ k_lo`). -/
theorem σ_zeroLevel00 (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.σ x (E.zeroLevel00 x) = 0 :=
  Sanctions.ZeroLevel.rho_level (E.stage_σ_continuous x).continuousOn (E.stage_σ_one hPs hx)

theorem σ_pos_of_lt_zeroLevel00 {x a : ℝ} (ha : a ∈ Sanctions.I) (h : a < E.zeroLevel00 x) :
    0 < E.σ x a :=
  Sanctions.ZeroLevel.rho_pos_of_lt (E.σ_mem x a).1 ha.1 ha.2 h

/-- Above the myopic zero level the stage sanction is zero. General in `F`; under
the stage placability `u_hi < k_lo` (BH3.2: the binder was placability `A ≤ k_lo`). -/
theorem σ_eq_zero_of_ge_zeroLevel00 (hPs : E.uhi < E.klo) {x a : ℝ} (hx : x ∈ Sanctions.I)
    (h : E.zeroLevel00 x ≤ a) (ha1 : a ≤ 1) : E.σ x a = 0 :=
  Sanctions.ZeroLevel.rho_eq_zero_of_ge (E.stage_σ_continuous x).continuousOn
    (E.stage_σ_one hPs hx) (E.stage_σ_antitoneOn hx) h ha1

/-- **The stage sanction below the zero level is at least `k_lo/Q̄` times the
distance to it** (a one-sided limit of the stage relief rate). General in `F`.
Under the stage appetite `u_hi < q` and the stage placability `u_hi < k_lo` (BH3.1,
BH3.2, 2026-10-06: the binders were interiority `A < q` and placability `A ≤ k_lo`,
read only through these stage parts). -/
theorem σ_ge_of_lt_zeroLevel00 (hS : E.uhi < E.q) (hPs : E.uhi < E.klo) {x a : ℝ}
    (hx : x ∈ Sanctions.I)
    (ha : a ∈ Sanctions.I) (h : a < E.zeroLevel00 x) :
    E.klo / E.Qbar * (E.zeroLevel00 x - a) ≤ E.σ x a := by
  have hz1 := (E.zeroLevel00_mem hPs hx).2
  apply Sanctions.ZeroLevel.rho_ge_of_lt (div_pos E.hklo E.Qbar_pos)
  · intro a' h1 h2
    have ha'I : a' ∈ Sanctions.I := ⟨by linarith [ha.1], by
      have : a' < E.zeroLevel00 x := h2
      linarith⟩
    have hint := E.σ_pos_of_lt_zeroLevel00 ha'I h2
    have hs := E.stage_σ_shift hS hx ha ha'I h1 hint
    have heq : E.klo / E.Qbar * (a' - a) = E.klo * (a' - a) / E.Qbar := by ring
    linarith
  · intro a' _ _
    exact (E.σ_mem x a').1
  · exact h

/-- The myopic zero level is positive: a defiant Target is sanctioned. General in
`F`; under the stage placability `u_hi < k_lo` (BH3.2: the binder was placability
`A ≤ k_lo`). -/
theorem zeroLevel00_pos (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I) :
    0 < E.zeroLevel00 x := by
  rcases (E.zeroLevel00_mem hPs hx).1.lt_or_eq with h | h
  · exact h
  · exfalso
    have h0 := E.σ_zeroLevel00 hPs hx
    rw [← h] at h0
    exact absurd h0 (E.stage_argmax_pos hx).ne'

/-- The myopic zero level is below one: compliance `u_hi/k_lo < 1` already
placates. General in `F`. Under the stage placability `u_hi < k_lo`, which is exactly
what the proof reads (BH3.2, 2026-10-06: the binder was placability `A ≤ k_lo`). -/
theorem zeroLevel00_lt_one (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.zeroLevel00 x < 1 := by
  have hk := E.hklo
  have hlt := hPs
  set a := E.uhi / E.klo with ha
  have ha1 : a < 1 := by rw [ha, div_lt_one hk]; exact hlt
  have ha0 : 0 ≤ a := div_nonneg E.uhi_pos.le hk.le
  have haI : a ∈ Sanctions.I := ⟨ha0, ha1.le⟩
  have hmul : E.klo * a = E.uhi := by
    rw [ha, mul_div_assoc']; exact mul_div_cancel_left₀ _ hk.ne'
  have hz : E.σ x a = 0 := E.stage_σ_eq_zero_of_uhi_le hx haI hmul.ge
  have hmem : a ∈ Sanctions.ZeroLevel.zeroSet E.σ x := ⟨haI, hz⟩
  have := csInf_le (Sanctions.ZeroLevel.zeroSet_bddBelow x) hmem
  exact lt_of_le_of_lt this ha1

/-- **The myopic zero level is continuous in the state.** General in `F`. Under the
stage appetite `u_hi < q` and the stage placability `u_hi < k_lo` (BH3.1, BH3.2,
2026-10-06: the binders were interiority `A < q` and placability `A ≤ k_lo`). -/
theorem zeroLevel00_continuousOn (hS : E.uhi < E.q) (hPs : E.uhi < E.klo) :
    ContinuousOn E.zeroLevel00 Sanctions.I :=
  Sanctions.ZeroLevel.level_continuousOn (c := E.klo / E.Qbar) (div_pos E.hklo E.Qbar_pos)
    E.σ_continuous.continuousOn (fun _ hx => E.stage_σ_one hPs hx)
    (fun _ hx => E.stage_σ_antitoneOn hx)
    (fun _ hx _ ha h => E.σ_ge_of_lt_zeroLevel00 hS hPs hx ha h)

/-- **At the myopic zero level the stage objective is flat at zero sanction, up
to the curvature ceiling**: `U_S(x, a⁰⁰, ε) − U_S(x, a⁰⁰, 0) ≥ −(Q̄/2)ε²`. Just
below the zero level the stage sanction is positive, so the quadratic lower
support of the stage objective at its interior maximiser bounds the loss from
moving to `ε`; the placation ceiling (S10u) carries the bound to the zero
level. On the quadratic family it holds with equality. General in `F`. Under the
stage placability `u_hi < k_lo` (BH3.2, 2026-10-06: the binder was placability
`A ≤ k_lo`) and a placation ceiling `hPC` (renovation item BJ2.2, 2026-10-07: until then
the base class's field S10u, now the predicate `PlacationCeiling`; any ceiling `k_hi`
serves, since only its finiteness is read). -/
theorem stage_flat_at_zeroLevel00 {khi : ℝ} (hPC : E.PlacationCeiling khi)
    (hPs : E.uhi < E.klo) {x ε : ℝ} (hx : x ∈ Sanctions.I)
    (hε : ε ∈ Sanctions.I) :
    -(E.Qbar / 2 * ε ^ 2) ≤ E.U_S x (E.zeroLevel00 x) ε - E.U_S x (E.zeroLevel00 x) 0 := by
  have hzI := E.zeroLevel00_mem hPs hx
  have hz0 := E.zeroLevel00_pos hPs hx
  have hσz := E.σ_zeroLevel00 hPs hx
  set z := E.zeroLevel00 x with hz
  have hstep : ∀ a, 0 ≤ a → a < z → E.σ x a ≤ ε →
      -(E.Qbar / 2 * ε ^ 2) - khi * ((z - a) * ε) ≤ E.U_S x z ε - E.U_S x z 0 := by
    intro a ha0 haz hσε
    have haI : a ∈ Sanctions.I := ⟨ha0, by linarith [hzI.2]⟩
    have hsa0 : 0 < E.σ x a := E.σ_pos_of_lt_zeroLevel00 haI haz
    have hsup : E.U_S x a (E.σ x a) - E.Qbar / 2 * (ε - E.σ x a) ^ 2 ≤ E.U_S x a ε :=
      Sanctions.SemiconvexArgmaxShift.quadratic_support_right_of_semiconvex_interior_max
        E.Qbar_pos (E.hUS_convex x hx a haI) (E.σ_isMaxOn_U_S x a) hsa0 (y := ε) hσε hε.2
    have hmax0 : E.U_S x a 0 ≤ E.U_S x a (E.σ x a) := (E.σ_isMaxOn_U_S x a) zero_mem_I
    have hpl := hPC x hx a haI z hzI 0 zero_mem_I ε hε haz.le
    rw [sub_zero, abs_of_nonneg hε.1] at hpl
    have hpl' := (abs_le.mp hpl).1
    have hsq : (ε - E.σ x a) ^ 2 ≤ ε ^ 2 := by nlinarith [hsa0, hσε]
    have hQ := E.Qbar_pos
    nlinarith [hsup, hmax0, hpl', hsq]
  rcases hε.1.eq_or_lt with h0 | hεpos
  · rw [← h0]; simp
  · apply le_of_forall_pos_le_add
    intro δ hδ
    have hcont := (E.stage_σ_continuous x).continuousAt (x := z)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨η, hη, hησ⟩ := hcont ε hεpos
    have hK : 0 < khi * ε + 1 := by
      have := mul_nonneg (E.khi_pos hPC).le hεpos.le; linarith
    set d := min (min (η / 2) (z / 2)) (δ / (khi * ε + 1)) with hd
    have hd0 : 0 < d := lt_min (lt_min (by linarith) (by linarith)) (div_pos hδ hK)
    have hdη : d < η := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _))
      (by linarith)
    have hdz : d ≤ z / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hdδ : d ≤ δ / (khi * ε + 1) := min_le_right _ _
    have ha0 : 0 ≤ z - d := by linarith
    have haz : z - d < z := by linarith
    have hσa : E.σ x (z - d) ≤ ε := by
      have h1 : dist (E.σ x (z - d)) (E.σ x z) < ε :=
        hησ (show dist (z - d) z < η by
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rw [Real.dist_eq, hσz, sub_zero] at h1
      exact (abs_lt.mp h1).2.le
    have hmain := hstep (z - d) ha0 haz hσa
    have hbound : khi * ((z - (z - d)) * ε) ≤ δ := by
      have hza : z - (z - d) = d := by ring
      rw [hza]
      have h2 : d * (khi * ε + 1) ≤ δ := by rw [le_div_iff₀ hK] at hdδ; exact hdδ
      nlinarith [hd0]
    linarith

/-! ### The myopic policy -/

/-- **The myopic Target's policy**, the zero level extended to `ℝ` through the
clip. Derived below as the unique stage optimum of the myopic Target. -/
def myopicPolicy (x : ℝ) : ℝ := E.zeroLevel00 (Sanctions.clipS x)

theorem myopicPolicy_eq {x : ℝ} (hx : x ∈ Sanctions.I) : E.myopicPolicy x = E.zeroLevel00 x := by
  unfold myopicPolicy
  rw [Sanctions.TransitionExtension.clipS_of_mem hx]

/-- The myopic policy is continuous. General in `F`. Under the stage appetite
`u_hi < q` and the stage placability `u_hi < k_lo` (BH3.1, BH3.2, 2026-10-06: the
binders were interiority `A < q` and placability `A ≤ k_lo`). -/
theorem myopicPolicy_continuous (hS : E.uhi < E.q) (hPs : E.uhi < E.klo) :
    Continuous E.myopicPolicy :=
  (E.zeroLevel00_continuousOn hS hPs).comp_continuous Sanctions.clipS_continuous
    (fun x => Sanctions.clipS_mem x)

/-- The myopic policy is positive. General in `F`; under the stage placability
`u_hi < k_lo` (BH3.2: the binder was placability `A ≤ k_lo`). -/
theorem myopicPolicy_pos (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I) :
    0 < E.myopicPolicy x := by
  rw [E.myopicPolicy_eq hx]; exact E.zeroLevel00_pos hPs hx

/-- The myopic policy is below one. General in `F`; under the stage placability
`u_hi < k_lo` (BH3.2: the binder was placability `A ≤ k_lo`). -/
theorem myopicPolicy_lt_one (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.myopicPolicy x < 1 := by
  rw [E.myopicPolicy_eq hx]; exact E.zeroLevel00_lt_one hPs hx

/-- The myopic policy is feasible. General in `F`; under the stage placability
`u_hi < k_lo` (BH3.2: the binder was placability `A ≤ k_lo`). -/
theorem myopicPolicy_mem (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.myopicPolicy x ∈ Sanctions.I :=
  ⟨(E.myopicPolicy_pos hPs hx).le, (E.myopicPolicy_lt_one hPs hx).le⟩

/-- **Partial compliance, strictly interior.** General in `F`; under the stage
placability `u_hi < k_lo` (BH3.2: the binder was placability `A ≤ k_lo`). -/
theorem myopicPolicy_mem_Ioo (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.myopicPolicy x ∈ Ioo (0 : ℝ) 1 :=
  ⟨E.myopicPolicy_pos hPs hx, E.myopicPolicy_lt_one hPs hx⟩

/-- **The stage sanction at the myopic policy is zero**: placation exactly. General
in `F`; under the stage placability `u_hi < k_lo` (BH3.2: the binder was placability
`A ≤ k_lo`). -/
theorem σ_at_myopicPolicy (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.σ x (E.myopicPolicy x) = 0 := by
  rw [E.myopicPolicy_eq hx]; exact E.σ_zeroLevel00 hPs hx

end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The myopic Target's stage objective is uniquely maximised at the myopic
policy.** Below it, the stage sanction is at least `k_lo/Q̄` per unit of the
remaining distance, each unit of sanction pains at least `p_lo`, and complying
costs at most `ℓ_hi` per unit: the stage relief margin `ℓ_hi·Q̄ < k_lo·p_lo` makes
the move to the policy strictly profitable. Above it, compliance buys nothing
and costs at least `ℓ_lo > 0`. A strict kink maximum. General in `F`. Under the
stage appetite `u_hi < q` and the stage placability `u_hi < k_lo` (BH3.1, BH3.2,
2026-10-06: the binders were interiority `A < q` and placability `A ≤ k_lo`, read
only through these stage parts). -/
theorem myopic_target_lt (hS : E.uhi < E.q) (hSR : E.StageRelief) (hPs : E.uhi < E.klo)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I) (hne : a ≠ E.myopicPolicy x) :
    E.toParams.U_T x a (E.toParams.σ x a)
      < E.toParams.U_T x (E.myopicPolicy x) (E.toParams.σ x (E.myopicPolicy x)) := by
  rw [E.σ_at_myopicPolicy hPs hx]
  have hmI := E.myopicPolicy_mem hPs hx
  rw [E.myopicPolicy_eq hx] at hne hmI ⊢
  rcases lt_or_gt_of_ne hne with h | h
  · have hσ := E.σ_ge_of_lt_zeroLevel00 hS hPs hx ha h
    have hσmem := E.σ_mem x a
    have hU := E.UT_sub_ge hx ha hmI hσmem zero_mem_I h.le hσmem.1
    have hgap : 0 < E.zeroLevel00 x - a := by linarith
    have hQ := E.Qbar_pos
    have hrel : E.ℓhi * (E.zeroLevel00 x - a)
        < E.plo * (E.klo / E.Qbar * (E.zeroLevel00 x - a)) := by
      have hSR : E.StageRelief := hSR
      unfold StageRelief at hSR
      have heq : E.plo * (E.klo / E.Qbar * (E.zeroLevel00 x - a))
          = (E.klo * E.plo / E.Qbar) * (E.zeroLevel00 x - a) := by ring
      rw [heq]
      apply mul_lt_mul_of_pos_right _ hgap
      rw [lt_div_iff₀ hQ]; linarith
    have h3 : E.plo * (E.klo / E.Qbar * (E.zeroLevel00 x - a)) ≤ E.plo * E.σ x a :=
      mul_le_mul_of_nonneg_left hσ E.hplo.le
    change E.U_T x a (E.σ x a) < E.U_T x (E.zeroLevel00 x) 0
    nlinarith [hU, hrel, h3]
  · have h0 := E.σ_eq_zero_of_ge_zeroLevel00 hPs hx h.le ha.2
    have hc := E.hUT_costLo x hx 0 zero_mem_I (E.zeroLevel00 x) hmI a ha h.le
    have : 0 < E.ℓlo * (a - E.zeroLevel00 x) := mul_pos E.hℓlo (by linarith)
    change E.U_T x a (E.σ x a) < E.U_T x (E.zeroLevel00 x) 0
    rw [h0]
    linarith

/-- The myopic policy maximises the myopic Target's stage objective. General in
`F`; under the stage appetite `u_hi < q` and the stage placability `u_hi < k_lo`
(BH3.1, BH3.2: the binders were interiority and placability). -/
theorem myopicPolicy_isMaxOn (hS : E.uhi < E.q) (hSR : E.StageRelief) (hPs : E.uhi < E.klo)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => E.toParams.U_T x a (E.toParams.σ x a)) Sanctions.I (E.myopicPolicy x) := by
  intro a ha
  simp only [Set.mem_setOf_eq]
  by_cases h : a = E.myopicPolicy x
  · rw [h]
  · exact (E.myopic_target_lt hS hSR hPs hx ha h).le

/-- **Uniqueness of the myopic Target optimum.** General in `F`; under the stage
appetite `u_hi < q` and the stage placability `u_hi < k_lo` (BH3.1, BH3.2: the
binders were interiority and placability). -/
theorem myopic_target_unique (hS : E.uhi < E.q) (hSR : E.StageRelief) (hPs : E.uhi < E.klo)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun a => E.toParams.U_T x a (E.toParams.σ x a)) Sanctions.I a) :
    a = E.myopicPolicy x := by
  by_contra hne
  have h1 := E.myopic_target_lt hS hSR hPs hx ha hne
  have h2 := hmax (E.myopicPolicy_mem hPs hx)
  simp only [Set.mem_setOf_eq] at h2
  linarith

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **Selector identity at the myopic view**: the greatest forward-looking
selector is the stage selector, for every continuation value. -/
theorem pM_σ_dyn_top (V : Val) {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    E.pM.σ_dyn_top V x a = E.toParams.σ x a :=
  E.pM.σ_dyn_top_eq_σ_of_βS_zero_of_strictConcaveOn rfl V x a (E.stage_strictConcaveOn hx a)

/-- An affine bounded continuous function on the state set. -/
def affBCF (m c : ℝ) : Val :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => m * y.val + c) (by fun_prop))

@[simp] theorem affBCF_apply (m c : ℝ) (y : ↥(Sanctions.S : Set ℝ)) :
    affBCF m c y = m * y.val + c := rfl

/-- The myopic Sender's value: its stage payoff at zero sanction along the
policy, `U_S(x, a⁰⁰(x), 0)`. -/
def VS00 (hInt : E.Interior) (hP : E.Placable) : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) => E.U_S y.val (E.myopicPolicy y.val) 0, by
      have hα : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.myopicPolicy y.val) :=
        (E.myopicPolicy_continuous (E.uhi_lt_q hInt) (E.uhi_lt_k hP)).comp
          continuous_subtype_val
      exact E.U_S_continuous.comp (continuous_subtype_val.prodMk (hα.prodMk continuous_const))⟩

/-- The myopic Target's value: its stage payoff at zero sanction along the
policy, `U_T(x, a⁰⁰(x), 0)`. -/
def VT00 (hInt : E.Interior) (hP : E.Placable) : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) => E.U_T y.val (E.myopicPolicy y.val) 0, by
      have hα : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.myopicPolicy y.val) :=
        (E.myopicPolicy_continuous (E.uhi_lt_q hInt) (E.uhi_lt_k hP)).comp
          continuous_subtype_val
      exact E.U_T_continuous.comp (continuous_subtype_val.prodMk (hα.prodMk continuous_const))⟩

theorem VS00_apply (hInt : E.Interior) (hP : E.Placable) (y : ↥(Sanctions.S : Set ℝ)) :
    E.VS00 hInt hP y = E.U_S y.val (E.myopicPolicy y.val) 0 := rfl

theorem VT00_apply (hInt : E.Interior) (hP : E.Placable) (y : ↥(Sanctions.S : Set ℝ)) :
    E.VT00 hInt hP y = E.U_T y.val (E.myopicPolicy y.val) 0 := rfl

/-- The myopic Sender's value under the stage appetite `u_hi < q` and the stage
placability `u_hi < k_lo`: the same function as `VS00` (its stage payoff at zero
sanction along the policy), built from the two stage conditions that the
continuity proof reads (BH3.1, BH3.2, 2026-10-06). General in `F`. `VS00` keeps its
binders `hInt`, `hP` because headline row 35 names it. -/
def VS00s (hS : E.uhi < E.q) (hPs : E.uhi < E.klo) : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) => E.U_S y.val (E.myopicPolicy y.val) 0, by
      have hα : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.myopicPolicy y.val) :=
        (E.myopicPolicy_continuous hS hPs).comp continuous_subtype_val
      exact E.U_S_continuous.comp (continuous_subtype_val.prodMk (hα.prodMk continuous_const))⟩

/-- The myopic Target's value under the stage appetite and the stage placability:
the same function as `VT00` (BH3.1, BH3.2, 2026-10-06). General in `F`. -/
def VT00s (hS : E.uhi < E.q) (hPs : E.uhi < E.klo) : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) => E.U_T y.val (E.myopicPolicy y.val) 0, by
      have hα : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.myopicPolicy y.val) :=
        (E.myopicPolicy_continuous hS hPs).comp continuous_subtype_val
      exact E.U_T_continuous.comp (continuous_subtype_val.prodMk (hα.prodMk continuous_const))⟩

theorem VS00s_apply (hS : E.uhi < E.q) (hPs : E.uhi < E.klo) (y : ↥(Sanctions.S : Set ℝ)) :
    E.VS00s hS hPs y = E.U_S y.val (E.myopicPolicy y.val) 0 := rfl

theorem VT00s_apply (hS : E.uhi < E.q) (hPs : E.uhi < E.klo) (y : ↥(Sanctions.S : Set ℝ)) :
    E.VT00s hS hPs y = E.U_T y.val (E.myopicPolicy y.val) 0 := rfl

/-- The myopic Sender Bellman integrand is the stage payoff. -/
theorem pM_integrandS (V : Val) (y s : ℝ) :
    E.pM.integrandS E.myopicPolicy (fun z => V z) (y, s)
      = E.toParams.U_S y (E.myopicPolicy y) s := by
  simp [AbstractGame.Params.integrandS, AbstractGame.Params.profileβ_S, ContinuationProfile.p00]

/-- The myopic joint top integrand is the substituted stage payoff. -/
theorem pM_joint_T_top_integrand (V_T V_S : Val) {y : ℝ} (hy : y ∈ Sanctions.I) (a : ℝ) :
    E.pM.joint_T_top_integrand V_T V_S y a = E.toParams.U_T y a (E.toParams.σ y a) := by
  simp only [AbstractGame.Params.joint_T_top_integrand, E.pM_σ_dyn_top _ hy]
  simp [AbstractGame.Params.profileβ_T, ContinuationProfile.p00]

end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The fully myopic equilibrium of a chord economy**: a top-selector feedback
Stackelberg equilibrium at the myopic view, with the stage payoffs at zero
sanction along the partial-compliance policy as values. Rule 15: constructed. -/
def myopicEquilibriumTop (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable) :
    E.toParams.RegimeEquilibrium ContinuationProfile.p00 where
  V_T := E.VT00 hInt hP
  V_S := E.VS00 hInt hP
  α := E.myopicPolicy
  hα := E.myopicPolicy_continuous (E.uhi_lt_q hInt) (E.uhi_lt_k hP)
  α_mem := fun _ hx => E.myopicPolicy_mem (E.uhi_lt_k hP) hx
  V_S_fix := by
    ext y
    change E.VS00 hInt hP y = sSup ((fun s => E.pM.integrandS E.myopicPolicy (fun z => E.VS00 hInt
        hP z)
      (y.val, s)) '' Sanctions.I)
    have hgt : IsGreatest ((fun s => E.pM.integrandS E.myopicPolicy (fun z => E.VS00 hInt hP z)
        (y.val, s)) '' Sanctions.I)
        (E.toParams.U_S y.val (E.myopicPolicy y.val)
          (E.toParams.σ y.val (E.myopicPolicy y.val))) := by
      refine ⟨⟨_, E.toParams.σ_mem y.val (E.myopicPolicy y.val), E.pM_integrandS _ _ _⟩, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [E.pM_integrandS]
      exact E.toParams.σ_isMaxOn_U_S y.val (E.myopicPolicy y.val) hs
    rw [hgt.csSup_eq, E.σ_at_myopicPolicy (E.uhi_lt_k hP) y.property, E.VS00_apply hInt]
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => E.pM.joint_T_top_integrand (E.VT00 hInt hP) (E.VS00 hInt hP)
        y.val a)
        '' Sanctions.I)
        (E.toParams.U_T y.val (E.myopicPolicy y.val)
          (E.toParams.σ y.val (E.myopicPolicy y.val))) := by
      refine ⟨⟨_, E.myopicPolicy_mem (E.uhi_lt_k hP) y.property,
        E.pM_joint_T_top_integrand _ _ y.property _⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      dsimp only
      rw [E.pM_joint_T_top_integrand _ _ y.property]
      exact E.myopicPolicy_isMaxOn (E.uhi_lt_q hInt) hSR (E.uhi_lt_k hP) y.property ha
    rw [hgt.csSup_eq, E.σ_at_myopicPolicy (E.uhi_lt_k hP) y.property, E.VT00_apply hInt]
  α_opt_top := by
    intro x hx a ha
    simp only [Set.mem_setOf_eq]
    rw [E.pM_joint_T_top_integrand _ _ hx, E.pM_joint_T_top_integrand _ _ hx]
    exact E.myopicPolicy_isMaxOn (E.uhi_lt_q hInt) hSR (E.uhi_lt_k hP) hx ha

/-- **The fully myopic equilibrium under the stage conditions**: the same
top-selector equilibrium at the myopic view as `myopicEquilibriumTop`, built from
the stage appetite `u_hi < q`, the stage relief margin and the stage placability
`u_hi < k_lo` (BH3.1, BH3.2, 2026-10-06). General in `F`. Interiority `A < q` and
placability `A ≤ k_lo` bound the forward-looking Sender's appetite, which the
myopic reading never meets: here only the myopic Sender's appetite `u_hi` is
compared with the curvature and with the placation rate. `myopicEquilibriumTop`
keeps its binders (headline row 35 names it) and equals this object by `rfl`
(`myopicEquilibriumTop_eq_S`). Rule 15: constructed. -/
def myopicEquilibriumTopS (hS : E.uhi < E.q) (hSR : E.StageRelief) (hPs : E.uhi < E.klo) :
    E.toParams.RegimeEquilibrium ContinuationProfile.p00 where
  V_T := E.VT00s hS hPs
  V_S := E.VS00s hS hPs
  α := E.myopicPolicy
  hα := E.myopicPolicy_continuous hS hPs
  α_mem := fun _ hx => E.myopicPolicy_mem hPs hx
  V_S_fix := by
    ext y
    change E.VS00s hS hPs y = sSup ((fun s => E.pM.integrandS E.myopicPolicy
        (fun z => E.VS00s hS hPs z) (y.val, s)) '' Sanctions.I)
    have hgt : IsGreatest ((fun s => E.pM.integrandS E.myopicPolicy (fun z => E.VS00s hS hPs z)
        (y.val, s)) '' Sanctions.I)
        (E.toParams.U_S y.val (E.myopicPolicy y.val)
          (E.toParams.σ y.val (E.myopicPolicy y.val))) := by
      refine ⟨⟨_, E.toParams.σ_mem y.val (E.myopicPolicy y.val), E.pM_integrandS _ _ _⟩, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [E.pM_integrandS]
      exact E.toParams.σ_isMaxOn_U_S y.val (E.myopicPolicy y.val) hs
    rw [hgt.csSup_eq, E.σ_at_myopicPolicy hPs y.property, E.VS00s_apply hS]
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => E.pM.joint_T_top_integrand (E.VT00s hS hPs)
        (E.VS00s hS hPs) y.val a) '' Sanctions.I)
        (E.toParams.U_T y.val (E.myopicPolicy y.val)
          (E.toParams.σ y.val (E.myopicPolicy y.val))) := by
      refine ⟨⟨_, E.myopicPolicy_mem hPs y.property,
        E.pM_joint_T_top_integrand _ _ y.property _⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      dsimp only
      rw [E.pM_joint_T_top_integrand _ _ y.property]
      exact E.myopicPolicy_isMaxOn hS hSR hPs y.property ha
    rw [hgt.csSup_eq, E.σ_at_myopicPolicy hPs y.property, E.VT00s_apply hS]
  α_opt_top := by
    intro x hx a ha
    simp only [Set.mem_setOf_eq]
    rw [E.pM_joint_T_top_integrand _ _ hx, E.pM_joint_T_top_integrand _ _ hx]
    exact E.myopicPolicy_isMaxOn hS hSR hPs hx ha

/-- **The bridge**: the pinned myopic equilibrium is the stage-form one at the
stage parts `uhi_lt_q`, `uhi_lt_k` of interiority and placability. Definitional
(the two differ only in proof terms). -/
theorem myopicEquilibriumTop_eq_S (hInt : E.Interior) (hSR : E.StageRelief)
    (hP : E.Placable) :
    E.myopicEquilibriumTop hInt hSR hP
      = E.myopicEquilibriumTopS (E.uhi_lt_q hInt) hSR (E.uhi_lt_k hP) := rfl

/-- **The realised myopic sanction is zero** at every feasible state, at the
stage-form myopic equilibrium. General in `F`; under the stage appetite and the
stage placability (BH3.1, BH3.2). -/
theorem myopicRuleS_eq_zero (hS : E.uhi < E.q) (hSR : E.StageRelief) (hPs : E.uhi < E.klo)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTopS hS hSR hPs) x = 0 := by
  change E.pM.σ_dyn_top (E.VS00s hS hPs) x (E.myopicPolicy x) = 0
  rw [E.pM_σ_dyn_top _ hx]
  exact E.σ_at_myopicPolicy hPs hx

/-- **The realised myopic sanction is zero** at every feasible state. The
interiority and placability form of `myopicRuleS_eq_zero`. -/
theorem myopicRule_eq_zero (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable) {x : ℝ}
    (hx : x ∈ Sanctions.I) :
    E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTop hInt hSR hP) x = 0 := by
  rw [E.myopicEquilibriumTop_eq_S]; exact E.myopicRuleS_eq_zero _ hSR _ hx

/-- **Uniqueness of the myopic policy at the stage-form equilibrium**: every
maximiser of the myopic joint objective is the partial-compliance policy. General
in `F`; under the stage appetite and the stage placability (BH3.1, BH3.2). -/
theorem myopicEquilibriumTopS_argmax_unique (hS : E.uhi < E.q) (hSR : E.StageRelief)
    (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.pM.joint_T_top_integrand
      (E.myopicEquilibriumTopS hS hSR hPs).V_T
      (E.myopicEquilibriumTopS hS hSR hPs).V_S x b) Sanctions.I a) :
    a = (E.myopicEquilibriumTopS hS hSR hPs).α x := by
  apply E.myopic_target_unique hS hSR hPs hx ha
  intro b hb
  have := hmax hb
  simp only [Set.mem_setOf_eq] at this ⊢
  change E.pM.joint_T_top_integrand (E.VT00s hS hPs) (E.VS00s hS hPs) x b
    ≤ E.pM.joint_T_top_integrand (E.VT00s hS hPs) (E.VS00s hS hPs) x a at this
  rwa [E.pM_joint_T_top_integrand _ _ hx, E.pM_joint_T_top_integrand _ _ hx] at this

/-- **Uniqueness of the myopic policy at the constructed equilibrium**: every
maximiser of the myopic joint objective is the partial-compliance policy. The
interiority and placability form of `myopicEquilibriumTopS_argmax_unique`. -/
theorem myopicEquilibriumTop_argmax_unique (hInt : E.Interior) (hSR : E.StageRelief)
    (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.pM.joint_T_top_integrand (E.myopicEquilibriumTop hInt hSR hP).V_T
      (E.myopicEquilibriumTop hInt hSR hP).V_S x b) Sanctions.I a) :
    a = (E.myopicEquilibriumTop hInt hSR hP).α x := by
  rw [E.myopicEquilibriumTop_eq_S] at hmax ⊢
  exact E.myopicEquilibriumTopS_argmax_unique _ hSR _ hx ha hmax

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 3. The two paths -/

/-- **The forward-looking realised rule is the response at defiance, given a
nondecreasing response** (renovation item BH4.1, 2026-10-06). General in `F`. At the
constructed equilibrium `equilibriumTop hTM hmono`, built from the loss-offset margin and
a response `responsePath VSstar` that is nondecreasing on `[0, 1]`, the realised sanction
rule is that response. Neither hypothesis is read beyond naming the equilibrium. -/
theorem dynamicRule_eq_responsePath_of_response_monotone (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono) x
      = E.responsePath E.VSstar x := by
  change E.toParams.σ_dyn_top E.VSstar x 0 = E.response E.VSstar x 0
  exact (E.response_eq_top E.VSstar_mem hx 0).symm

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- The forward-looking realised rule is the response at defiance. General in `F`. The
rally-margin form of `dynamicRule_eq_responsePath_of_response_monotone` (BH4.1). On the
two-sided extension since renovation item BJ3.1 (2026-10-07): the rally margin reads the
two-sided curvature data. -/
theorem dynamicRule_eq_responsePath (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x
      = E.responsePath E.VSstar x :=
  E.dynamicRule_eq_responsePath_of_response_monotone hTM
    (E.responsePath_monotoneOn_of_margin hmargin) hx

end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- The state path under the myopic equilibrium. -/
def myopicPath (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable) (x₀ : ℝ) (t : ℕ) :
    ℝ :=
  E.toParams.rulePathF (E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTop hInt hSR hP)) x₀ t

/-- The state path under the stage-form myopic equilibrium (BH3.1, BH3.2). General
in `F`. -/
def myopicPathS (hS : E.uhi < E.q) (hSR : E.StageRelief) (hPs : E.uhi < E.klo) (x₀ : ℝ)
    (t : ℕ) : ℝ :=
  E.toParams.rulePathF (E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTopS hS hSR hPs)) x₀ t

/-- **The path bridge**: the pinned myopic path is the stage-form one at the stage
parts of interiority and placability. Definitional. -/
theorem myopicPath_eq_S (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable) :
    E.myopicPath hInt hSR hP = E.myopicPathS (E.uhi_lt_q hInt) hSR (E.uhi_lt_k hP) := rfl

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **The state path under the forward-looking equilibrium, given a nondecreasing
response** (renovation item BH4.1, 2026-10-06). General in `F`. It is the path of the
constructed equilibrium `equilibriumTop hTM hmono`. Beside the loss-offset margin it takes
only what the rally margin of `dynamicPath` was used for: a response `responsePath VSstar`
that is nondecreasing on `[0, 1]`. That is a condition on an endogenous object, not
checkable from the primitives alone; the rally margin implies it
(`responsePath_monotoneOn_of_margin`) and is strictly stronger
(`exists_member_response_monotone_not_margin`). -/
def dynamicPathOf (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) (x₀ : ℝ) (t : ℕ) : ℝ :=
  E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono)) x₀ t

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- The state path under the forward-looking equilibrium, given the margin. On the
two-sided extension since renovation item BJ3.1 (2026-10-07). -/
def dynamicPath (hTM : E.LossOffset) (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 *
    E.SigC) * E.Mmix) ≤ E.rlo)
    (x₀ : ℝ) (t : ℕ) : ℝ :=
  E.toParams.rulePathF (E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin)) x₀ t

/-- **The path bridge** (BH4.1): the rally-margin path is the monotone-response path at
the nondecreasing response that the margin gives. Definitional. General in `F`.
On the two-sided extension since renovation item BJ3.1 (2026-10-07). -/
theorem dynamicPath_eq_dynamicPathOf (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    E.dynamicPath hTM hmargin
      = E.dynamicPathOf hTM (E.responsePath_monotoneOn_of_margin hmargin) := rfl

end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **Wash-out under the stage-form myopic equilibrium**: geometric decay at rate
`1 − d_lo`. General in `F`; under the stage appetite and the stage placability
(BH3.1, BH3.2). -/
theorem myopicPathS_le_geom (hS : E.uhi < E.q) (hSR : E.StageRelief) (hPs : E.uhi < E.klo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E.myopicPathS hS hSR hPs) x₀ t ≤ (1 - E.dlo) ^ t * x₀ :=
  E.toParams.rulePathF_le_geom_of_zero_rule E.hSlo
    (fun _ hx => (E.myopicRuleS_eq_zero hS hSR hPs) hx) hx₀

/-- The stage-form myopic path converges to zero. General in `F`; under the stage
appetite and the stage placability (BH3.1, BH3.2). -/
theorem myopicPathS_tendsto_zero (hS : E.uhi < E.q) (hSR : E.StageRelief)
    (hPs : E.uhi < E.klo) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Tendsto ((E.myopicPathS hS hSR hPs) x₀) atTop (𝓝 0) :=
  E.toParams.rulePathF_tendsto_zero_of_zero_rule E.hdlo0 E.hSlo
    (fun _ hx => (E.myopicRuleS_eq_zero hS hSR hPs) hx) hx₀

/-- **Wash-out under the myopic equilibrium**: geometric decay at rate `1 − d_lo`.
The interiority and placability form of `myopicPathS_le_geom`. -/
theorem myopicPath_le_geom (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E.myopicPath hInt hSR hP) x₀ t ≤ (1 - E.dlo) ^ t * x₀ := by
  rw [E.myopicPath_eq_S]; exact E.myopicPathS_le_geom _ hSR _ hx₀

/-- The myopic path converges to zero. The interiority and placability form of
`myopicPathS_tendsto_zero`. -/
theorem myopicPath_tendsto_zero (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Tendsto ((E.myopicPath hInt hSR hP) x₀) atTop (𝓝 0) := by
  rw [E.myopicPath_eq_S]; exact E.myopicPathS_tendsto_zero _ hSR _ hx₀

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)

/-- The realised rule of `equilibriumTop hTM hmono` maps `[0, 1]` into itself (BH4.1).
General in `F`. -/
theorem dynamicRule_mem_of_response_monotone (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    ∀ x ∈ Sanctions.I,
      E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono) x ∈ Sanctions.I :=
  fun _ _ => E.toParams.σ_dyn_top_mem_I _ _ _

/-- **Wash-in under the forward-looking equilibrium, given a nondecreasing response**
(BH4.1, 2026-10-06): the state dominates `(u₀/q)(1 − (1 − d_lo)^t)`. General in `F`. The
nondecreasing response only names the equilibrium; the bound reads that the realised
rule is at least the sanction floor. -/
theorem dynamicPath_ge_approach_of_response_monotone (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, approach E.sfloor E.dlo t ≤ E.dynamicPathOf hTM hmono x₀ t :=
  E.toParams.rulePathF_ge_approach_of_rule_ge E.hdlo0.le E.hSlo E.sfloor_mem
    (E.dynamicRule_mem_of_response_monotone hTM hmono)
    (fun x hx => by
      rw [E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hx]
      exact E.responsePath_ge_sfloor E.VSstar_mem hx) hx₀

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- The realised rule maps `[0, 1]` into itself. General in `F`. The rally-margin form of
`dynamicRule_mem_of_response_monotone` (BH4.1). On the two-sided extension since
renovation item BJ3.1 (2026-10-07). -/
theorem dynamicRule_mem (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    ∀ x ∈ Sanctions.I,
      E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x ∈ Sanctions.I :=
  E.dynamicRule_mem_of_response_monotone hTM (E.responsePath_monotoneOn_of_margin hmargin)

/-- **Wash-in under the forward-looking equilibrium, with no margin beyond the
composed equilibrium's own**: the state dominates `(u₀/q)(1 − (1 − d_lo)^t)`. General in
`F`. The rally-margin form of `dynamicPath_ge_approach_of_response_monotone` (BH4.1).
On the two-sided extension since renovation item BJ3.1 (2026-10-07). -/
theorem dynamicPath_ge_approach (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, approach E.sfloor E.dlo t ≤ (E.dynamicPath hTM) hmargin x₀ t :=
  E.dynamicPath_ge_approach_of_response_monotone hTM
    (E.responsePath_monotoneOn_of_margin hmargin) hx₀

/-- **Eventually within `ε` of the floor**: the forward-looking path is eventually at
least `b − ε`, `b = σ(0,0)`, from every feasible start. General in `F`. On the two-sided
extension since renovation item BJ3.1 (2026-10-07). -/
theorem dynamicPath_eventually_ge (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, E.sfloor - ε ≤ (E.dynamicPath hTM) hmargin x₀ t :=
  eventually_ge_of_ge_approach E.hdlo0 E.dlo_le_one ((E.dynamicPath_ge_approach hTM) hmargin hx₀) hε

end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The forward-looking path strictly dominates the stage-form myopic path, given a
nondecreasing response** (BH4.1, 2026-10-06), from a common feasible start, at every
positive date. General in `F`; under the stage appetite and the stage placability. The
nondecreasing response only names the forward-looking equilibrium; the domination reads
that its realised rule is positive. -/
theorem myopicPathS_lt_dynamicPath_of_response_monotone (hS : E.uhi < E.q)
    (hSR : E.StageRelief) (hTM : E.LossOffset) (hPs : E.uhi < E.klo)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E.myopicPathS hS hSR hPs) x₀ t ≤ E.dynamicPathOf hTM hmono x₀ t
      ∧ (1 ≤ t → (E.myopicPathS hS hSR hPs) x₀ t < E.dynamicPathOf hTM hmono x₀ t) := by
  have hzero : ∀ t, (E.myopicPathS hS hSR hPs) x₀ t
      = E.toParams.rulePathF (fun _ => 0) x₀ t :=
    E.toParams.rulePathF_congr_on
      (fun x hx => by rw [(E.myopicRuleS_eq_zero hS hSR hPs) hx]; exact ⟨le_rfl, zero_le_one⟩)
      (fun x hx => (E.myopicRuleS_eq_zero hS hSR hPs) hx) hx₀
  have h := E.toParams.rulePathF_gt_zero_rule_of_pos E.hdlo0 E.hSlo
    (E.dynamicRule_mem_of_response_monotone hTM hmono)
    (fun x hx => by
      rw [E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hx]
      exact E.responsePath_pos E.VSstar_mem hx) hx₀
  intro t
  rw [hzero t]
  exact h t

/-- **The forward-looking path strictly dominates the stage-form myopic path** from
a common feasible start, at every positive date. General in `F`; under the stage
appetite and the stage placability (BH3.1, BH3.2). The rally-margin form of
`myopicPathS_lt_dynamicPath_of_response_monotone` (BH4.1). -/
theorem myopicPathS_lt_dynamicPath (hS : E.uhi < E.q) (hSR : E.StageRelief)
    (hTM : E.LossOffset) (hPs : E.uhi < E.klo)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E.myopicPathS hS hSR hPs) x₀ t ≤ (E.dynamicPath hTM) hmargin x₀ t
      ∧ (1 ≤ t → (E.myopicPathS hS hSR hPs) x₀ t < (E.dynamicPath hTM) hmargin x₀ t) :=
  E.myopicPathS_lt_dynamicPath_of_response_monotone hS hSR hTM hPs
    (E.responsePath_monotoneOn_of_margin hmargin) hx₀

/-- **The forward-looking path strictly dominates the myopic path** from a common
feasible start, at every positive date. The interiority and placability form of
`myopicPathS_lt_dynamicPath`. -/
theorem myopicPath_lt_dynamicPath (hInt : E.Interior) (hSR : E.StageRelief)
    (hTM : E.LossOffset) (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E.myopicPath hInt hSR hP) x₀ t ≤ (E.dynamicPath hTM) hmargin x₀ t
      ∧ (1 ≤ t → (E.myopicPath hInt hSR hP) x₀ t < (E.dynamicPath hTM) hmargin x₀ t) := by
  rw [E.myopicPath_eq_S]; exact E.myopicPathS_lt_dynamicPath _ hSR hTM _ hmargin hx₀

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **The forward-looking path converges to an interior steady state, given a
nondecreasing response** (renovation item BH4.1, 2026-10-06): `ρ(x∞) = x∞ ∈ (u₀/q, A/q]`.
General in `F`; under the stage appetite `u_hi < q`. This is `dynamicPath_tendsto` with
the rally margin replaced by the one thing it was used for: the realised rule is
nondecreasing, so the path is monotone and converges (the response is continuous without
any margin). The limit may depend on the start; uniqueness is a separate question (§5). -/
theorem dynamicPath_tendsto_of_response_monotone (hS : E.uhi < E.q) (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
      Tendsto (E.dynamicPathOf hTM hmono x₀) atTop (𝓝 z) := by
  have hrule : MonotoneOn (E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono))
      Sanctions.I := by
    intro x hx y hy hxy
    rw [E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hx,
      E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hy]
    exact hmono hx hy hxy
  have hcont : ContinuousOn (E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono))
      Sanctions.I :=
    (E.responsePath_continuousOn E.VSstar_mem).congr
      (fun x hx => E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hx)
  obtain ⟨z, hz, hfix, htend⟩ := E.toParams.rulePathF_tendsto_fixedPoint_of_monotoneOn
    (E.dynamicRule_mem_of_response_monotone hTM hmono) hrule hcont hx₀
  have hrz := E.toParams.rule_eq_self_of_closedLoop_fixed E.hdlo0 E.hSlo hz
    (E.dynamicRule_mem_of_response_monotone hTM hmono z hz) hfix
  rw [E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hz] at hrz
  refine ⟨z, hz, hrz, ?_, ?_, htend⟩
  · rw [← hrz]; exact E.responsePath_gt_sfloor hS E.VSstar_mem hz
  · rw [← hrz]; exact E.responsePath_le_cap E.VSstar_mem hz

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- **The forward-looking path converges to an interior steady state** at which
the sanction equals the state: `ρ(x∞) = x∞ ∈ (u₀/q, A/q]`. The limit may depend
on the start; uniqueness is a separate question (§5). General in `F`. Under the
stage appetite `u_hi < q`, which makes the limit strictly exceed the floor (BH3.1,
2026-10-06: the binder was interiority `A < q`; the cap `A/q` bounds the limit
whether or not it is below one). The rally-margin form of
`dynamicPath_tendsto_of_response_monotone` (BH4.1). On the two-sided extension since
renovation item BJ3.1 (2026-10-07). -/
theorem dynamicPath_tendsto (hS : E.uhi < E.q) (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
      Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z) :=
  E.dynamicPath_tendsto_of_response_monotone hS hTM
    (E.responsePath_monotoneOn_of_margin hmargin) hx₀

end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-! ## 4. The capstone -/

/-- **Re-solved continuation-regime separation under the stage conditions and a
nondecreasing response, general in `F`** (renovation item BH4.1, 2026-10-06). The
separation of `myopic_dynamic_equilibrium_separation_generalF_stage`, with the rally
margin replaced by a response `responsePath VSstar` that is nondecreasing on `[0, 1]`,
read at the constructed forward-looking equilibrium `equilibriumTop hTM hmono` and its
path `dynamicPathOf hTM hmono`. The myopic Target complies partially and uniquely, buys a
zero sanction, and the state washes out. The forward-looking Target defies, the sanction
is strictly above the stage vertex and at most `A/q`, the state dominates the myopic state
at every positive date from any common start, and it converges to a steady state with
sanction equal to state in `(b, A/q]`. The rally margin was read only to make the
response nondecreasing (`responsePath_monotoneOn_of_margin`); only the limit clause uses
that monotonicity. In plain terms: what separates the regimes on the forward-looking side
is that a higher state never lowers the Sender's sanction against a defiant Target, not
the particular rate inequality that guarantees it. The nondecreasing response is a
condition on the constructed Sender value, so it is not checkable from the primitives
alone; the rally margin is one sufficient condition. -/
theorem myopic_dynamic_equilibrium_separation_generalF_stage_of_response_monotone
    (hS : E.uhi < E.q) (hSR : E.StageRelief) (hTM : E.LossOffset) (hPs : E.uhi < E.klo)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    -- (1) the same primitives at both views
    (E.pM.U_T = E.toParams.U_T ∧ E.pM.U_S = E.toParams.U_S ∧ E.pM.F = E.toParams.F) ∧
    -- (2) the myopic equilibrium: interior partial compliance, unique, zero sanction, wash-out
    (∀ x ∈ Sanctions.I,
      (E.myopicEquilibriumTopS hS hSR hPs).α x ∈ Ioo (0 : ℝ) 1 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pM.joint_T_top_integrand (E.myopicEquilibriumTopS hS hSR hPs).V_T
          (E.myopicEquilibriumTopS hS hSR hPs).V_S x b) Sanctions.I a →
            a = (E.myopicEquilibriumTopS hS hSR hPs).α x) ∧
      E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTopS hS hSR hPs) x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, (E.myopicPathS hS hSR hPs) x₀ t ≤ (1 - E.dlo) ^ t * x₀) ∧
      Tendsto ((E.myopicPathS hS hSR hPs) x₀) atTop (𝓝 0)) ∧
    -- (3) the forward-looking equilibrium: defiance, strict wedge, the cap
    (∀ x ∈ Sanctions.I,
      (E.equilibriumTop hTM hmono).α x = 0 ∧
      E.toParams.σ x 0 < E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono) x ∧
      E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono) x ≤ E.cap) ∧
    -- (4) paths: wash-in, strict dominance, the limit
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach E.sfloor E.dlo t ≤ E.dynamicPathOf hTM hmono x₀ t) ∧
      (∀ t, 1 ≤ t → (E.myopicPathS hS hSR hPs) x₀ t < E.dynamicPathOf hTM hmono x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
        Tendsto (E.dynamicPathOf hTM hmono x₀) atTop (𝓝 z)) := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(E.myopicPolicy_mem_Ioo hPs) hx,
      fun a ha hmax => (E.myopicEquilibriumTopS_argmax_unique hS hSR hPs) hx ha hmax,
      (E.myopicRuleS_eq_zero hS hSR hPs) hx⟩
  · intro x₀ hx₀
    exact ⟨(E.myopicPathS_le_geom hS hSR hPs) hx₀, (E.myopicPathS_tendsto_zero hS hSR hPs) hx₀⟩
  · intro x hx
    refine ⟨rfl, ?_, ?_⟩
    · rw [E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hx]
      exact E.responsePath_gt_stage hS E.VSstar_mem hx
    · rw [E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hx]
      exact E.responsePath_le_cap E.VSstar_mem hx
  · intro x₀ hx₀
    exact ⟨E.dynamicPath_ge_approach_of_response_monotone hTM hmono hx₀,
      fun t ht =>
        (E.myopicPathS_lt_dynamicPath_of_response_monotone hS hSR hTM hPs hmono hx₀ t).2 ht,
      E.dynamicPath_tendsto_of_response_monotone hS hTM hmono hx₀⟩

/-- **Re-solved continuation-regime separation under the stage conditions, general
in `F`** (renovation items BH3.1, BH3.2, 2026-10-06). The same separation as the
pinned `myopic_dynamic_equilibrium_separation_generalF`, with interiority
`A = u_hi + β_S·K_S·d_hi < q` weakened to the stage appetite `u_hi < q` and
placability `A ≤ k_lo` weakened to the stage placability `u_hi < k_lo`, at the
stage-form myopic equilibrium `E.myopicEquilibriumTopS hS hSR hPs` (equal by `rfl`
to the pinned one when interiority and placability hold). The myopic Target complies
partially and uniquely, buys a zero sanction, and the state washes out. The
forward-looking Target defies, the sanction is strictly above the stage vertex and
at most `A/q`, the state dominates the myopic state at every positive date from
any common start, and it converges to a steady state with sanction equal to state
in `(b, A/q]`. The one clause dropped is `A/q < 1` (the forward-looking sanction is
interior from above), the only place interiority itself is read; it returns under
`hInt` through `cap_lt_one`. In plain terms: regime separation needs only that the
myopic Sender would not sanction fully (`u_hi < q`) and that full compliance would
placate it (`u_hi < k_lo`); neither condition involves the Sender's patience or
the transition. The rally-margin form of
`myopic_dynamic_equilibrium_separation_generalF_stage_of_response_monotone` (BH4.1), at
`hmono := responsePath_monotoneOn_of_margin hmargin`. -/
theorem myopic_dynamic_equilibrium_separation_generalF_stage (hS : E.uhi < E.q)
    (hSR : E.StageRelief) (hTM : E.LossOffset) (hPs : E.uhi < E.klo)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    -- (1) the same primitives at both views
    (E.pM.U_T = E.toParams.U_T ∧ E.pM.U_S = E.toParams.U_S ∧ E.pM.F = E.toParams.F) ∧
    -- (2) the myopic equilibrium: interior partial compliance, unique, zero sanction, wash-out
    (∀ x ∈ Sanctions.I,
      (E.myopicEquilibriumTopS hS hSR hPs).α x ∈ Ioo (0 : ℝ) 1 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pM.joint_T_top_integrand (E.myopicEquilibriumTopS hS hSR hPs).V_T
          (E.myopicEquilibriumTopS hS hSR hPs).V_S x b) Sanctions.I a →
            a = (E.myopicEquilibriumTopS hS hSR hPs).α x) ∧
      E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTopS hS hSR hPs) x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, (E.myopicPathS hS hSR hPs) x₀ t ≤ (1 - E.dlo) ^ t * x₀) ∧
      Tendsto ((E.myopicPathS hS hSR hPs) x₀) atTop (𝓝 0)) ∧
    -- (3) the forward-looking equilibrium: defiance, strict wedge, the cap
    (∀ x ∈ Sanctions.I,
      ((E.equilibriumTop_of_margin hTM) hmargin).α x = 0 ∧
      E.toParams.σ x 0
        < E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x ∧
      E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x ≤ E.cap) ∧
    -- (4) paths: wash-in, strict dominance, the limit
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach E.sfloor E.dlo t ≤ (E.dynamicPath hTM) hmargin x₀ t) ∧
      (∀ t, 1 ≤ t → (E.myopicPathS hS hSR hPs) x₀ t < (E.dynamicPath hTM) hmargin x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
        Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z)) :=
  E.myopic_dynamic_equilibrium_separation_generalF_stage_of_response_monotone hS hSR hTM hPs
    (E.responsePath_monotoneOn_of_margin hmargin)

/-- **Re-solved continuation-regime separation on the placable family, general
in `F`.** One economy; two constructed top-selector equilibria — the fully
myopic `E.myopicEquilibriumTop hInt hSR hP` at the `p00` view and the fully forward-looking
`(E.equilibriumTop_of_margin hTM) hmargin` at the economy itself — with identical
stage payoffs and transition. The myopic Target complies partially and
uniquely, buys a zero sanction, and the state washes out. The forward-looking
Target defies, the sanction is interior and strictly above the stage vertex,
the state dominates the myopic state at every positive date from any common
start, and it converges to a steady state with sanction equal to state in
`(u₀/q, A/q]`. (The activation of both channels at the forward-looking
equilibrium is `both_channels_active_of_margin`, under the stage flip, and
`ChordEconomyCs.both_channels_active_of_relief` under (RL); it left this
statement in round Q2 so that the separation needs no flip.) A pinned headline, so
it keeps interiority and placability; it is the corollary of
`myopic_dynamic_equilibrium_separation_generalF_stage` at their stage parts
(`uhi_lt_q`, `uhi_lt_k`) through the bridges `myopicEquilibriumTop_eq_S` and
`myopicPath_eq_S`, with `A/q < 1` added from interiority (`cap_lt_one`) (BH3.1,
BH3.2, 2026-10-06). -/
theorem myopic_dynamic_equilibrium_separation_generalF (hInt : E.Interior)
    (hSR : E.StageRelief) (hTM : E.LossOffset) (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    -- (1) the same primitives at both views
    (E.pM.U_T = E.toParams.U_T ∧ E.pM.U_S = E.toParams.U_S ∧ E.pM.F = E.toParams.F) ∧
    -- (2) the myopic equilibrium: interior partial compliance, unique, zero sanction, wash-out
    (∀ x ∈ Sanctions.I,
      (E.myopicEquilibriumTop hInt hSR hP).α x ∈ Ioo (0 : ℝ) 1 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pM.joint_T_top_integrand (E.myopicEquilibriumTop hInt hSR hP).V_T
          (E.myopicEquilibriumTop hInt hSR hP).V_S x b) Sanctions.I a → a = (E.myopicEquilibriumTop
              hInt hSR hP).α x) ∧
      E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTop hInt hSR hP) x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, (E.myopicPath hInt hSR hP) x₀ t ≤ (1 - E.dlo) ^ t * x₀) ∧
      Tendsto ((E.myopicPath hInt hSR hP) x₀) atTop (𝓝 0)) ∧
    -- (3) the forward-looking equilibrium: defiance, strict wedge, interior cap
    (∀ x ∈ Sanctions.I,
      ((E.equilibriumTop_of_margin hTM) hmargin).α x = 0 ∧
      E.toParams.σ x 0
        < E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x ∧
      E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x ≤ E.cap ∧
      E.cap < 1) ∧
    -- (4) paths: wash-in, strict dominance, interior limit
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach E.sfloor E.dlo t ≤ (E.dynamicPath hTM) hmargin x₀ t) ∧
      (∀ t, 1 ≤ t → (E.myopicPath hInt hSR hP) x₀ t < (E.dynamicPath hTM) hmargin x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
        Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := E.myopic_dynamic_equilibrium_separation_generalF_stage
    (E.uhi_lt_q hInt) hSR hTM (E.uhi_lt_k hP) hmargin
  rw [E.myopicEquilibriumTop_eq_S, E.myopicPath_eq_S]
  exact ⟨h1, h2, h3,
    fun x hx => ⟨(h4 x hx).1, (h4 x hx).2.1, (h4 x hx).2.2, E.cap_lt_one hInt⟩, h5⟩

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 5. The closed loop as a self-map: contraction and its consequences -/

/-- The forward-looking closed loop `x ↦ F(x, ρ(x))` at the constructed Sender
value. -/
def closedLoop (x : ℝ) : ℝ := E.F x (E.responsePath E.VSstar x)

theorem closedLoop_maps {x : ℝ} (hx : x ∈ Sanctions.I) : E.closedLoop x ∈ Sanctions.I :=
  E.F_mem _ _ hx (E.responsePath_mem _ _)

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- The closed loop's Lipschitz constant, closed form: `g_hi + d_hi·4L_resp/μ` (the
factor-four form of round D; the sharp constant is `LloopSharp` below). On the
two-sided extension since renovation item BJ3.1 (2026-10-07), with `L_resp`. -/
def Lloop : ℝ := E.ghi + E.dhi * (4 * E.Lresp / E.mu)

/-- The closed loop's sharp Lipschitz constant, closed form: `g_hi + d_hi·L_resp/μ`.
On the two-sided extension since renovation item BJ3.1 (2026-10-07). -/
def LloopSharp : ℝ := E.ghi + E.dhi * (E.Lresp / E.mu)

end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

theorem Lloop_nonneg : 0 ≤ E.Lloop :=
  add_nonneg E.ghi_nonneg
    (mul_nonneg E.dhi_nonneg (div_nonneg (by linarith [E.Lresp_nonneg]) E.mu_pos.le))

theorem closedLoop_lipschitz :
    ∀ x ∈ Sanctions.I, ∀ y ∈ Sanctions.I,
      |E.closedLoop x - E.closedLoop y| ≤ E.Lloop * |x - y| :=
  fun _ hx _ hy => E.successor_lipschitz hx hy

end ChordEconomyRelief

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- The forward-looking path is the iterated closed loop. On the two-sided extension
since renovation item BJ3.1 (2026-10-07). -/
theorem dynamicPath_eq_closedLoop_iterate (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E.dynamicPath hTM) hmargin x₀ t = E.closedLoop^[t] x₀ := by
  have h := E.toParams.rulePathF_congr_on (R₂ := E.responsePath E.VSstar)
    ((E.dynamicRule_mem hTM) hmargin) (fun x hx => (E.dynamicRule_eq_responsePath hTM) hmargin hx) hx₀
  intro t
  rw [dynamicPath, h t]
  rfl

end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **A geometric bound on the distance between two resumed paths**: after a
finite shock ends and the same equilibrium resumes at states `x` and `y`, the
paths are within `L_loop^n·|x − y|` after `n` periods. A propagation bound: the
paths approach each other when `L_loop < 1`, which is not a hypothesis here
(wording corrected 2026-09-15, the reader's 09-12 package). -/
theorem closedLoop_iterate_dist_le {x y : ℝ} (hx : x ∈ Sanctions.I) (hy : y ∈ Sanctions.I) :
    ∀ n, |E.closedLoop^[n] x - E.closedLoop^[n] y| ≤ E.Lloop ^ n * |x - y| :=
  Sanctions.IntervalContraction.iterate_dist_le E.Lloop_nonneg (fun _ hz => E.closedLoop_maps hz)
    E.closedLoop_lipschitz hx hy

/-! ### The sharp constant (round L, doc 80 M1)

`Lloop` carries the factor four of the midpoint chord. The sharp argmax
stability lemma removes it: the same closed loop is
`g_hi + d_hi·L_resp/μ`-Lipschitz (`successor_lipschitz_sharp`). The old constant,
theorems and snapshot rows are kept as they are, and `Lloop < 1` implies
`LloopSharp < 1` (`LloopSharp_le_Lloop`), never the reverse. Since renovation item
BH3.5 (2026-10-06) the factor-four `closedLoop_unique_attracting_of_lt_one` is the
corollary of the sharp form through that inequality, and the class theorem
`unique_attracting_state_of_sharp_lt_one` carries the members' statements. -/

theorem LloopSharp_nonneg : 0 ≤ E.LloopSharp :=
  add_nonneg E.ghi_nonneg (mul_nonneg E.dhi_nonneg (div_nonneg E.Lresp_nonneg E.mu_pos.le))

/-- The sharp constant is at most the factor-four one. -/
theorem LloopSharp_le_Lloop : E.LloopSharp ≤ E.Lloop := by
  unfold LloopSharp Lloop
  have h : E.Lresp / E.mu ≤ 4 * E.Lresp / E.mu := by
    rw [div_le_div_iff_of_pos_right E.mu_pos]; linarith [E.Lresp_nonneg]
  nlinarith [mul_le_mul_of_nonneg_left h E.dhi_nonneg]

theorem closedLoop_lipschitz_sharp :
    ∀ x ∈ Sanctions.I, ∀ y ∈ Sanctions.I,
      |E.closedLoop x - E.closedLoop y| ≤ E.LloopSharp * |x - y| :=
  fun _ hx _ hy => E.successor_lipschitz_sharp hx hy

/-- **The same geometric bound at the sharp rate** `L_loop^sharp`; approach
when it is below one. -/
theorem closedLoop_iterate_dist_le_sharp {x y : ℝ} (hx : x ∈ Sanctions.I)
    (hy : y ∈ Sanctions.I) :
    ∀ n, |E.closedLoop^[n] x - E.closedLoop^[n] y| ≤ E.LloopSharp ^ n * |x - y| :=
  Sanctions.IntervalContraction.iterate_dist_le E.LloopSharp_nonneg
    (fun _ hz => E.closedLoop_maps hz) E.closedLoop_lipschitz_sharp hx hy

/-- **A closed loop contracting at the sharp constant has one globally attracting
steady state**: when `LloopSharp < 1`, the steady state is unique in `[0,1]`, every
feasible start converges to it, and finite shocks are asymptotically irrelevant.
It holds at the non-affine member `placableQuadDiag` (`35/47`) where the
factor-four constant (`277/235`) does not. General in `F`. -/
theorem closedLoop_unique_attracting_of_sharp_lt_one (hL : E.LloopSharp < 1) :
    ∃ z ∈ Sanctions.I, E.closedLoop z = z ∧
      (∀ y ∈ Sanctions.I, E.closedLoop y = y → y = z) ∧
      ∀ x ∈ Sanctions.I, Tendsto (fun n => E.closedLoop^[n] x) atTop (𝓝 z) :=
  Sanctions.IntervalContraction.exists_unique_fixedPoint_and_tendsto zero_le_one
    E.LloopSharp_nonneg hL (fun _ hz => E.closedLoop_maps hz) E.closedLoop_lipschitz_sharp

/-- **A contracting closed loop has one globally attracting steady state.** When
`L_loop < 1`, the steady state is unique in `[0,1]`, every feasible start
converges to it, and finite shocks are asymptotically irrelevant. This is the
scope certificate for the hysteresis narrative on such a member: both
channels active, no same-equilibrium hysteresis. General in `F`. Since renovation
item BH3.5 (2026-10-06) the corollary of `closedLoop_unique_attracting_of_sharp_lt_one`:
the factor-four constant bounds the sharp one (`LloopSharp_le_Lloop`), so its
hypothesis `L_loop < 1` is the stronger of the two and is used only through
`LloopSharp < 1`. -/
theorem closedLoop_unique_attracting_of_lt_one (hL : E.Lloop < 1) :
    ∃ z ∈ Sanctions.I, E.closedLoop z = z ∧
      (∀ y ∈ Sanctions.I, E.closedLoop y = y → y = z) ∧
      ∀ x ∈ Sanctions.I, Tendsto (fun n => E.closedLoop^[n] x) atTop (𝓝 z) :=
  E.closedLoop_unique_attracting_of_sharp_lt_one (lt_of_le_of_lt E.LloopSharp_le_Lloop hL)

/-- **Activation without hysteresis on the class: one globally attracting steady
state at the forward-looking equilibrium** (renovation item BH3.5, 2026-10-06). On
every relief chord economy with the stage appetite `u_hi < q`, the loss offset, the
rally margin and a closed loop that contracts at the sharp constant
`L_loop^sharp = g_hi + d_hi·L_resp/μ < 1`, the forward-looking equilibrium has one
steady state in `[0,1]`: sanction equals state there, it lies in `(b, A/q]`
(`sfloor < z ≤ cap`), and every feasible start's forward-looking path converges to
it. Both channels can be active there (`both_channels_active_of_margin` under the
stage flip, `ChordEconomyCs.both_channels_active_of_relief` under (RL)) and still a
finite shock leaves no lasting trace: no same-equilibrium hysteresis. General in `F`.

Neither the stage relief margin `hSR` nor placability `hP` is read; they belong to
the myopic side of the separation, not to the forward-looking limit. The members
`placableAffine_unique_attracting_state` (sharp constant `14/23`) and
`placableQuadDiag_unique_attracting_state` (`35/47`) are instances. The plan item
named interiority `A = u_hi + β_S·K_S·d_hi < q`; only its consequence `u_hi < q` is
read (through `dynamicPath_tendsto`, as re-signed in BH3.1), so the binder is the
stage appetite and interiority supplies it through `uhi_lt_q`. -/
theorem unique_attracting_state_of_sharp_lt_one (hS : E.uhi < E.q) (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hL : E.LloopSharp < 1) :
    ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
      (∀ y ∈ Sanctions.I, E.closedLoop y = y → y = z) ∧
      ∀ x₀ ∈ Sanctions.I, Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z) := by
  obtain ⟨z, hz, _, huniq, hall⟩ := E.closedLoop_unique_attracting_of_sharp_lt_one hL
  have hpath : ∀ x₀ ∈ Sanctions.I, Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z) := by
    intro x₀ hx₀
    have heq : (E.dynamicPath hTM) hmargin x₀ = fun n => E.closedLoop^[n] x₀ :=
      funext ((E.dynamicPath_eq_closedLoop_iterate hTM) hmargin hx₀)
    rw [heq]
    exact hall x₀ hx₀
  obtain ⟨z', _, hfix', hlo', hhi', htend'⟩ :=
    (E.dynamicPath_tendsto hS hTM) hmargin ⟨le_rfl, zero_le_one⟩
  have hzz : z' = z := tendsto_nhds_unique htend' (hpath 0 ⟨le_rfl, zero_le_one⟩)
  subst hzz
  exact ⟨z', hz, hfix', hlo', hhi', huniq, hpath⟩

end ChordEconomyRelief

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.ChordEconomy.dynamicArgmax_le_cap
#print axioms Sanctions.Examples.ChordEconomyRelief.myopicEquilibriumTop
#print axioms Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF
#print axioms Sanctions.Examples.ChordEconomyRelief.myopicEquilibriumTopS
#print axioms
  Sanctions.Examples.ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF_stage
#print axioms ChordEconomy.dynamicPath_tendsto_of_response_monotone
#print axioms
  ChordEconomyRelief.myopic_dynamic_equilibrium_separation_generalF_stage_of_response_monotone
#print axioms Sanctions.Examples.ChordEconomyRelief.closedLoop_unique_attracting_of_lt_one
#print axioms Sanctions.Examples.ChordEconomyRelief.closedLoop_unique_attracting_of_sharp_lt_one
#print axioms Sanctions.Examples.ChordEconomyRelief.unique_attracting_state_of_sharp_lt_one

end Examples
end Sanctions
