/-
Sanctions/Examples/HostileSenderClass.lean

**A hostile Sender on the chord class: the reverse wedge, the residual floor, the cheaper
relief price, and every full-defiance case-11 equilibrium** (step 2, target 2b, 2026-10-10;
referee M2(a)). RARE CASE: a Sender whose coalition loses when hard-liners in the Target gain.

The hostile reading of a chord economy `E` is the stake-shifted economy
`E.hostileParams κ = E.toParams.senderStateShift (−κ)`: the Sender's stage payoff is
`U_S(x,a,s) − κ·x`, and the static selector `σ`, the transition `F` and the Target's side are
`E`'s (`SenderStakeShift.lean`). It need not be a chord economy. On it, with the curvature
ceiling `Q̄`, the chords `g_lo, g_hi, d_lo, d_hi`, the floor `u_lo`, the cross rate `r_lo` and
the placation ceiling `k_hi` read off `E`:

* `hostile_defianceValue_falls` — under the **hostile stake bound** (approved hypothesis 3: the
  Sender's payoff at defiance falls in the state at rate at least `w̄` at every sanction level),
  the Sender's value against full defiance falls at rate at least `ḡ_S = w̄/(1 − β_S·g_lo)`
  (`chGS β_S g_lo w̄`).
* `hostile_wedge` — the **reverse wedge**: the forward-looking response to defiance is at most
  `max 0 (σᴹ(x,0) − β_S·ḡ_S·d_lo/Q̄)`.
* `hostile_residual_floor`, `hostile_sanction_pos` — the **residual floor**: under the stake bound
  the response is at least `min 1 ((u_lo − β_S·K_S·d_hi)/Q̄)` with `K_S = (κ − w_lo)/(1 − β_S·g_hi)`
  the hostile payoff's fall-rate ceiling; and, under the **residual appetite** alone
  `u_lo > β_S·K_S·d_hi` (approved hypothesis 4, no stake bound), it is positive.
* `hostile_relief_price` — the **cheaper relief price**: at the relief value, the forward-looking
  Sender's zero level is at most `max 0 (a⁰⁰(x) − β_S·ḡ⁰_S·d_lo/k_hi) < a⁰⁰(x)`, `ḡ⁰_S` the
  compounded fall rate of the zero-sanction payoff; `hostile_relief_value_eq` identifies the
  relief value as the Sender's value in every relief equilibrium (case 01).
* `hostile_full_defiance_bounds` — **every full-defiance case-11 equilibrium**: its realised rule
  is at most `max 0 (σ(x,0) − β_S·ḡ_S·d_lo/Q̄)`; from a common start its state path lies below the
  stage-rule path (the case-10 path, `targetOnlyPath_eq_stageRulePath`) at every date; its sanctions
  lie below the stage-rule sanctions less the wedge; and every limit of its path is at most
  `max 0 (z₁₀ − β_S·ḡ_S·d_lo/(Q̄ − r_lo))`, `z₁₀` the case-10 limit.

Every bound is attained at the hostile benchmark of `HostileSenderWitness.lean`.

**Scope.** Rare case: hostile Sender (hypotheses 3–4). Existence of hostile equilibria on the
class is not shown here (Tier 2); the case-11 statements hold at every equilibrium of the case,
and existence is shown at the benchmark. The stake bound is uniform in the sanction: measured at
zero sanction only, the reverse wedge is false when the rally term is positive (plan D2).

Rule 3: approved hypotheses 3 and 4 only, as theorem binders over the hostile economy's
`U_S`. Rule 15: the values are constructed fixed points. Rule 22: general in `F`.
-/
import Sanctions.Examples.SenderStakeShift
import Sanctions.Examples.PlacableSenderWedge
import Sanctions.Theory.LockIn.SenderStakeSign

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Mechanism

noncomputable section

/-- Adding a constant keeps a semiconvexity modulus.
Scope: general class (real analysis; no economic hypothesis). -/
theorem semiconvexOnSet_add_const {ψ : ℝ → ℝ} {X : Set ℝ} {M c : ℝ}
    (h : Sanctions.Semiconcave.SemiconvexOnSet ψ X M) :
    Sanctions.Semiconcave.SemiconvexOnSet (fun u => ψ u + c) X M := by
  intro x₁ hx₁ x₂ hx₂ t ht0 ht1
  have := h x₁ hx₁ x₂ hx₂ t ht0 ht1
  linarith

namespace ChordEconomy

variable (E : ChordEconomy) (κ : ℝ)

/-! ## The hostile reading -/

/-- **The hostile reading of a chord economy**: Sender payoff `U_S(x,a,s) − κ·x`, everything else
unchanged. For `κ` large enough the Sender's payoff falls with the political state. -/
abbrev hostileParams : Params := E.toParams.senderStateShift (-κ)

/-- **The hostile Sender's value against full defiance**: the constructed Banach fixed point of
its Bellman operator at the policy `a ≡ 0`. -/
def hostileDefianceValue : Val := (E.hostileParams κ).V_S (fun _ => 0) continuous_const

/-- **The hostile relief price** `a*(x)`: the least compliance at which the forward-looking
hostile Sender's response at the relief value vanishes. -/
def hostileZeroLevel (x : ℝ) : ℝ :=
  Sanctions.ZeroLevel.level (fun x a => (E.hostileParams κ).σ_dyn_top
    (E.hostileParams κ).reliefValue x a) x

/-- The state path under the stage rule at defiance, `x_{t+1} = F(x_t, σ(x_t, 0))`. -/
def stageRulePath (x₀ : ℝ) (t : ℕ) : ℝ := E.toParams.rulePathF E.stageResp x₀ t

/-- **The case-10 path is the stage-rule path.**
Scope: general class (chord economy, loss-offset condition); no approved hypothesis. -/
theorem targetOnlyPath_eq_stageRulePath (hTM : E.LossOffset) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    (t : ℕ) : E.targetOnlyPath hTM x₀ t = E.stageRulePath x₀ t :=
  E.toParams.rulePathF_congr_on (fun _ hx => E.targetOnlyRule_mem hTM hx)
    (fun _ hx => E.targetOnlyRule_eq_stage hTM hx) hx₀ t

/-- **The stage-rule path converges to a fixed point of the stage rule**, from every start.
Scope: general class (chord economy); no approved hypothesis. -/
theorem stageRulePath_tendsto {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z₁₀ ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧ Tendsto (E.stageRulePath x₀) atTop (𝓝 z₁₀) := by
  obtain ⟨z, hz, hfix, htend⟩ := E.toParams.rulePathF_tendsto_fixedPoint_of_monotoneOn
    (fun x _ => E.stageResp_mem x) E.stageResp_monotoneOn
    E.stageResp_continuous.continuousOn hx₀
  exact ⟨z, hz, E.toParams.rule_eq_self_of_closedLoop_fixed E.hdlo0 E.hSlo hz
    (E.stageResp_mem z) hfix, htend⟩

/-! ## The Sender's value falls, at a bounded rate -/

/-- **The hostile Sender's value against full defiance falls at rate at least
`ḡ_S = w̄/(1 − β_S·g_lo)`**, when its payoff at defiance falls in the state at rate at least
`w̄ ≥ 0` at every sanction level.
The stake bound is uniform in the sanction.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 3. -/
theorem hostile_defianceValue_falls {w : ℝ} (hw : 0 ≤ w)
    (hH1 : ∀ s ∈ Sanctions.I, ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, x₁ ≤ x₂ →
      (E.hostileParams κ).U_S x₂ 0 s - (E.hostileParams κ).U_S x₁ 0 s ≤ -(w * (x₂ - x₁))) :
    Params.LowerSlopeOnValueOn (-E.hostileDefianceValue κ) (Icc (0 : ℝ) 1) (chGS E.β_S E.glo w) :=
  (E.hostileParams κ).V_S_negLowerSlope_of_stateChords continuous_const hw E.βS_glo_lt_one
    hH1 (fun s hs y₁ hy₁ y₂ hy₂ hle => (E.hbandAll s hs y₁ hy₁ y₂ hy₂ hle).1)

/-- **A hostile stake bound forces `κ ≥ w_lo + w̄`**: the shift must overcome the original
stake. Read at zero sanction between the endpoints, with S3.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 3. -/
theorem wlo_add_le_of_hostile {w : ℝ}
    (hH1 : ∀ s ∈ Sanctions.I, ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, x₁ ≤ x₂ →
      (E.hostileParams κ).U_S x₂ 0 s - (E.hostileParams κ).U_S x₁ 0 s ≤ -(w * (x₂ - x₁))) :
    E.wlo + w ≤ κ := by
  have h1 := hH1 0 zero_mem_I 0 zero_mem_I 1 one_mem_I zero_le_one
  have h2 := E.hUS_stateSlope 0 zero_mem_I 0 zero_mem_I 0 zero_mem_I 1 one_mem_I zero_le_one
  simp only [Params.senderStateShift_U_S] at h1
  linarith

/-- **The hostile Sender's value against full defiance falls at most at rate
`K_S = (κ − w_lo)/(1 − β_S·g_hi)`** (`chKS β_S g_hi (κ − w_lo)`): the hostile payoff falls at
most at rate `κ − w_lo` (S3), compounded through the upper state chord.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 3. -/
theorem hostile_defianceValue_fall_le {w : ℝ} (hw : 0 ≤ w)
    (hH1 : ∀ s ∈ Sanctions.I, ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, x₁ ≤ x₂ →
      (E.hostileParams κ).U_S x₂ 0 s - (E.hostileParams κ).U_S x₁ 0 s ≤ -(w * (x₂ - x₁))) :
    Params.LowerSlopeOnValueOn (E.hostileDefianceValue κ) (Icc (0 : ℝ) 1)
      (-chKS E.β_S E.ghi (κ - E.wlo)) := by
  have hκ := E.wlo_add_le_of_hostile κ hH1
  refine (E.hostileParams κ).V_S_lowerSlope_of_stateLowerChords continuous_const
    (by linarith) E.βS_ghi_lt_one ?_ (fun s hs y₁ hy₁ y₂ hy₂ hle =>
      (E.hbandAll s hs y₁ hy₁ y₂ hy₂ hle).2)
  intro s hs y₁ hy₁ y₂ hy₂ hle
  have h := E.hUS_stateSlope 0 zero_mem_I s hs y₁ hy₁ y₂ hy₂ hle
  simp only [Params.senderStateShift_U_S]
  nlinarith [h]

/-! ## The reverse wedge and the residual floor -/

/-- **The reverse wedge** (N7 on the class). Under the hostile stake bound at rate `w̄ > 0` and
the stage appetite `u_hi < q`, at every feasible state the hostile Sender's forward-looking
response to defiance satisfies `R(x) ≤ max 0 (σᴹ(x,0) − β_S·ḡ_S·d_lo/Q̄)`, with
`ḡ_S = w̄/(1 − β_S·g_lo)`. The mirror of `responsePath_ge_stage_add_wedge`.
The stake bound is uniform in the sanction.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 3. -/
theorem hostile_wedge {w : ℝ} (hw : 0 < w)
    (hH1 : ∀ s ∈ Sanctions.I, ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, x₁ ≤ x₂ →
      (E.hostileParams κ).U_S x₂ 0 s - (E.hostileParams κ).U_S x₁ 0 s ≤ -(w * (x₂ - x₁)))
    (hS : E.uhi < E.q) {x : ℝ} (hx : x ∈ Sanctions.I) :
    (E.hostileParams κ).σ_dyn_top (E.hostileDefianceValue κ) x 0
      ≤ max 0 (E.σ x 0 - E.β_S * chGS E.β_S E.glo w * E.dlo / E.Qbar) := by
  have hpos : 0 < 1 - E.β_S * E.glo := E.one_sub_βS_glo_pos
  have hg : 0 < chGS E.β_S E.glo w := div_pos hw hpos
  exact (E.hostileParams κ).σ_dyn_top_le_stage_sub_wedge hx
    (E.hostile_defianceValue_falls κ hw.le hH1) hg.le
    (fun s₁ hs₁ s₂ hs₂ hle => E.hSlo hx hs₁ hs₂ hle) E.Qbar_pos
    (semiconvexOnSet_add_const (E.hUS_convex x hx 0 zero_mem_I))
    (E.stage_argmax_lt_one hS hx) (mul_pos (mul_pos E.hβS0 hg) E.hdlo0)

/-- **The residual floor** (N11 on the class). Under the hostile stake bound, at every feasible
state the hostile Sender's forward-looking response to defiance is at least
`min 1 ((u_lo − β_S·K_S·d_hi)/Q̄)`, `K_S = (κ − w_lo)/(1 − β_S·g_hi)`.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 3. -/
theorem hostile_residual_floor {w : ℝ} (hw : 0 ≤ w)
    (hH1 : ∀ s ∈ Sanctions.I, ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, x₁ ≤ x₂ →
      (E.hostileParams κ).U_S x₂ 0 s - (E.hostileParams κ).U_S x₁ 0 s ≤ -(w * (x₂ - x₁)))
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    min 1 ((E.ulo - E.β_S * chKS E.β_S E.ghi (κ - E.wlo) * E.dhi) / E.Qbar)
      ≤ (E.hostileParams κ).σ_dyn_top (E.hostileDefianceValue κ) x 0 := by
  have hκ := E.wlo_add_le_of_hostile κ hH1
  have hK : 0 ≤ chKS E.β_S E.ghi (κ - E.wlo) :=
    div_nonneg (by linarith) E.one_sub_βS_ghi_pos.le
  refine (E.hostileParams κ).σ_dyn_top_ge_residual hx
    (E.hostile_defianceValue_fall_le κ hw hH1) hK
    (fun s₁ hs₁ s₂ hs₂ hle => E.hShi hx hs₁ hs₂ hle) E.Qbar_pos ?_
  intro t ht s hs hle
  have h := E.hUS_floor x hx t ht s hs hle
  simp only [Params.senderStateShift_U_S]
  linarith

/-- The hostile Sender's value against full defiance falls at most at rate
`chKS β_S g_hi (max 0 (κ − w_lo))`, for every stake shift `κ` (no hostile stake bound is read).
Scope: rare case: hostile Sender (hypotheses 3–4); no approved hypothesis is used. -/
theorem hostile_defianceValue_fall_le_max :
    Params.LowerSlopeOnValueOn (E.hostileDefianceValue κ) (Icc (0 : ℝ) 1)
      (-chKS E.β_S E.ghi (max 0 (κ - E.wlo))) := by
  refine (E.hostileParams κ).V_S_lowerSlope_of_stateLowerChords continuous_const
    (le_max_left _ _) E.βS_ghi_lt_one ?_ (fun s hs y₁ hy₁ y₂ hy₂ hle =>
      (E.hbandAll s hs y₁ hy₁ y₂ hy₂ hle).2)
  intro s hs y₁ hy₁ y₂ hy₂ hle
  have h := E.hUS_stateSlope 0 zero_mem_I s hs y₁ hy₁ y₂ hy₂ hle
  have hm : κ - E.wlo ≤ max 0 (κ - E.wlo) := le_max_right _ _
  have hd : 0 ≤ y₂ - y₁ := by linarith
  have hmd := mul_le_mul_of_nonneg_right hm hd
  simp only [Params.senderStateShift_U_S]
  nlinarith [hmd]

/-- **Under the residual appetite alone the hostile Sender still sanctions a defiant Target**
(N11 on the class): if `β_S·K_S·d_hi < u_lo`, the forward-looking response to defiance is
positive at every feasible state, for every stake shift `κ`. No hostile stake bound is read: for
`κ < w_lo` the hostile value is nondecreasing and the residual floor is `u_lo/Q̄ > 0`.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 4 only. -/
theorem hostile_sanction_pos
    (hH3 : E.β_S * chKS E.β_S E.ghi (κ - E.wlo) * E.dhi < E.ulo)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    0 < (E.hostileParams κ).σ_dyn_top (E.hostileDefianceValue κ) x 0 := by
  have hpos : 0 < 1 - E.β_S * E.ghi := E.one_sub_βS_ghi_pos
  have hK : 0 ≤ chKS E.β_S E.ghi (max 0 (κ - E.wlo)) := div_nonneg (le_max_left _ _) hpos.le
  have hres : E.β_S * chKS E.β_S E.ghi (max 0 (κ - E.wlo)) * E.dhi < E.ulo := by
    rcases le_total (κ - E.wlo) 0 with h | h
    · rw [max_eq_left h]
      simp only [chKS, zero_div, mul_zero, zero_mul]
      exact E.hulo
    · rw [max_eq_right h]; exact hH3
  have hfl : min 1 ((E.ulo - E.β_S * chKS E.β_S E.ghi (max 0 (κ - E.wlo)) * E.dhi) / E.Qbar)
      ≤ (E.hostileParams κ).σ_dyn_top (E.hostileDefianceValue κ) x 0 := by
    refine (E.hostileParams κ).σ_dyn_top_ge_residual hx (E.hostile_defianceValue_fall_le_max κ) hK
      (fun s₁ hs₁ s₂ hs₂ hle => E.hShi hx hs₁ hs₂ hle) E.Qbar_pos ?_
    intro t ht s hs hle
    have h := E.hUS_floor x hx t ht s hs hle
    simp only [Params.senderStateShift_U_S]
    linarith
  exact lt_of_lt_of_le (lt_min one_pos (div_pos (by linarith) E.Qbar_pos)) hfl

/-! ## The cheaper relief price -/

/-- **The hostile relief price is cheaper** (N9 on the class). Let the Sender's zero-sanction
payoff at defiance fall in the state at rate at least `w̄₀ > 0`, let `k_hi` be a placation
ceiling and let the stage placability `u_hi < k_lo` hold. Then at every feasible state the
hostile Sender's zero level at the relief value satisfies
`a*(x) ≤ max 0 (a⁰⁰(x) − β_S·ḡ⁰_S·d_lo/k_hi) < a⁰⁰(x)`, with `ḡ⁰_S = w̄₀/(1 − β_S·g_lo)` and
`a⁰⁰` the myopic zero level.
The stake bound is read at zero sanction only, as the plan allows for the relief price.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 3 at `s = 0`. -/
theorem hostile_relief_price {w₀ khi : ℝ} (hw₀ : 0 < w₀)
    (hH1₀ : ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, x₁ ≤ x₂ →
      (E.hostileParams κ).U_S x₂ 0 0 - (E.hostileParams κ).U_S x₁ 0 0 ≤ -(w₀ * (x₂ - x₁)))
    (hPC : E.PlacationCeiling khi) (hPs : E.uhi < E.klo) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.hostileZeroLevel κ x ≤ max 0 (E.zeroLevel00 x - E.β_S * chGS E.β_S E.glo w₀ * E.dlo / khi)
      ∧ max 0 (E.zeroLevel00 x - E.β_S * chGS E.β_S E.glo w₀ * E.dlo / khi)
        < E.zeroLevel00 x := by
  have hpos : 0 < 1 - E.β_S * E.glo := E.one_sub_βS_glo_pos
  have hg : 0 < chGS E.β_S E.glo w₀ := div_pos hw₀ hpos
  have hzI := E.zeroLevel00_mem hPs hx
  have hσz := E.σ_zeroLevel00 hPs hx
  set z := E.zeroLevel00 x with hz_def
  have hzmax : IsMaxOn (fun s => (E.hostileParams κ).U_S x z s) Sanctions.I 0 := by
    intro s hs
    have h := E.σ_isMaxOn_U_S x z hs
    rw [hσz] at h
    simp only [Set.mem_setOf_eq, Params.senderStateShift_U_S] at h ⊢
    linarith
  have hPC' : ∀ a ∈ Sanctions.I, a ≤ z → ∀ s ∈ Sanctions.I,
      ((E.hostileParams κ).U_S x a s - (E.hostileParams κ).U_S x a 0)
        - ((E.hostileParams κ).U_S x z s - (E.hostileParams κ).U_S x z 0)
        ≤ khi * (z - a) * s := by
    intro a ha haz s hs
    have h := hPC x hx a ha z hzI 0 zero_mem_I s hs haz
    rw [sub_zero, abs_of_nonneg hs.1] at h
    have h' := (abs_le.mp h).1
    simp only [Params.senderStateShift_U_S]
    nlinarith [h']
  have hV := (E.hostileParams κ).reliefValue_negLowerSlope hw₀.le E.βS_glo_lt_one hH1₀
    (fun y₁ hy₁ y₂ hy₂ hle => (E.hbandAll 0 zero_mem_I y₁ hy₁ y₂ hy₂ hle).1)
  exact (E.hostileParams κ).zeroLevel_lt_of_placation_gap hx hzI hzmax hPC' hV hg.le
    (fun s₁ hs₁ s₂ hs₂ hle => E.hSlo hx hs₁ hs₂ hle) (E.khi_pos hPC)
    (mul_pos (mul_pos E.hβS0 hg) E.hdlo0) (E.zeroLevel00_pos hPs hx)

/-- **The relief value is the hostile Sender's value in every relief equilibrium** (case 01).
In every top-selector equilibrium of the hostile reading at the profile `01` (myopic Target,
forward-looking Sender) whose realised sanction is zero at every state, under zero-sanction
neutrality, the Sender's value is the relief value; so the Sender's response is the one whose
zero level is `hostileZeroLevel`.
It holds at every stake.
Scope: rare case: hostile Sender (hypotheses 3–4); no approved hypothesis is used. -/
theorem hostile_relief_value_eq (hN : E.ZeroSanctionNeutral)
    (EH : ((E.hostileParams κ).withProfile
      ContinuationProfile.p01).FeedbackStackelbergEquilibriumTop)
    (hzero : ∀ x ∈ Sanctions.S,
      ((E.hostileParams κ).withProfile ContinuationProfile.p01).dynamicEquilibriumRule EH x = 0) :
    EH.V_S = (E.hostileParams κ).reliefValue := by
  have h := ((E.hostileParams κ).withProfile ContinuationProfile.p01).equilibrium_V_S_eq_reliefValue
    EH hzero (fun x hx => by
      have h := hN x hx (EH.α x) (EH.α_mem x hx)
      simp only [Params.withProfile_U_S, Params.senderStateShift_U_S]
      linarith)
  exact h

/-! ## Every full-defiance case-11 equilibrium -/

/-- **Every full-defiance case-11 equilibrium of the hostile reading** (N10 on the class). Let
`EH` be a top-selector equilibrium of `E.hostileParams κ` in which the Target fully defies at
every state, under the hostile stake bound at rate `w̄ > 0` and the stage appetite `u_hi < q`.
With `ḡ_S = w̄/(1 − β_S·g_lo)`:
(a) at every feasible state the realised sanction is at most `max 0 (σ(x,0) − β_S·ḡ_S·d_lo/Q̄)`;
(b) from every feasible start, the state path lies below the stage-rule path at every date;
(c) the realised sanctions lie below the stage-rule sanctions less the wedge at every date;
(d) if the path converges to `z`, the stage-rule path converges to a fixed point
`z₁₀ = σ(z₁₀, 0)` and `z ≤ max 0 (z₁₀ − β_S·ḡ_S·d_lo/(Q̄ − r_lo))`.
Under the loss-offset condition the stage-rule path is the case-10 path
(`targetOnlyPath_eq_stageRulePath`). No monotone forward-looking response is used.
Conditional on an equilibrium of the case (existence at the benchmark only).
The stake bound is uniform in the sanction.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 3. -/
theorem hostile_full_defiance_bounds {w : ℝ} (hw : 0 < w)
    (hH1 : ∀ s ∈ Sanctions.I, ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, x₁ ≤ x₂ →
      (E.hostileParams κ).U_S x₂ 0 s - (E.hostileParams κ).U_S x₁ 0 s ≤ -(w * (x₂ - x₁)))
    (hS : E.uhi < E.q)
    (EH : (E.hostileParams κ).FeedbackStackelbergEquilibriumTop)
    (hdef : ∀ x ∈ Sanctions.S, EH.α x = 0) :
    (∀ x ∈ Sanctions.I, (E.hostileParams κ).dynamicEquilibriumRule EH x
        ≤ max 0 (E.σ x 0 - E.β_S * chGS E.β_S E.glo w * E.dlo / E.Qbar)) ∧
    (∀ x₀ ∈ Sanctions.I, ∀ t,
      (E.hostileParams κ).rulePathF ((E.hostileParams κ).dynamicEquilibriumRule EH) x₀ t
        ≤ E.stageRulePath x₀ t) ∧
    (∀ x₀ ∈ Sanctions.I, ∀ t,
      (E.hostileParams κ).dynamicEquilibriumRule EH
          ((E.hostileParams κ).rulePathF ((E.hostileParams κ).dynamicEquilibriumRule EH) x₀ t)
        ≤ max 0 (E.σ (E.stageRulePath x₀ t) 0 - E.β_S * chGS E.β_S E.glo w * E.dlo / E.Qbar)) ∧
    (∀ x₀ ∈ Sanctions.I, ∀ z, Tendsto ((E.hostileParams κ).rulePathF
        ((E.hostileParams κ).dynamicEquilibriumRule EH) x₀) atTop (𝓝 z) →
      ∃ z₁₀ ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧ Tendsto (E.stageRulePath x₀) atTop (𝓝 z₁₀) ∧
        z ≤ max 0 (z₁₀ - E.β_S * chGS E.β_S E.glo w * E.dlo / (E.Qbar - E.rlo))) := by
  have hpos : 0 < 1 - E.β_S * E.glo := E.one_sub_βS_glo_pos
  have hg : 0 < chGS E.β_S E.glo w := div_pos hw hpos
  have hL : 0 < (E.hostileParams κ).β_S * (w / (1 - (E.hostileParams κ).β_S * E.glo)) * E.dlo :=
    mul_pos (mul_pos E.hβS0 hg) E.hdlo0
  have hconv : ∀ x ∈ Sanctions.I, Sanctions.Semiconcave.SemiconvexOnSet
      (fun s => (E.hostileParams κ).U_S x 0 s) (Icc (0 : ℝ) 1) E.Qbar :=
    fun x hx => semiconvexOnSet_add_const (E.hUS_convex x hx 0 zero_mem_I)
  have hF : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      E.glo * (y₂ - y₁) ≤ (E.hostileParams κ).F y₂ s - (E.hostileParams κ).F y₁ s :=
    fun s hs y₁ hy₁ y₂ hy₂ hle => (E.hbandAll s hs y₁ hy₁ y₂ hy₂ hle).1
  have hσ1 : ∀ x ∈ Sanctions.I, (E.hostileParams κ).σ x 0 < 1 :=
    fun x hx => E.stage_argmax_lt_one hS hx
  have hmono : MonotoneOn (fun x => (E.hostileParams κ).σ x 0) Sanctions.I :=
    E.stageResp_monotoneOn
  refine ⟨fun x hx => ?_, fun x₀ hx₀ t => ?_, fun x₀ hx₀ t => ?_, fun x₀ hx₀ z htend => ?_⟩
  · exact (E.hostileParams κ).hostileRule_le_stage_sub_wedge EH hdef hw.le E.βS_glo_lt_one hH1
      hF E.hSlo E.Qbar_pos hconv hσ1 hL hx
  · exact (E.hostileParams κ).hostilePath_le_stagePath EH hdef hw.le E.βS_glo_lt_one hH1 hF
      E.hSlo E.Qbar_pos hconv hσ1 hL hmono hx₀ t
  · exact (E.hostileParams κ).hostileSanction_le_stage_sub_wedge EH hdef hw.le E.βS_glo_lt_one
      hH1 hF E.hSlo E.Qbar_pos hconv hσ1 hL hmono hx₀ t
  · obtain ⟨z₁₀, hz₁₀, hfix, htend₁₀⟩ := E.stageRulePath_tendsto hx₀
    refine ⟨z₁₀, hz₁₀, hfix, htend₁₀, ?_⟩
    exact (E.hostileParams κ).hostileLimit_le_stageLimit_sub_gap EH hdef hw.le E.βS_glo_lt_one
      hH1 hF E.hSlo E.hdlo0 E.Qbar_pos (E.rlo_lt_Qbar hS) hconv hσ1 hL hmono
      (fun x hx x' hx' hxx' => E.stage_argmax_sub_ge hS hx hx' hxx') hx₀ htend htend₁₀ hfix

end ChordEconomy

end

end Examples
end Sanctions
