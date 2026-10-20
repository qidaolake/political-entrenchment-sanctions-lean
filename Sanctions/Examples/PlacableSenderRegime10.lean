/-
Sanctions/Examples/PlacableSenderRegime10.lean

**The Target-only reading of a chord economy: the Target looks ahead, the
Sender does not** (`ContinuationProfile.p10`), and where it sits between the
myopic and the forward-looking readings.

Rung 5 (`PlacableSenderRegimes`) constructed the readings `00` and `11`. This
file constructs `10` on every chord economy and orders its limit against `11`:

* **The Sender's rule is the stage selector** `σ(x, 0)`: at `β_S = 0` both
  dynamic selectors are the primitive stage selector (`ZeroDiscountSelector`),
  and its value is the stage value `U_S(x, 0, σ(x, 0))`.
* **The Target still defies.** Against the stage response — antitone in
  compliance, monotone in the state — the forward-looking Target's objective is
  strictly decreasing in compliance on the lower-slope carrier, by the same
  loss-offset argument as in the `11` reading (`targetObj10_strictAntiOn`). Its
  value is a Banach fixed point on that carrier. So the Target channel **alone**
  flips the Target from partial compliance (`00`) to defiance (`10`).
* **The state washes in** to a fixed point of the stage selector,
  `σ(z, 0) = z`, from every start (`targetOnlyPath_tendsto`), and that limit is
  **strictly below** the forward-looking limit from the same start
  (`targetOnly_limit_lt_dynamic_limit`): the forward-looking sanction sits
  strictly above the stage selector at every state, so the forward-looking path
  dominates, and the two limits cannot coincide.

**What the rate bounds do not give.** The fixed point of the stage selector need
not be unique: two fixed points need the cross rate to exceed the curvature
somewhere, and the conditions bound the cross rate only from above by `r_hi`,
which may exceed `q`. Uniqueness and a geometric rate hold when `r_hi < q`; on
the quadratic–linear family `r < q`, the fixed point is the closed form
`u₀/(q − r)`, and §6 states both (sign-off M6: exact-form results stay on the
family).

**The reading `01`** (Target myopic, Sender forward-looking) is constructed in
`PlacableSenderRegime01` on the subclass `ChordEconomyCs`: the Target's optimum
is the zero level, the least compliance at which the dynamic response vanishes,
and the four-cell theorem there orders all four readings. Nothing in this file
uses the subclass.

Rule 1: the Target policy is the unique argmax; the Sender rule is the stage
argmax. Rule 3: no new assumption. Rule 22: general in `F`.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation item BJ3.1 (2026-10-07): the two rally-margin forms,
`targetOnly_limit_lt_dynamic_limit` and `target_only_regime_generalF`, read the two-sided
curvature data and are stated on `ChordEconomyTwoSided`.

Renovation items BH3.1 and BH3.2 (2026-10-06): `targetOnly_limit_lt_dynamic_limit`
and `target_only_regime_generalF` read interiority only through the stage appetite
`u_hi < q`, which they now take as the binder `hS`; the family's closed-form myopic
policy needs only `u₀ + r < k` (`toChord_myopicPolicy_of_lt`).

Renovation item BH4.1 (2026-10-06): the comparison of the `10` and `11` limits reads the
rally margin only to make the forward-looking response nondecreasing. Its
`_of_response_monotone` forms take that nondecreasing response `hmono` in place of the
margin, at `equilibriumTop hTM hmono` and its path `dynamicPathOf hTM hmono`; the margin
forms keep their statements and are corollaries at
`hmono := responsePath_monotoneOn_of_margin hmargin`.

Renovation item BJ2.3 (2026-10-07): the family `PlacableEconomyF` no longer carries the
interiority field. The closed-form results of §6 read it (through `r < q`, the vertex
and the floor `u₀ ≤ q`), so each takes the family's interiority as the hypothesis
`hInt : E.Interior`; `steady10_lt_of_r_lt` takes it for the member with the larger rally
slope. Nothing else changes; general in the family's transition `F`.
-/
import Sanctions.Foundations.CenteredContraction
import Sanctions.Examples.PlacableSenderRegimes
import Sanctions.Examples.PlacableSenderFamilyF

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.TransitionChords
  Sanctions.GeometricApproach Sanctions.Mechanism

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 1. The profile view and the stage response -/

/-- The Target-only reading: the Target's discount is `β_T`, the Sender's is `0`. -/
abbrev pT : AbstractGame.Params := E.toParams.withProfile ContinuationProfile.p10

theorem pT_β_S : E.pT.β_S = 0 := rfl
theorem pT_β_T : E.pT.β_T = E.toParams.β_T := rfl

theorem pT_σ_dyn_top (V : Val) {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    E.pT.σ_dyn_top V x a = E.toParams.σ x a :=
  E.pT.σ_dyn_top_eq_σ_of_βS_zero_of_strictConcaveOn rfl V x a (E.stage_strictConcaveOn hx a)

/-- The stage response at defiance, as a function of the state. -/
def stageResp (y : ℝ) : ℝ := E.toParams.σ y 0

theorem stageResp_mem (y : ℝ) : E.stageResp y ∈ Sanctions.I := E.toParams.σ_mem y 0

theorem stageResp_continuous : Continuous E.stageResp :=
  E.toParams.σ_continuous.comp (continuous_id.prodMk continuous_const)

/-- The stage response is nondecreasing in the state (increasing differences, S8). -/
theorem stageResp_monotoneOn : MonotoneOn E.stageResp Sanctions.I :=
  fun _ hx _ hy hxy => E.stage_argmax_mono hx hy hxy

/-- The stage response is never below the sanction floor `b = σ(0, 0)`. -/
theorem stageResp_ge_sfloor {y : ℝ} (hy : y ∈ Sanctions.I) : E.sfloor ≤ E.stageResp y :=
  E.sfloor_le hy

/-! ## 2. The Target side against the stage response -/

/-- The Target's forward-looking objective against the stage response. -/
def targetObj10 (V_T : Val) (x a : ℝ) : ℝ :=
  E.toParams.U_T x a (E.toParams.σ x a)
    + E.toParams.β_T * V_T (Sanctions.clipS' (E.toParams.F x (E.toParams.σ x a)))

/-- **Defiance is the strict unique Target argmax against the stage response**,
on the lower-slope carrier: more compliance buys less sanction, but the
discounted continuation gain of the higher state that sanction would have
produced exceeds the sanction's pain (`hTM`, the loss-offset margin), and
compliance costs at least `ℓ_lo` per unit. -/
theorem targetObj10_strictAntiOn (hTM : E.LossOffset) {V_T : Val} (hV_T : V_T ∈ E.carrierT)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    StrictAntiOn (fun a => E.targetObj10 V_T x a) Sanctions.I := by
  intro a₁ ha₁ a₂ ha₂ hlt
  change E.targetObj10 V_T x a₂ < E.targetObj10 V_T x a₁
  unfold targetObj10
  have hρ : E.σ x a₂ ≤ E.σ x a₁ := E.stage_σ_antitoneOn hx ha₁ ha₂ hlt.le
  have hρ₁ := E.σ_mem x a₁
  have hρ₂ := E.σ_mem x a₂
  have hz : E.F x (E.σ x a₂) ≤ E.F x (E.σ x a₁) := E.F_mono_s x hρ
  have hchord : E.dlo * (E.σ x a₁ - E.σ x a₂) ≤ E.F x (E.σ x a₁) - E.F x (E.σ x a₂) :=
    E.hSlo hx hρ₂ hρ₁ hρ
  have hslope := E.clipT_lowerSlope hV_T _ (E.F_mem _ _ hx hρ₂) _ (E.F_mem _ _ hx hρ₁) hz
  have hTM : E.c ≤ E.β_T * E.dlo * E.gT := hTM
  have hgT := E.gT_pos
  have hA : E.β_T * (V_T (Sanctions.clipS' (E.F x (E.σ x a₂)))
        - V_T (Sanctions.clipS' (E.F x (E.σ x a₁))))
      ≤ -(E.β_T * E.dlo * E.gT) * (E.σ x a₁ - E.σ x a₂) := by
    have h1 := mul_le_mul_of_nonneg_left hchord (mul_nonneg E.hβT0.le hgT.le)
    have h2 := mul_le_mul_of_nonneg_left hslope E.hβT0.le
    nlinarith [h1, h2]
  have hB : (E.σ x a₁ - E.σ x a₂) * (E.c - E.β_T * E.dlo * E.gT) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hρ) (by linarith)
  -- The stage: the pain bound at the lower sanction, the cost bound at the lower compliance.
  have hU := E.UT_sub_le hx ha₁ ha₂ hρ₁ hρ₂ hlt.le hρ
  have hD : 0 < E.ℓlo * (a₂ - a₁) := mul_pos E.hℓlo (by linarith)
  nlinarith [hA, hB, hU, hD]

theorem zero_isMaxOn_joint10 (hTM : E.LossOffset) {V_T : Val} (hV_T : V_T ∈ E.carrierT)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => E.targetObj10 V_T x a) Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rcases eq_or_lt_of_le ha.1 with h0 | hpos
  · rw [← h0]
  · exact ((E.targetObj10_strictAntiOn hTM) hV_T hx ⟨le_refl 0, zero_le_one⟩ ha hpos).le

theorem targetArgmax10_eq_zero (hTM : E.LossOffset) {V_T : Val} (hV_T : V_T ∈ E.carrierT)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.targetObj10 V_T x b) Sanctions.I a) : a = 0 := by
  by_contra hne
  have hpos : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm hne)
  have h1 := (E.targetObj10_strictAntiOn hTM) hV_T hx ⟨le_refl 0, zero_le_one⟩ ha hpos
  have h2 := hmax (show (0:ℝ) ∈ Sanctions.I from ⟨le_refl 0, zero_le_one⟩)
  exact absurd h2 (not_le.mpr h1)

/-! ## 3. The Target operator against the stage response -/

/-- The Target Bellman operator at defiance against the stage response. -/
def targetOp10 (V_T : Val) : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) =>
        E.toParams.U_T y.val 0 (E.stageResp y.val)
          + E.toParams.β_T
              * V_T (Sanctions.clipS' (E.toParams.F y.val (E.stageResp y.val))),
     by
       have hρ : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.stageResp y.val) :=
         E.stageResp_continuous.comp continuous_subtype_val
       have hU : Continuous (fun y : ↥(Sanctions.S : Set ℝ) =>
           E.toParams.U_T y.val 0 (E.stageResp y.val)) :=
         E.toParams.U_T_continuous.comp
           (continuous_subtype_val.prodMk (continuous_const.prodMk hρ))
       have hF : Continuous (fun y : ↥(Sanctions.S : Set ℝ) =>
           E.toParams.F y.val (E.stageResp y.val)) :=
         E.toParams.F_continuous.comp (continuous_subtype_val.prodMk hρ)
       exact hU.add (continuous_const.mul
         (V_T.continuous.comp (Sanctions.clipS'_continuous.comp hF)))⟩

theorem targetOp10_apply (V_T : Val) (y : ↥(Sanctions.S : Set ℝ)) :
    E.targetOp10 V_T y
      = E.toParams.U_T y.val 0 (E.stageResp y.val)
        + E.toParams.β_T
            * V_T (Sanctions.clipS' (E.toParams.F y.val (E.stageResp y.val))) := rfl

theorem targetOp10_contracting : ContractingWith E.toParams.β_T_nnreal E.targetOp10 := by
  refine ⟨E.toParams.β_T_nnreal_lt_one, ?_⟩
  apply lipschitzWith_of_pointwise_dist_le
  intro V W y
  rw [targetOp10_apply, targetOp10_apply, Real.dist_eq]
  have hβ : (0:ℝ) ≤ E.toParams.β_T := E.toParams.β_T_mem.1
  have h1 : |(E.toParams.U_T y.val 0 (E.stageResp y.val)
        + E.toParams.β_T * V (Sanctions.clipS' (E.toParams.F y.val (E.stageResp y.val))))
      - (E.toParams.U_T y.val 0 (E.stageResp y.val)
        + E.toParams.β_T * W (Sanctions.clipS' (E.toParams.F y.val (E.stageResp y.val))))|
      = E.toParams.β_T * |V (Sanctions.clipS' (E.toParams.F y.val (E.stageResp y.val)))
          - W (Sanctions.clipS' (E.toParams.F y.val (E.stageResp y.val)))| := by
    rw [show ∀ a b c : ℝ, (a + E.toParams.β_T * b) - (a + E.toParams.β_T * c)
        = E.toParams.β_T * (b - c) from fun a b c => by ring, abs_mul, abs_of_nonneg hβ]
  rw [h1]
  have h2 := BoundedContinuousFunction.dist_coe_le_dist (f := V) (g := W)
    (Sanctions.clipS' (E.toParams.F y.val (E.stageResp y.val)))
  rw [Real.dist_eq] at h2
  have := mul_le_mul_of_nonneg_left h2 hβ
  convert this using 2

/-- **The Target carrier is invariant under the operator at the stage
response**: the same norm and slope legs as `targetOp_mem_of_monotone`, with
the stage response's monotonicity in the state in place of the margin and its
floor `stageResp_ge_sfloor` in place of `responsePath_ge_sfloor`. -/
theorem targetOp10_mem (hTM : E.LossOffset) {V_T : Val} (hV_T : V_T ∈ E.carrierT) :
    E.targetOp10 V_T ∈ E.carrierT := by
  have hβ : (0:ℝ) ≤ E.β_T := E.hβT0.le
  refine ⟨?_, ?_⟩
  · -- Norm leg.
    rw [BoundedContinuousFunction.norm_le E.MT_nonneg]
    intro y
    rw [targetOp10_apply, Real.norm_eq_abs]
    have hVb : |V_T (Sanctions.clipS' (E.toParams.F y.val (E.stageResp y.val)))| ≤ E.MT := by
      have h := BoundedContinuousFunction.norm_coe_le_norm V_T
        (Sanctions.clipS' (E.toParams.F y.val (E.stageResp y.val)))
      rw [Real.norm_eq_abs] at h
      exact h.trans hV_T.1
    have hρ := E.stageResp_mem y.val
    have hy := y.property
    have hU : |E.toParams.U_T y.val 0 (E.stageResp y.val)| ≤ E.MT₀ :=
      E.abs_U_T_le_MT₀ hy zero_mem_I hρ
    have hMT : E.MT₀ + E.β_T * E.MT ≤ E.MT := by
      unfold MT
      have h2 : 0 < 1 - E.β_T := by linarith [E.hβT1]
      have h2' : (1 - E.β_T) ≠ 0 := h2.ne'
      have hid : E.MT₀ + E.β_T * (2 * E.MT₀ / (1 - E.β_T))
          = E.MT₀ * (1 + E.β_T) / (1 - E.β_T) := by field_simp; ring
      rw [hid]
      apply div_le_div_of_nonneg_right _ h2.le
      nlinarith [E.MT₀_nonneg, E.hβT1]
    calc |E.toParams.U_T y.val 0 (E.stageResp y.val)
          + E.β_T * V_T (Sanctions.clipS' (E.toParams.F y.val (E.stageResp y.val)))|
        ≤ |E.toParams.U_T y.val 0 (E.stageResp y.val)|
          + |E.β_T * V_T (Sanctions.clipS' (E.toParams.F y.val (E.stageResp y.val)))| :=
          abs_add_le _ _
      _ ≤ E.MT₀ + E.β_T * E.MT := by
          rw [abs_mul, abs_of_nonneg hβ]
          exact add_le_add hU (mul_le_mul_of_nonneg_left hVb hβ)
      _ ≤ E.MT := hMT
  · -- Slope leg.
    intro y₁ y₂ hy₁ hy₂ hle
    rw [targetOp10_apply, targetOp10_apply]
    have hyle : y₁.val ≤ y₂.val := hle
    have hd : dist y₁ y₂ = y₂.val - y₁.val := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hd]
    have hρ : E.stageResp y₁.val ≤ E.stageResp y₂.val := E.stageResp_monotoneOn hy₁ hy₂ hyle
    have hρ₁ := E.stageResp_mem y₁.val
    have hρ₂ := E.stageResp_mem y₂.val
    have hz₁ : E.F y₁.val (E.stageResp y₁.val) ≤ E.F y₁.val (E.stageResp y₂.val) :=
      E.F_mono_s _ hρ
    have hz₂ : E.F y₁.val (E.stageResp y₂.val) ≤ E.F y₂.val (E.stageResp y₂.val) :=
      E.F_mono_x _ hyle
    have hband := (E.hbandAll _ hρ₂) y₁.val hy₁ y₂.val hy₂ hyle
    have hchord := E.hSlo hy₁ hρ₁ hρ₂ hρ
    have hslope := E.clipT_lowerSlope hV_T _ (E.F_mem _ _ hy₁ hρ₁) _ (E.F_mem _ _ hy₂ hρ₂)
      (hz₁.trans hz₂)
    have hTM : E.c ≤ E.β_T * E.dlo * E.gT := hTM
    have hgT : E.gT * (1 - E.β_T * E.glo) * (y₂.val - y₁.val)
        = (E.vlo + E.nlo * E.sfloor) * (y₂.val - y₁.val) := by rw [E.gT_mul]
    have hgT0 := E.gT_pos
    have hsucc : E.glo * (y₂.val - y₁.val)
          + E.dlo * (E.stageResp y₂.val - E.stageResp y₁.val)
        ≤ E.F y₂.val (E.stageResp y₂.val) - E.F y₁.val (E.stageResp y₁.val) := by
      linarith [hband.1, hchord]
    have hA : E.β_T * E.gT * (E.glo * (y₂.val - y₁.val)
          + E.dlo * (E.stageResp y₂.val - E.stageResp y₁.val))
        ≤ E.β_T * (V_T (Sanctions.clipS' (E.F y₂.val (E.stageResp y₂.val)))
          - V_T (Sanctions.clipS' (E.F y₁.val (E.stageResp y₁.val)))) := by
      have h1 := mul_le_mul_of_nonneg_left hsucc (mul_nonneg hβ hgT0.le)
      have h2 := mul_le_mul_of_nonneg_left hslope hβ
      nlinarith [h1, h2]
    have hC : 0 ≤ (E.stageResp y₂.val - E.stageResp y₁.val)
        * (E.β_T * E.dlo * E.gT - E.c) :=
      mul_nonneg (sub_nonneg.mpr hρ) (by linarith)
    -- The stage: the state rate `v_lo + n_lo·ρ₁` at the lower sanction, which the
    -- floor `ρ₁ ≥ b` puts at least at `v_lo + n_lo·b`; then the pain `c`.
    have hUst := E.UT_state_chord_ge hy₁ hy₂ zero_mem_I hρ₁ hρ₂ hyle hρ
    have hE : E.sfloor * (E.nlo * (y₂.val - y₁.val))
        ≤ E.stageResp y₁.val * (E.nlo * (y₂.val - y₁.val)) :=
      mul_le_mul_of_nonneg_right (E.stageResp_ge_sfloor hy₁)
        (mul_nonneg E.hnlo (by linarith))
    change E.gT * (y₂.val - y₁.val)
      ≤ (E.U_T y₂.val 0 (E.stageResp y₂.val)
          + E.β_T * V_T (Sanctions.clipS' (E.F y₂.val (E.stageResp y₂.val))))
        - (E.U_T y₁.val 0 (E.stageResp y₁.val)
          + E.β_T * V_T (Sanctions.clipS' (E.F y₁.val (E.stageResp y₁.val))))
    nlinarith [hA, hC, hUst, hE, hgT]

/-- The operator restricted to the carrier. -/
def targetOp10Sub (hTM : E.LossOffset) : E.carrierT → E.carrierT :=
  fun V => ⟨E.targetOp10 V.1, (E.targetOp10_mem hTM) V.2⟩

theorem targetOp10Sub_contracting (hTM : E.LossOffset) :
    ContractingWith E.toParams.β_T_nnreal (E.targetOp10Sub hTM) := by
  refine ⟨E.toParams.β_T_nnreal_lt_one, ?_⟩
  intro V W
  have h := E.targetOp10_contracting.2 V.1 W.1
  simpa [targetOp10Sub, Subtype.edist_eq] using h

/-- **The Target's value in the Target-only reading**, a Banach fixed point. -/
def VT10 (hTM : E.LossOffset) : Val :=
  (ContractingWith.fixedPoint (E.targetOp10Sub hTM) (E.targetOp10Sub_contracting hTM)).1

theorem VT10_mem (hTM : E.LossOffset) : (E.VT10 hTM) ∈ E.carrierT :=
  (ContractingWith.fixedPoint (E.targetOp10Sub hTM) (E.targetOp10Sub_contracting hTM)).2

theorem VT10_fix (hTM : E.LossOffset) : E.targetOp10 (E.VT10 hTM) = (E.VT10 hTM) := by
  have h := ContractingWith.fixedPoint_isFixedPt (E.targetOp10Sub_contracting hTM)
  exact congrArg Subtype.val h

/-! ## 4. The Sender's stage value and the equilibrium -/

/-- **The myopic Sender's value at defiance**: the stage payoff at the stage
selector. -/
def VS10 : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) => E.toParams.U_S y.val 0 (E.stageResp y.val), by
      have hρ : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.stageResp y.val) :=
        E.stageResp_continuous.comp continuous_subtype_val
      exact E.toParams.U_S_continuous.comp
        (continuous_subtype_val.prodMk (continuous_const.prodMk hρ))⟩

theorem VS10_apply (y : ↥(Sanctions.S : Set ℝ)) :
    E.VS10 y = E.toParams.U_S y.val 0 (E.stageResp y.val) := rfl

theorem pT_integrandS (V : Val) (y s : ℝ) :
    E.pT.integrandS (fun _ => 0) (fun z => V z) (y, s) = E.toParams.U_S y 0 s := by
  simp [AbstractGame.Params.integrandS, AbstractGame.Params.profileβ_S, ContinuationProfile.p10]

theorem pT_joint_T_top_integrand (V_T V_S : Val) {y : ℝ} (hy : y ∈ Sanctions.I) (a : ℝ) :
    E.pT.joint_T_top_integrand V_T V_S y a = E.targetObj10 V_T y a := by
  unfold targetObj10
  simp only [AbstractGame.Params.joint_T_top_integrand, E.pT_σ_dyn_top _ hy]
  simp [AbstractGame.Params.profileβ_T, ContinuationProfile.p10]

/-- **The Target-only equilibrium of a chord economy**: a top-selector
feedback Stackelberg equilibrium at the `10` view, with the Sender at its
stage value and the Target at the fixed point of its operator against the
stage response; the leader policy is full defiance, derived as the strict
unique argmax. Rule 15: constructed. -/
def targetOnlyEquilibriumTop (hTM : E.LossOffset) :
    E.toParams.RegimeEquilibrium ContinuationProfile.p10 where
  V_T := (E.VT10 hTM)
  V_S := E.VS10
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_refl 0, zero_le_one⟩
  V_S_fix := by
    ext y
    change E.VS10 y = sSup ((fun s => E.pT.integrandS (fun _ => 0) (fun z => E.VS10 z)
      (y.val, s)) '' Sanctions.I)
    have hgt : IsGreatest ((fun s => E.pT.integrandS (fun _ => 0) (fun z => E.VS10 z)
        (y.val, s)) '' Sanctions.I)
        (E.toParams.U_S y.val 0 (E.toParams.σ y.val 0)) := by
      refine ⟨⟨_, E.toParams.σ_mem y.val 0, E.pT_integrandS _ _ _⟩, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [E.pT_integrandS]
      exact E.toParams.σ_isMaxOn_U_S y.val 0 hs
    rw [hgt.csSup_eq]
    rfl
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => E.pT.joint_T_top_integrand (E.VT10 hTM) E.VS10 y.val a)
        '' Sanctions.I)
        (E.pT.joint_T_top_integrand (E.VT10 hTM) E.VS10 y.val 0) := by
      refine ⟨⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      dsimp only
      rw [E.pT_joint_T_top_integrand _ _ y.property, E.pT_joint_T_top_integrand _ _ y.property]
      exact (E.zero_isMaxOn_joint10 hTM) (E.VT10_mem hTM) y.property ha
    rw [hgt.csSup_eq, E.pT_joint_T_top_integrand _ _ y.property]
    have h := congrArg (fun V : Val => V y) (E.VT10_fix hTM)
    simp only at h
    rw [targetOp10_apply] at h
    exact h.symm
  α_opt_top := by
    intro x hx
    rw [isMaxOn_iff]
    intro a ha
    rw [E.pT_joint_T_top_integrand _ _ hx, E.pT_joint_T_top_integrand _ _ hx]
    exact (E.zero_isMaxOn_joint10 hTM) (E.VT10_mem hTM) hx ha

/-- **Uniqueness of defiance at the Target-only equilibrium.** -/
theorem targetOnlyEquilibriumTop_argmax_unique (hTM : E.LossOffset) {x : ℝ}
    (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.pT.joint_T_top_integrand (E.targetOnlyEquilibriumTop hTM).V_T
      (E.targetOnlyEquilibriumTop hTM).V_S x b) Sanctions.I a) :
    a = (E.targetOnlyEquilibriumTop hTM).α x := by
  apply (E.targetArgmax10_eq_zero hTM) (E.VT10_mem hTM) hx ha
  intro b hb
  have := hmax hb
  simp only [Set.mem_setOf_eq] at this ⊢
  change E.pT.joint_T_top_integrand (E.VT10 hTM) E.VS10 x b
    ≤ E.pT.joint_T_top_integrand (E.VT10 hTM) E.VS10 x a at this
  rwa [E.pT_joint_T_top_integrand _ _ hx, E.pT_joint_T_top_integrand _ _ hx] at this

/-- **The realised Target-only rule is the stage selector at defiance.** -/
theorem targetOnlyRule_eq_stage (hTM : E.LossOffset) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x = E.σ x 0 := by
  change E.pT.σ_dyn_top E.VS10 x 0 = E.toParams.σ x 0
  exact E.pT_σ_dyn_top _ hx 0

/-! ## 5. The Target-only path: wash-in to a fixed point of the stage selector -/

/-- The state path under the Target-only equilibrium. -/
def targetOnlyPath (hTM : E.LossOffset) (x₀ : ℝ) (t : ℕ) : ℝ :=
  E.toParams.rulePathF (E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM)) x₀ t

theorem targetOnlyRule_mem (hTM : E.LossOffset) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x ∈ Sanctions.I := by
  rw [E.targetOnlyRule_eq_stage hTM hx]; exact E.σ_mem x 0

theorem targetOnlyRule_monotoneOn (hTM : E.LossOffset) :
    MonotoneOn (E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM)) Sanctions.I := by
  intro x hx y hy hxy
  rw [E.targetOnlyRule_eq_stage hTM hx, E.targetOnlyRule_eq_stage hTM hy]
  exact E.stage_argmax_mono hx hy hxy

theorem targetOnlyRule_continuousOn (hTM : E.LossOffset) :
    ContinuousOn (E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM)) Sanctions.I :=
  E.stageResp_continuous.continuousOn.congr (fun _ hx => E.targetOnlyRule_eq_stage hTM hx)

theorem targetOnlyPath_mem (hTM : E.LossOffset) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    E.targetOnlyPath hTM x₀ t ∈ Sanctions.I :=
  E.toParams.rulePathF_mem_I_of_rule_mem (fun _ hx => E.targetOnlyRule_mem hTM hx) hx₀ t

/-- **Wash-in under the Target-only equilibrium**: the path approaches the
sanction floor `b = σ(0, 0)` at least geometrically from below. -/
theorem targetOnlyPath_ge_approach (hTM : E.LossOffset) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, approach E.sfloor E.dlo t ≤ (E.targetOnlyPath hTM) x₀ t :=
  E.toParams.rulePathF_ge_approach_of_rule_ge E.hdlo0.le E.hSlo E.sfloor_mem
    (fun _ hx => E.targetOnlyRule_mem hTM hx)
    (fun _ hx => by rw [E.targetOnlyRule_eq_stage hTM hx]; exact E.sfloor_le hx) hx₀

/-- **Convergence to a fixed point of the stage selector**, from every start:
the path converges to some `z` with `σ(z, 0) = z`, at or above the floor. The
limit may depend on the start (see the header). -/
theorem targetOnlyPath_tendsto (hTM : E.LossOffset) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z ∈ Sanctions.I, E.σ z 0 = z ∧ E.sfloor ≤ z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z) := by
  obtain ⟨z, hz, hfix, htend⟩ :=
    E.toParams.rulePathF_tendsto_fixedPoint_of_monotoneOn
      (fun _ hx => E.targetOnlyRule_mem hTM hx) (E.targetOnlyRule_monotoneOn hTM)
      (E.targetOnlyRule_continuousOn hTM) hx₀
  have hRz := E.toParams.rule_eq_self_of_closedLoop_fixed E.hdlo0 E.hSlo hz
    (E.targetOnlyRule_mem hTM hz) hfix
  rw [E.targetOnlyRule_eq_stage hTM hz] at hRz
  refine ⟨z, hz, hRz, ?_, htend⟩
  rw [← hRz]
  exact E.sfloor_le hz

/-- **The Target-only limit lies strictly below the forward-looking one, given a
nondecreasing response** (renovation item BH4.1, 2026-10-06), from every start. General
in `F`; under the stage appetite `u_hi < q`. This is `targetOnly_limit_lt_dynamic_limit`
with the rally margin replaced by what it was used for: the realised rule of the
forward-looking equilibrium `equilibriumTop hTM hmono` is nondecreasing. That lets the
forward-looking path dominate the Target-only path period by period (and makes it
converge); the strict order of the limits comes from the strict wedge
(`responsePath_gt_stage`), which needs no margin. -/
theorem targetOnly_limit_lt_dynamic_limit_of_response_monotone (hS : E.uhi < E.q)
    (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ z₁₀ < z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto (E.dynamicPathOf hTM hmono x₀) atTop (𝓝 z) := by
  obtain ⟨z₁₀, hz₁₀, hfix₁₀, -, htend₁₀⟩ := E.targetOnlyPath_tendsto hTM hx₀
  obtain ⟨z, hz, hfix, -, -, htend⟩ :=
    E.dynamicPath_tendsto_of_response_monotone hS hTM hmono hx₀
  have hrule : MonotoneOn
      (E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono)) Sanctions.I := by
    intro x hx y hy hxy
    rw [E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hx,
      E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hy]
    exact hmono hx hy hxy
  have hdom : ∀ t, (E.targetOnlyPath hTM) x₀ t ≤ E.dynamicPathOf hTM hmono x₀ t :=
    E.toParams.rulePathF_le_of_rule_le_and_upper_mono
      (fun _ hx => E.targetOnlyRule_mem hTM hx)
      (E.dynamicRule_mem_of_response_monotone hTM hmono) hrule
      (fun x hx => by
        rw [E.targetOnlyRule_eq_stage hTM hx,
          E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hx]
        exact (E.responsePath_gt_stage hS E.VSstar_mem hx).le) hx₀
  have hle : z₁₀ ≤ z := le_of_tendsto_of_tendsto' htend₁₀ htend hdom
  refine ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, ?_, htend₁₀, htend⟩
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    subst h
    have hgt := E.responsePath_gt_stage hS E.VSstar_mem hz
    rw [hfix] at hgt
    linarith [hfix₁₀]

/-- **The Target-only reading, general in `F` and in the payoffs, given a nondecreasing
response** (renovation item BH4.1, 2026-10-06): (i) the same primitives; (ii) the Target
defies, uniquely, and the realised sanction is the stage selector at defiance; (iii) the
state washes in, above the approach to the floor, and converges to a fixed point of the
stage selector from every start; (iv) that limit is strictly below the limit of the
forward-looking equilibrium `equilibriumTop hTM hmono` from the same start. This is
`target_only_regime_generalF` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]`, which is all clause (iv) used
the margin for. Only clause (iv) reads `hmono` and the stage appetite `u_hi < q`. -/
theorem target_only_regime_generalF_of_response_monotone (hS : E.uhi < E.q)
    (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    (E.pT.U_T = E.toParams.U_T ∧ E.pT.U_S = E.toParams.U_S ∧ E.pT.F = E.toParams.F) ∧
    (∀ x ∈ Sanctions.I,
      (E.targetOnlyEquilibriumTop hTM).α x = 0 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pT.joint_T_top_integrand (E.targetOnlyEquilibriumTop hTM).V_T
          (E.targetOnlyEquilibriumTop hTM).V_S x b) Sanctions.I a → a = 0) ∧
      E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x = E.σ x 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, approach E.sfloor E.dlo t ≤ (E.targetOnlyPath hTM) x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.σ z 0 = z ∧ E.sfloor ≤ z ∧
        Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ z₁₀ < z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto (E.dynamicPathOf hTM hmono x₀) atTop (𝓝 z)) :=
  ⟨⟨rfl, rfl, rfl⟩,
   fun _ hx => ⟨rfl, fun _ ha hmax => (E.targetOnlyEquilibriumTop_argmax_unique hTM) hx ha hmax,
     (E.targetOnlyRule_eq_stage hTM) hx⟩,
   fun _ hx₀ => ⟨(E.targetOnlyPath_ge_approach hTM) hx₀, (E.targetOnlyPath_tendsto hTM) hx₀⟩,
   fun _ hx₀ => E.targetOnly_limit_lt_dynamic_limit_of_response_monotone hS hTM hmono hx₀⟩

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- **The Target-only limit lies strictly below the forward-looking one**, from
every start. The forward-looking rule sits strictly above the stage selector at
every state (`responsePath_gt_stage`) and is monotone under the rally margin, so
the forward-looking path dominates the Target-only path period by period and the
limits are ordered weakly; they cannot coincide, because at the forward-looking
limit the sanction equals the state and exceeds the stage selector. General in `F`.
Under the stage appetite `u_hi < q` (BH3.1, 2026-10-06: the binder was interiority
`A < q`, read only through `u_hi < q` by the strict wedge and the limit bound). The
rally-margin form of `targetOnly_limit_lt_dynamic_limit_of_response_monotone` (BH4.1). On
the two-sided extension since renovation item BJ3.1 (2026-10-07): the rally margin reads
the two-sided curvature data. -/
theorem targetOnly_limit_lt_dynamic_limit (hS : E.uhi < E.q) (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ z₁₀ < z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z) :=
  E.targetOnly_limit_lt_dynamic_limit_of_response_monotone hS hTM
    (E.responsePath_monotoneOn_of_margin hmargin) hx₀

/-- **The Target-only reading, general in `F` and in the payoffs** (the third
cell of the factorial): (i) the same primitives; (ii) the Target defies,
uniquely, and the realised sanction is the stage selector at defiance; (iii)
the state washes in, above the approach to the floor, and converges to a fixed
point of the stage selector from every start; (iv) given the rally margin, that
limit is strictly below the forward-looking limit from the same start. Only
clause (iv) reads the stage appetite `u_hi < q` (BH3.1, 2026-10-06: the binder was
interiority `A < q`, of which only `u_hi < q` is read). The rally-margin form of
`target_only_regime_generalF_of_response_monotone` (BH4.1). On the two-sided extension
since renovation item BJ3.1 (2026-10-07). -/
theorem target_only_regime_generalF (hS : E.uhi < E.q) (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    (E.pT.U_T = E.toParams.U_T ∧ E.pT.U_S = E.toParams.U_S ∧ E.pT.F = E.toParams.F) ∧
    (∀ x ∈ Sanctions.I,
      (E.targetOnlyEquilibriumTop hTM).α x = 0 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pT.joint_T_top_integrand (E.targetOnlyEquilibriumTop hTM).V_T
          (E.targetOnlyEquilibriumTop hTM).V_S x b) Sanctions.I a → a = 0) ∧
      E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x = E.σ x 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, approach E.sfloor E.dlo t ≤ (E.targetOnlyPath hTM) x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.σ z 0 = z ∧ E.sfloor ≤ z ∧
        Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ z₁₀ < z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z)) :=
  E.target_only_regime_generalF_of_response_monotone hS hTM
    (E.responsePath_monotoneOn_of_margin hmargin)

end ChordEconomyTwoSided

/-! ## 6. The quadratic–linear family: the closed-form steady state (sign-off M6)

On the quadratic–linear family the stage selector at defiance is the vertex
`(u₀ + r·x)/q` (`toChord_σ_zero`), affine with slope `r/q < 1`, so its fixed
point is unique, the closed form `u₀/(q − r)`, and the Target-only path
converges to it at a geometric rate. With the lower sanction chord `d_lo`, the
centred contraction lemma of `Foundations/CenteredContraction` gives
`|x_t − u₀/(q − r)| ≤ θ^t |x₀ − u₀/(q − r)|` with `θ = 1 − d_lo(1 − r/q) ∈ [0,1)`.
These are exact-form statements and stay on the family, as do the comparisons of
two members that differ in `r`. Since renovation item BJ2.3 (2026-10-07) interiority is
a hypothesis `hInt` of the results here that read it, not a field of the family. -/

namespace PlacableEconomyF

variable (E : PlacableEconomyF)

/-- **The family's myopic policy in closed form**: the least compliance at which
the stage sanction `max 0 (min 1 ((u₀ − k·a + r·x)/q))` vanishes is
`(u₀ + r·x)/k`. Under the family's stage placability `u₀ + r < k` (the chord form
`u_hi < k_lo`), which is all the proof reads (BH3.2, 2026-10-06; placability
`u₀ + r + β_S·K_S·d_hi ≤ k` implies it, `toChord_myopicPolicy`). A closed form on
the quadratic–linear family, general in the family's transition `F`. -/
theorem toChord_myopicPolicy_of_lt (hkA : E.u₀ + E.r < E.k) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toChord.myopicPolicy x = (E.u₀ + E.r * x) / E.k := by
  rw [E.toChord.myopicPolicy_eq hx]
  have hk := E.k_pos
  have hnum0 : 0 ≤ E.u₀ + E.r * x := by nlinarith [E.hu₀, E.hr, hx.1]
  have hnum1 : E.u₀ + E.r * x < E.k := by nlinarith [E.hr, hx.2]
  unfold ChordEconomy.zeroLevel00 Sanctions.ZeroLevel.level
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨⟨div_nonneg hnum0 hk.le, (div_lt_one hk).2 hnum1 |>.le⟩, ?_⟩
    show symσ E.q E.u₀ E.k E.r x ((E.u₀ + E.r * x) / E.k) = 0
    unfold symσ
    have h0 : E.u₀ - E.k * ((E.u₀ + E.r * x) / E.k) + E.r * x = 0 := by
      field_simp; ring
    rw [h0, zero_div, min_eq_right zero_le_one, max_self]
  · rintro a ⟨ha, hz⟩
    by_contra hlt
    push_neg at hlt
    change symσ E.q E.u₀ E.k E.r x a = 0 at hz
    unfold symσ at hz
    have hpos : 0 < (E.u₀ - E.k * a + E.r * x) / E.q := by
      apply div_pos _ E.hq
      rw [lt_div_iff₀ hk] at hlt
      linarith
    have hmin : 0 < min 1 ((E.u₀ - E.k * a + E.r * x) / E.q) := lt_min one_pos hpos
    have := le_max_right 0 (min 1 ((E.u₀ - E.k * a + E.r * x) / E.q))
    linarith

/-- **The family's myopic policy in closed form**, under the family's placability:
the corollary of `toChord_myopicPolicy_of_lt` at `u₀ + r < k`, which placability
implies through `uhi_lt_A` and `A_le_k` (BH3.2). -/
theorem toChord_myopicPolicy (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toChord.myopicPolicy x = (E.u₀ + E.r * x) / E.k := by
  have hkA : E.u₀ + E.r < E.k := by
    have h1 := E.toChord.uhi_lt_A
    have h2 := E.toChord.A_le_k (E.toChord_placable hP)
    change E.u₀ + E.r < E.toChord.A at h1
    change E.toChord.A ≤ E.k at h2
    linarith
  exact E.toChord_myopicPolicy_of_lt hkA hx

/-- **The family's rally margin at a flat transition** (convex state sections,
`M_cx = 0`, and no mixed curvature, `M_mix = 0`): the family's stage payoff is
affine in the state, so the margin reads `0 ≤ r`. -/
theorem familyMargin_of_flat (hMcx : E.Mcx = 0) (hMmix : E.Mmix = 0) :
    E.βS * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.r := by
  have h := E.toChord.margin_of_flat rfl hMcx hMmix
  rw [E.toChord_SigC] at h
  exact h

/-- The Target-only steady state of the family. -/
def steady10 : ℝ := E.u₀ / (E.q - E.r)

/-- The Target-only steady state is positive, under interiority (`r < q`; the
hypothesis `hInt` since renovation item BJ2.3, until then a field). General in `F`. -/
theorem steady10_pos (hInt : E.Interior) : 0 < E.steady10 :=
  div_pos E.hu₀ (sub_pos.2 (E.r_lt_q hInt))

/-- **The Target-only steady state rises strictly with the Sender's rally slope**
(round L, doc 80 M10; the reader's document 03 §6.1): two members with the same
stage floor `u₀` and sanction curvature `q` and `r₁ < r₂` have
`u₀/(q − r₁) < u₀/(q − r₂)`. Kaempfer–Lowenberg's pro-sanction effectiveness,
read as the rally slope `r`, raises the cell-`10` long-run entrenchment. A
comparison of closed forms across economies; the cell-`11` analogue is not a
theorem (the constructed Sender value would have to be identified across
economies). Renovation item BJ2.3 (2026-10-07): interiority of the member with the
larger rally slope, `hInt₂`, is now a hypothesis (it was a field); it is what keeps
`r₂ < q`, without which the closed form `u₀/(q − r₂)` is not a steady state. Of
interiority the proof reads only `r₂ < q` (`r_lt_q`). General in `F`. -/
theorem steady10_lt_of_r_lt (E₁ E₂ : PlacableEconomyF) (hu : E₁.u₀ = E₂.u₀)
    (hq : E₁.q = E₂.q) (hr : E₁.r < E₂.r) (hInt₂ : E₂.Interior) :
    E₁.steady10 < E₂.steady10 := by
  unfold steady10
  rw [hu, hq]
  exact div_lt_div_of_pos_left E₂.hu₀ (sub_pos.2 (E₂.r_lt_q hInt₂)) (by linarith)

/-- **The Target-only rule rises strictly with the rally slope at every positive
state**: `(u₀ + r₁x)/q < (u₀ + r₂x)/q` for `x > 0` (and the two agree at
`x = 0`). -/
theorem vertex_lt_of_r_lt (E₁ E₂ : PlacableEconomyF) (hu : E₁.u₀ = E₂.u₀)
    (hq : E₁.q = E₂.q) (hr : E₁.r < E₂.r) {x : ℝ} (hx : 0 < x) :
    E₁.vertex x < E₂.vertex x := by
  unfold vertex
  rw [hu, hq]
  apply div_lt_div_of_pos_right _ E₂.hq
  have := mul_lt_mul_of_pos_right hr hx
  linarith

/-- The vertex fixes exactly `u₀/(q − r)`, under interiority (`r < q`; the hypothesis
`hInt` since renovation item BJ2.3). General in `F`. -/
theorem vertex_eq_self_iff (hInt : E.Interior) (z : ℝ) : E.vertex z = z ↔ z = E.steady10 := by
  unfold vertex steady10
  have hq : E.q ≠ 0 := E.hq.ne'
  have hqr : E.q - E.r ≠ 0 := (sub_pos.2 (E.r_lt_q hInt)).ne'
  constructor
  · intro h
    rw [div_eq_iff hq] at h
    rw [eq_div_iff hqr]
    linarith
  · intro h
    rw [div_eq_iff hq]
    rw [eq_div_iff hqr] at h
    linarith

/-- The rule is affine about the steady state with slope `r/q`, under interiority
(`r < q`; the hypothesis `hInt` since renovation item BJ2.3). General in `F`. -/
theorem vertex_sub_steady10 (hInt : E.Interior) (x : ℝ) :
    E.vertex x - E.steady10 = E.r / E.q * (x - E.steady10) := by
  unfold vertex steady10
  have hq : E.q ≠ 0 := E.hq.ne'
  have hqr : E.q - E.r ≠ 0 := (sub_pos.2 (E.r_lt_q hInt)).ne'
  field_simp
  ring

theorem r_div_q_nonneg : 0 ≤ E.r / E.q := div_nonneg E.hr E.hq.le
/-- `r/q < 1`, under interiority (the hypothesis `hInt` since renovation item BJ2.3, until
then a field). General in `F`. -/
theorem r_div_q_lt_one (hInt : E.Interior) : E.r / E.q < 1 :=
  (div_lt_one E.hq).2 (E.r_lt_q hInt)

/-- The Target-only steady state is a feasible state, under interiority (the hypothesis
`hInt` since renovation item BJ2.3). General in `F`. -/
theorem steady10_mem (hInt : E.Interior) : E.steady10 ∈ Sanctions.I := by
  have h := E.vertex_eq_self_iff hInt E.steady10 |>.2 rfl
  have := E.vertex_mem hInt (x := E.steady10) ⟨(E.steady10_pos hInt).le, ?_⟩
  · rwa [h] at this
  · -- `steady10 ≤ 1` from `u₀ + r < q`.
    unfold steady10
    rw [div_le_one (sub_pos.2 (E.r_lt_q hInt))]
    linarith [E.u₀_r_lt_q hInt]

/-- **On the family the Target-only rule is the vertex.** Renovation item BJ2.3
(2026-10-07): interiority is the hypothesis `hInt` (it was a field); it makes the stage
selector the vertex and gives the floor condition `u₀ ≤ q` that carries the loss-offset
margin to the chord economy. General in `F`. -/
theorem targetOnlyRule_eq_vertex (hInt : E.Interior) (hTM : E.LossOffset) {x : ℝ}
    (hx : x ∈ Sanctions.I) :
    E.toChord.pT.dynamicEquilibriumRule
        (E.toChord.targetOnlyEquilibriumTop (E.toChord_lossOffset (E.u₀_le_q hInt) hTM)) x
      = E.vertex x := by
  rw [E.toChord.targetOnlyRule_eq_stage _ hx]
  exact E.toChord_σ_zero hInt hx

/-- **Geometric convergence of the family's Target-only path**, general in `F`.
Interiority is the hypothesis `hInt` since renovation item BJ2.3 (it was a field). -/
theorem targetOnlyPath_error_le_geometric (hInt : E.Interior) (hTM : E.LossOffset) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, |E.toChord.targetOnlyPath (E.toChord_lossOffset (E.u₀_le_q hInt) hTM) x₀ t
        - E.steady10|
      ≤ (1 - E.dlo * (1 - E.r / E.q)) ^ t * |x₀ - E.steady10| := by
  intro t
  have hRz : ∀ x ∈ Sanctions.I,
      E.toChord.pT.dynamicEquilibriumRule
          (E.toChord.targetOnlyEquilibriumTop (E.toChord_lossOffset (E.u₀_le_q hInt) hTM)) x
          - E.steady10
        = E.r / E.q * (x - E.steady10) :=
    fun x hx => by
      rw [E.targetOnlyRule_eq_vertex hInt hTM hx]; exact E.vertex_sub_steady10 hInt x
  have h := Sanctions.CenteredContraction.iterate_abs_le (F := E.toChord.F)
    (fun s _ => (E.toChord.F_mono_x s).monotoneOn _)
    (fun y _ => (E.toChord.F_mono_s y).monotoneOn _)
    (fun y _ => E.toChord.F_diag y)
    E.toChord.hSlo E.r_div_q_nonneg (E.r_div_q_lt_one hInt).le
    (fun _ hx => E.toChord.targetOnlyRule_mem _ hx) hRz hx₀ t
  exact h.2

/-- **Convergence of the family's Target-only path to `u₀/(q − r)` from every
start**: the abstract limit is a fixed point of the vertex, and the vertex has
exactly one. Interiority is the hypothesis `hInt` since renovation item BJ2.3 (it was a
field). General in `F`. -/
theorem targetOnlyPath_tendsto (hInt : E.Interior) (hTM : E.LossOffset) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    Tendsto (E.toChord.targetOnlyPath (E.toChord_lossOffset (E.u₀_le_q hInt) hTM) x₀) atTop
      (𝓝 E.steady10) := by
  obtain ⟨z, hz, hfix, -, htend⟩ :=
    E.toChord.targetOnlyPath_tendsto (E.toChord_lossOffset (E.u₀_le_q hInt) hTM) hx₀
  rw [E.toChord_σ_zero hInt hz] at hfix
  rwa [(E.vertex_eq_self_iff hInt z).1 hfix] at htend

/-- **The family's Target-only steady state lies strictly below the forward-looking
limit, given a nondecreasing response** (renovation item BH4.1, 2026-10-06), from every
start. On the quadratic–linear family, general in the family's transition `F`. This is
`targetOnly_steady_lt_dynamic_steady` with the rally margin replaced by a response
`responsePath VSstar` of the member's chord economy that is nondecreasing on `[0, 1]`,
read at `equilibriumTop` and its path `dynamicPathOf`. Interiority is the hypothesis
`hInt` since renovation item BJ2.3 (it was a field). -/
theorem targetOnly_steady_lt_dynamic_steady_of_response_monotone (hInt : E.Interior)
    (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.toChord.responsePath E.toChord.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z ∈ Sanctions.I, E.toChord.responsePath E.toChord.VSstar z = z ∧ E.steady10 < z ∧
      Tendsto (E.toChord.dynamicPathOf (E.toChord_lossOffset (E.u₀_le_q hInt) hTM) hmono x₀)
        atTop (𝓝 z) := by
  obtain ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, hlt, -, htend⟩ :=
    E.toChord.targetOnly_limit_lt_dynamic_limit_of_response_monotone
      (E.toChord.uhi_lt_q (E.toChord_interior hInt)) (E.toChord_lossOffset (E.u₀_le_q hInt) hTM)
      hmono hx₀
  rw [E.toChord_σ_zero hInt hz₁₀] at hfix₁₀
  rw [(E.vertex_eq_self_iff hInt z₁₀).1 hfix₁₀] at hlt
  exact ⟨z, hz, hfix, hlt, htend⟩

/-- **The family's Target-only steady state lies strictly below the
forward-looking limit**, from every start. The rally-margin form of
`targetOnly_steady_lt_dynamic_steady_of_response_monotone` (BH4.1). Interiority is the
hypothesis `hInt` since renovation item BJ2.3 (it was a field). General in `F`. -/
theorem targetOnly_steady_lt_dynamic_steady (hInt : E.Interior) (hTM : E.LossOffset)
    (hmargin : E.βS * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.r)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z ∈ Sanctions.I, E.toChord.responsePath E.toChord.VSstar z = z ∧ E.steady10 < z ∧
      Tendsto (E.toChord.dynamicPath (E.toChord_lossOffset (E.u₀_le_q hInt) hTM)
        (E.toChord_margin hmargin) x₀) atTop (𝓝 z) :=
  E.targetOnly_steady_lt_dynamic_steady_of_response_monotone hInt hTM
    (E.toChord.responsePath_monotoneOn_of_margin (E.toChord_margin hmargin)) hx₀

/-- **The Target-only reading on the quadratic–linear family** (the closed-form
companion of `ChordEconomyTwoSided.target_only_regime_generalF`): the Target defies and
the realised sanction is the vertex `(u₀ + r·x)/q`; the path washes in above the
approach to `u₀/q` and converges to the unique steady state `u₀/(q − r)` from
every start; given the rally margin, that steady state is strictly below the
forward-looking limit. Renovation item BJ2.3 (2026-10-07): interiority is the
hypothesis `hInt` (it was a field of the family). General in `F`. -/
theorem target_only_regime_closedForm (hInt : E.Interior) (hTM : E.LossOffset)
    (hmargin : E.βS * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.r) :
    (∀ x ∈ Sanctions.I,
      (E.toChord.targetOnlyEquilibriumTop (E.toChord_lossOffset (E.u₀_le_q hInt) hTM)).α x
        = 0 ∧
      E.toChord.pT.dynamicEquilibriumRule
        (E.toChord.targetOnlyEquilibriumTop (E.toChord_lossOffset (E.u₀_le_q hInt) hTM)) x
          = E.vertex x) ∧
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach (E.u₀ / E.q) E.dlo t
        ≤ E.toChord.targetOnlyPath (E.toChord_lossOffset (E.u₀_le_q hInt) hTM) x₀ t) ∧
      Tendsto (E.toChord.targetOnlyPath (E.toChord_lossOffset (E.u₀_le_q hInt) hTM) x₀) atTop
        (𝓝 E.steady10)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.toChord.responsePath E.toChord.VSstar z = z ∧
      E.steady10 < z ∧
      Tendsto (E.toChord.dynamicPath (E.toChord_lossOffset (E.u₀_le_q hInt) hTM)
        (E.toChord_margin hmargin) x₀) atTop (𝓝 z)) :=
  ⟨fun _ hx => ⟨rfl, E.targetOnlyRule_eq_vertex hInt hTM hx⟩,
   fun _ hx₀ => ⟨by
      have h := E.toChord.targetOnlyPath_ge_approach
        (E.toChord_lossOffset (E.u₀_le_q hInt) hTM) hx₀
      rwa [E.toChord_sfloor (E.u₀_le_q hInt)] at h, E.targetOnlyPath_tendsto hInt hTM hx₀⟩,
   fun _ hx₀ => E.targetOnly_steady_lt_dynamic_steady hInt hTM hmargin hx₀⟩

end PlacableEconomyF

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.ChordEconomy.targetOnlyEquilibriumTop
#print axioms Sanctions.Examples.ChordEconomy.targetOnlyPath_tendsto
#print axioms Sanctions.Examples.ChordEconomyTwoSided.targetOnly_limit_lt_dynamic_limit
#print axioms Sanctions.Examples.ChordEconomyTwoSided.target_only_regime_generalF
#print axioms ChordEconomy.targetOnly_limit_lt_dynamic_limit_of_response_monotone
#print axioms ChordEconomy.target_only_regime_generalF_of_response_monotone
#print axioms Sanctions.Examples.PlacableEconomyF.target_only_regime_closedForm
#print axioms Sanctions.Examples.PlacableEconomyF.targetOnlyPath_error_le_geometric
#print axioms Sanctions.Examples.PlacableEconomyF.steady10_lt_of_r_lt

end Examples
end Sanctions
