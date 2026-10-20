/-
Sanctions/Examples/PlacableSenderRegime01.lean

**The fourth reading of a chord economy: the Sender looks ahead, the
Target does not** (`ContinuationProfile.p01`), and the four-cell theorem.

Doc 62 recorded this reading as open because the myopic Target's stage
objective against the forward-looking response had no derived shape in
compliance. It has one once the transition's sanction sections are
semiconvex — the modulus `Mcs` of the subclass `ChordEconomyCs` (Rule 3
authorized 2026-09-05, doc 63; a subclass rather than a base field since doc
65) — and the construction then has an unexpected simplification (on the
abstract payoffs since round AV, 2026-09-25, doc 104):

* **The Sender's value is constructed before the Target's policy is
  identified.** At the Target's optimum the realised sanction is zero, and
  along that zero-sanction path the Sender's stage payoff and its transition
  `F(x, 0)` do not depend on compliance *when a concession is worth nothing to
  the Sender at zero sanction* (`ZeroSanctionNeutral`, sign-off M2: a
  hypothesis of this reading's equilibrium, never a field). So `V_S` is the
  fixed point of one contraction `W ↦ U_S(x, 0, 0) + β_S·W(F(x,0))`
  (`relaxOp`), it lies in the two-sided carrier, and the Bellman equation at the
  Target's policy holds because the argmax there is zero. (This is a property of
  the constructed equilibrium, not independence from an arbitrary Target
  policy: a policy inducing positive sanctions would enter the Sender's value.)
* **The response's relief rate is bounded below.** The Sender's objective is
  `μ`-strongly concave and `M_tot`-semiconvex in the sanction, with
  `M_tot = Q̄ + β_S(σ_C·d_hi² + K_S·M_cs)`; a unit of extra compliance is a tilt
  of rate at least `k_lo` (placation, S10), so by
  `Foundations/SemiconvexArgmaxShift` the interior response falls by at least
  `k_lo·Δa/M_tot` (`ρ01_shift_ge_linear`).
* **The Target's optimum is the zero level `a*(x)`** — the least compliance
  at which the response vanishes (`Foundations/ZeroLevel`) — and it is unique
  given the relief margin `ℓ_hi·M_tot < k_lo·p_lo` (a theorem hypothesis, never
  a field). Below `a*`, at distance `Δ = a* − a`, the response is at least
  `k_lo·Δ/M_tot` (`ρ01_ge_of_lt_sharp`), and the margin makes the sanction pain
  avoided by closing that distance, at least `p_lo·ρ`, exceed its cost, at most
  `ℓ_hi·Δ`; above `a*` compliance buys nothing and costs at least `ℓ_lo` per
  unit. The two-branch margin `2ℓ_hi·max(M_tot, k_lo) < k_lo·p_lo` of the first
  construction implies the sharp one (`reliefSharp_of_relief`) and survives as
  the hypothesis of the unprimed compatibility theorems.
* **`a*(x) > a⁰⁰(x)`**: the forward-looking Sender extracts strictly more
  compliance for complete relief than the myopic one, because its response
  at `a⁰⁰` is still positive (the continuation wedge).
* **The state washes out**, exactly as under `00`.

**The four-cell theorem** (`four_cell_generalF'`): the state washes out under
`00` and `01` and washes in under `10` and `11`; the Target channel is what
produces defiance and entrenchment, and given defiance the Sender channel
raises the limit (`z₁₀ < z₁₁` from every start). On the quadratic–linear family
the `10` limit is the closed form `u₀/(q − r)` (`PlacableEconomyFcs.
four_cell_closedForm`, sign-off M6). No interaction is claimed beyond these
directions.

Rule 1: `a*` is the unique argmax, `V_S` and `V_T` are constructed. Rule 3:
one authorized field, on the subclass, and theorem-level margins. Rule 22:
general in `F`.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation item BG3.2 (2026-10-06): the four-cell theorems no longer take `hSR`. The
sharp relief margin they already assume implies it (`stageRelief_of_reliefSharp`, since
`Q̄ ≤ M_tot` and `ℓ_hi > 0`), so the myopic cell reads it from there.

Renovation item BH4.1 (2026-10-06): the four-cell theorem reads the rally margin only in
the `11` cell, and only to make the forward-looking response nondecreasing.
`four_cell_generalF'_of_response_monotone` takes that nondecreasing response `hmono` in
its place, at `equilibriumTop hTM hmono` and `dynamicPathOf hTM hmono`;
`four_cell_generalF'` keeps its statement and is the corollary at
`hmono := responsePath_monotoneOn_of_margin hmargin`.

Renovation item BJ2.3 (2026-10-07): the family `PlacableEconomyF` no longer carries the
interiority and stage relief fields. Its closed-form four-cell theorem
(`PlacableEconomyFcs.four_cell_closedForm`) takes interiority as the hypothesis `hInt`,
and reads the stage relief margin of the myopic cell from the sharp relief margin it
already assumes (`stageRelief_of_reliefSharp`, BG3.2).
-/
import Sanctions.Examples.PlacableSenderRegime10
import Sanctions.Examples.PlacableSenderWitnesses
import Sanctions.Foundations.SemiconvexArgmaxShift
import Sanctions.Foundations.TransitionExtension
import Sanctions.Foundations.ZeroLevel

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.TransitionChords
  Sanctions.GeometricApproach Sanctions.Mechanism Sanctions.Semiconcave

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-- The state part of the Riccati closure alone is below the modulus: the Schur
term `ρ²/μ` of `chSigImg` is nonnegative. -/
theorem chSig_le_SigV : chSig E.β_S E.σx E.SigV E.ghi E.KS E.Mx ≤ E.SigV := by
  have h := E.hSigV
  unfold chSigImg at h
  have hμ := E.mu_pos
  unfold mu at hμ
  have hnn : 0 ≤ plRho E.β_S E.rhi E.SigV E.ghi E.dhi E.KS E.Mm ^ 2
      / plMu E.β_S E.q E.SigV E.dhi E.KS E.Ms := div_nonneg (sq_nonneg _) hμ.le
  unfold KS at hnn ⊢
  linarith

end ChordEconomy

namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided ChordEconomyRelief

variable (E : ChordEconomyCs)

/-! ## 1. The profile view -/

/-- The Sender-only reading: the Sender's discount is `β_S`, the Target's `0`. -/
abbrev pS : AbstractGame.Params := E.toParams.withProfile ContinuationProfile.p01

theorem pS_β_T : E.pS.β_T = 0 := rfl
theorem pS_β_S : E.pS.β_S = E.toParams.β_S := rfl

theorem pS_σ_dyn_top (V : Val) (x a : ℝ) :
    E.pS.σ_dyn_top V x a = E.toParams.σ_dyn_top V x a := rfl

/-! ## 2. The Sender's value along zero sanctions -/

/-- `W ↦ U_S(y, 0, 0) + β_S·W(F(y,0))`. -/
def relaxOp (W : Val) : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) =>
        E.toParams.U_S y.val 0 0 + E.toParams.β_S * W (Sanctions.clipS' (E.toParams.F y.val 0)),
      by
      have hF : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.toParams.F y.val 0) :=
        E.toParams.F_continuous.comp (continuous_subtype_val.prodMk continuous_const)
      have hU : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.toParams.U_S y.val 0 0) :=
        E.toParams.U_S_continuous.comp
          (continuous_subtype_val.prodMk (continuous_const.prodMk continuous_const))
      exact hU.add
        (continuous_const.mul (W.continuous.comp (Sanctions.clipS'_continuous.comp hF)))⟩

theorem relaxOp_apply (W : Val) (y : ↥(Sanctions.S : Set ℝ)) :
    E.relaxOp W y
      = E.toParams.U_S y.val 0 0 + E.toParams.β_S * W (Sanctions.clipS' (E.toParams.F y.val 0)) :=
  rfl

theorem relaxOp_contracting : ContractingWith E.toParams.β_S_nnreal E.relaxOp := by
  refine ⟨E.toParams.β_S_nnreal_lt_one, ?_⟩
  apply lipschitzWith_of_pointwise_dist_le
  intro V W y
  rw [relaxOp_apply, relaxOp_apply, Real.dist_eq]
  have hβ : (0:ℝ) ≤ E.toParams.β_S := E.toParams.β_S_mem.1
  have h1 : |(E.toParams.U_S y.val 0 0
        + E.toParams.β_S * V (Sanctions.clipS' (E.toParams.F y.val 0)))
      - (E.toParams.U_S y.val 0 0
        + E.toParams.β_S * W (Sanctions.clipS' (E.toParams.F y.val 0)))|
      = E.toParams.β_S * |V (Sanctions.clipS' (E.toParams.F y.val 0))
          - W (Sanctions.clipS' (E.toParams.F y.val 0))| := by
    rw [show ∀ a b c : ℝ, (a + E.toParams.β_S * b) - (a + E.toParams.β_S * c)
        = E.toParams.β_S * (b - c) from fun a b c => by ring, abs_mul, abs_of_nonneg hβ]
  rw [h1]
  have h2 := BoundedContinuousFunction.dist_coe_le_dist (f := V) (g := W)
    (Sanctions.clipS' (E.toParams.F y.val 0))
  rw [Real.dist_eq] at h2
  have := mul_le_mul_of_nonneg_left h2 hβ
  convert this using 2

/-- **The relaxed operator preserves the two-sided carrier.** Five legs:
norm (the payoff bound `M_U`), Lipschitz (S2u and the upper state chord), lower
slope (S2 and the lower state chord), semiconcavity (the state section at zero
sanction of the jointly semiconcave objective, modulus `chSig ≤ σ_V`), and
semiconvexity (the stage's state convexity `τ_x` and the transition's, closed
by `σ_C`). -/
theorem relaxOp_mem2 {W : Val} (hW : W ∈ E.carrierS2) : E.relaxOp W ∈ E.carrierS2 := by
  have hβ : (0:ℝ) ≤ E.β_S := E.hβS0.le
  have hW1 := hW.1
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · -- Norm leg.
    have hMS0 : 0 ≤ E.MS := by
      unfold MS; exact div_nonneg (by linarith [E.MU_nonneg]) (by linarith [E.hβS1])
    rw [BoundedContinuousFunction.norm_le hMS0]
    intro y
    rw [relaxOp_apply, Real.norm_eq_abs]
    have hWb : |W (Sanctions.clipS' (E.toParams.F y.val 0))| ≤ E.MS := by
      have h := BoundedContinuousFunction.norm_coe_le_norm W
        (Sanctions.clipS' (E.toParams.F y.val 0))
      rw [Real.norm_eq_abs] at h
      exact h.trans hW1.1.1
    have hy := y.property
    have hU : |E.toParams.U_S y.val 0 0| ≤ E.MU := E.abs_U_S_le_MU hy zero_mem_I zero_mem_I
    have hMS : E.MU + E.β_S * E.MS ≤ E.MS := by
      unfold MS
      have h2 : 0 < 1 - E.β_S := by linarith [E.hβS1]
      have h2' : (1 - E.β_S) ≠ 0 := h2.ne'
      have hid : E.MU + E.β_S * (2 * E.MU / (1 - E.β_S))
          = E.MU * (1 + E.β_S) / (1 - E.β_S) := by field_simp; ring
      rw [hid]
      apply div_le_div_of_nonneg_right _ h2.le
      nlinarith [E.MU_nonneg, E.hβS1]
    calc |E.toParams.U_S y.val 0 0 + E.β_S * W (Sanctions.clipS' (E.toParams.F y.val 0))|
        ≤ |E.toParams.U_S y.val 0 0| + |E.β_S * W (Sanctions.clipS' (E.toParams.F y.val 0))| :=
          abs_add_le _ _
      _ ≤ E.MU + E.β_S * E.MS := by
          rw [abs_mul, abs_of_nonneg hβ]
          exact add_le_add hU (mul_le_mul_of_nonneg_left hWb hβ)
      _ ≤ E.MS := hMS
  · -- Lipschitz leg.
    intro y₁ y₂
    rw [relaxOp_apply, relaxOp_apply]
    have hlip := E.clip_lip hW1.1 (E.F y₂.val 0) (E.F_mem _ _ y₂.property zero_mem_I)
      (E.F y₁.val 0) (E.F_mem _ _ y₁.property zero_mem_I)
    have hband : |E.F y₂.val 0 - E.F y₁.val 0| ≤ E.ghi * |y₂.val - y₁.val| :=
      abs_sub_le_of_stateBand E.hglo0 (E.hbandAll 0 zero_mem_I) y₂.property y₁.property
    have hstage : |E.U_S y₂.val 0 0 - E.U_S y₁.val 0 0| ≤ E.whi * |y₂.val - y₁.val| :=
      E.hUS_stateLip 0 zero_mem_I y₁.val y₁.property y₂.val y₂.property
    have hdist : dist y₁ y₂ = |y₂.val - y₁.val| := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    rw [hdist]
    have hrew : (E.U_S y₂.val 0 0 + E.β_S * W (Sanctions.clipS' (E.F y₂.val 0)))
        - (E.U_S y₁.val 0 0 + E.β_S * W (Sanctions.clipS' (E.F y₁.val 0)))
        = (E.U_S y₂.val 0 0 - E.U_S y₁.val 0 0)
          + E.β_S * (W (Sanctions.clipS' (E.F y₂.val 0))
            - W (Sanctions.clipS' (E.F y₁.val 0))) := by ring
    rw [hrew]
    have hKS := E.KS_mul
    calc |(E.U_S y₂.val 0 0 - E.U_S y₁.val 0 0)
          + E.β_S * (W (Sanctions.clipS' (E.F y₂.val 0)) - W (Sanctions.clipS' (E.F y₁.val 0)))|
        ≤ |E.U_S y₂.val 0 0 - E.U_S y₁.val 0 0|
          + |E.β_S * (W (Sanctions.clipS' (E.F y₂.val 0))
            - W (Sanctions.clipS' (E.F y₁.val 0)))| := abs_add_le _ _
      _ ≤ E.whi * |y₂.val - y₁.val| + E.β_S * (E.KS * (E.ghi * |y₂.val - y₁.val|)) := by
          rw [abs_mul, abs_of_nonneg hβ]
          apply add_le_add hstage
          apply mul_le_mul_of_nonneg_left _ hβ
          exact hlip.trans (mul_le_mul_of_nonneg_left hband E.KS_pos.le)
      _ = E.KS * |y₂.val - y₁.val| := by rw [← hKS]; ring
  · -- Lower-slope leg.
    intro y₁ y₂ hy₁ hy₂ hle
    rw [relaxOp_apply, relaxOp_apply]
    have hyle : y₁.val ≤ y₂.val := hle
    have hd : dist y₁ y₂ = y₂.val - y₁.val := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hd]
    have hband := (E.hbandAll 0 zero_mem_I) y₁.val hy₁ y₂.val hy₂ hyle
    have hslope := E.clip_lowerSlope hW1.1 _ (E.F_mem _ _ hy₁ zero_mem_I)
      _ (E.F_mem _ _ hy₂ zero_mem_I) (E.F_mono_x 0 hyle)
    have hU := E.hUS_stateSlope 0 zero_mem_I 0 zero_mem_I y₁.val hy₁ y₂.val hy₂ hyle
    have h1 : 0 ≤ E.β_S * E.gS := mul_nonneg hβ E.gS_pos.le
    have hgSy : E.wlo * (y₂.val - y₁.val)
        = E.gS * (y₂.val - y₁.val) - E.β_S * E.gS * (E.glo * (y₂.val - y₁.val)) := by
      rw [← E.gS_mul]; ring
    change E.gS * (y₂.val - y₁.val)
      ≤ (E.U_S y₂.val 0 0 + E.β_S * W (Sanctions.clipS' (E.F y₂.val 0)))
        - (E.U_S y₁.val 0 0 + E.β_S * W (Sanctions.clipS' (E.F y₁.val 0)))
    nlinarith [mul_le_mul_of_nonneg_left hband.1 h1, mul_le_mul_of_nonneg_left hslope hβ, hU,
      hgSy]
  · -- Semiconcave leg.
    have hj := E.senderObj_jointSemiconcave hW1
    have hmodle := E.chSig_le_SigV
    intro z₁ hz₁ z₂ hz₂ t ht0 ht1
    have hm := mem_Icc_convexComb hz₁ hz₂ ht0 ht1
    have h := hj z₁ hz₁ z₂ hz₂ 0 zero_mem_I 0 zero_mem_I t ht0 ht1
    have hmid : t * (0:ℝ) + (1 - t) * 0 = 0 := by ring
    have hR : t * (1 - t) / 2
        * (chSig E.β_S E.σx E.SigV E.ghi E.KS E.Mx * (z₁ - z₂) ^ 2
          + 2 * plRho E.β_S E.rhi E.SigV E.ghi E.dhi E.KS E.Mm * |z₁ - z₂| * |(0:ℝ) - 0|
          - plMu E.β_S E.q E.SigV E.dhi E.KS E.Ms * ((0:ℝ) - 0) ^ 2)
        = chSig E.β_S E.σx E.SigV E.ghi E.KS E.Mx / 2 * (t * (1 - t) * (z₁ - z₂) ^ 2) := by
      simp only [sub_self, abs_zero, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, sub_zero]
      ring
    rw [hmid, hR] at h
    have hT : 0 ≤ t * (1 - t) * (z₁ - z₂) ^ 2 :=
      mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
    have hmod := mul_le_mul_of_nonneg_right hmodle hT
    simp only [relaxOp_apply, Sanctions.clipS'_val_eq_of_mem hz₁,
      Sanctions.clipS'_val_eq_of_mem hz₂, Sanctions.clipS'_val_eq_of_mem hm]
    linarith [h, hmod]
  · -- Semiconvex leg.
    have hcomp := semiconvexOnSet_comp_of_stateChord
      (v := fun z => W (Sanctions.clipS' z)) (G := fun y => E.F y 0)
      E.SigC_nonneg E.KS_nonneg E.hglo0 E.hMcx0
      (E.clip_monotoneOn hW.1.1) (E.clip_lip hW.1.1) hW.2
      (fun y hy => E.F_maps y hy 0 zero_mem_I) (E.hbandAll 0 zero_mem_I) (E.hFcx 0 zero_mem_I)
    have hsec := ((E.hUS_stateConvex 0 zero_mem_I).add (hcomp.const_mul E.hβS0.le)).mono
      E.SigC_closure
    intro z₁ hz₁ z₂ hz₂ t ht0 ht1
    have hm := mem_Icc_convexComb hz₁ hz₂ ht0 ht1
    have h := hsec z₁ hz₁ z₂ hz₂ t ht0 ht1
    simp only [relaxOp_apply, Sanctions.clipS'_val_eq_of_mem hz₁,
      Sanctions.clipS'_val_eq_of_mem hz₂, Sanctions.clipS'_val_eq_of_mem hm]
    exact h

/-- The relaxed operator restricted to the two-sided carrier. -/
def relaxOpSub : E.carrierS2 → E.carrierS2 :=
  fun W => ⟨E.relaxOp W.1, E.relaxOp_mem2 W.2⟩

theorem relaxOpSub_contracting : ContractingWith E.toParams.β_S_nnreal E.relaxOpSub := by
  refine ⟨E.toParams.β_S_nnreal_lt_one, ?_⟩
  intro V W
  have h := E.relaxOp_contracting.2 V.1 W.1
  simpa [relaxOpSub, Subtype.edist_eq] using h

instance carrierS2_completeSpace : CompleteSpace E.carrierS2 :=
  E.carrierS2_isClosed.completeSpace_coe

instance carrierS2_nonempty_inst : Nonempty E.carrierS2 :=
  E.carrierS2_nonempty.to_subtype

/-- **The Sender's value in the Sender-only reading**: the value of the
zero-sanction path, a Banach fixed point on the two-sided carrier. -/
def VS01 : Val :=
  (ContractingWith.fixedPoint E.relaxOpSub E.relaxOpSub_contracting).1

theorem VS01_mem2 : E.VS01 ∈ E.carrierS2 :=
  (ContractingWith.fixedPoint E.relaxOpSub E.relaxOpSub_contracting).2

theorem VS01_mem : E.VS01 ∈ E.carrierS := E.VS01_mem2.1

theorem VS01_fix : E.relaxOp E.VS01 = E.VS01 := by
  have h := ContractingWith.fixedPoint_isFixedPt E.relaxOpSub_contracting
  exact congrArg Subtype.val h

/-! ## 3. The response at that value -/

/-- Joint continuity of the response in (state, compliance). -/
theorem ρ01_continuousOn :
    ContinuousOn (fun xa : ℝ × ℝ => E.response E.VS01 xa.1 xa.2)
      ((Sanctions.S : Set ℝ) ×ˢ (Set.univ : Set ℝ)) :=
  E.toParams.σ_dyn_continuousOn_S_of_unique_on E.VS01
    (fun x hx a s₁ s₂ hs₁ hs₂ h₁ h₂ => E.DAU_on_carrier E.VS01_mem x hx a s₁ s₂ hs₁ hs₂ h₁ h₂)

theorem ρ01_continuous_a {x : ℝ} (hx : x ∈ Sanctions.I) :
    Continuous (fun a => E.response E.VS01 x a) := by
  have hmap : Set.MapsTo (fun a : ℝ => ((x, a) : ℝ × ℝ)) Set.univ
      ((Sanctions.S : Set ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    fun a _ => ⟨hx, Set.mem_univ _⟩
  have hc := E.ρ01_continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hc' : ContinuousOn (fun a => E.response E.VS01 x a) Set.univ :=
    hc.congr (fun a _ => rfl)
  exact continuousOn_univ.1 hc'

/-- The curvature ceiling of the Sender's objective in the sanction. -/
def Mtot : ℝ := E.Qbar + E.β_S * (E.SigC * E.dhi ^ 2 + E.KS * E.Mcs)

theorem Mtot_pos : 0 < E.Mtot := by
  unfold Mtot
  have h1 : 0 ≤ E.SigC * E.dhi ^ 2 := mul_nonneg E.SigC_nonneg (sq_nonneg _)
  have h2 : 0 ≤ E.KS * E.Mcs := mul_nonneg E.KS_nonneg E.hMcs0
  nlinarith [E.Qbar_pos, E.hβS0, h1, h2]

theorem Qbar_le_Mtot : E.Qbar ≤ E.Mtot := by
  unfold Mtot
  have h1 : 0 ≤ E.SigC * E.dhi ^ 2 := mul_nonneg E.SigC_nonneg (sq_nonneg _)
  have h2 : 0 ≤ E.KS * E.Mcs := mul_nonneg E.KS_nonneg E.hMcs0
  nlinarith [E.hβS0, h1, h2]

theorem q_le_Mtot : E.q ≤ E.Mtot := E.q_le_Qbar.trans E.Qbar_le_Mtot

/-- The sanction sections of `F` as a chord band `[d_lo, d_hi]`. -/
theorem sanctionBand {x : ℝ} (hx : x ∈ Sanctions.I) :
    StateChordBand (fun s => E.F x s) E.dlo E.dhi := by
  intro s₁ hs₁ s₂ hs₂ hle
  exact ⟨E.hSlo hx hs₁ hs₂ hle, E.hShi hx hs₁ hs₂ hle⟩

/-- **The Sender's objective is `M_tot`-semiconvex in the sanction**: the stage
is `Q̄`-semiconvex (S5), the continuation `σ_C·d_hi² + K_S·M_cs`-semiconvex. -/
theorem senderObj_semiconvex {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    SemiconvexOnSet (fun s => E.senderObj E.VS01 x a s) Sanctions.I E.Mtot := by
  have hcomp : SemiconvexOnSet (fun s => E.VS01 (Sanctions.clipS' (E.F x s))) Sanctions.I
      (E.SigC * E.dhi ^ 2 + E.KS * E.Mcs) :=
    semiconvexOnSet_comp_of_stateChord
      (v := fun z => E.VS01 (Sanctions.clipS' z)) (G := fun s => E.F x s)
      E.SigC_nonneg E.KS_nonneg E.hdlo0.le E.hMcs0
      (E.clip_monotoneOn E.VS01_mem.1) (E.clip_lip E.VS01_mem.1) E.VS01_mem2.2
      (fun s hs => E.F_maps x hx s hs) (E.sanctionBand hx) (E.hFcs x hx)
  exact (E.hUS_convex x hx a ha).add (hcomp.const_mul E.hβS0.le)

/-! ## 4. The zero level -/

/-- The response at the Sender-only value is zero at full compliance
(placability). -/
theorem ρ01_one (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.response E.VS01 x 1 = 0 :=
  E.response_at_one hP E.VS01_mem hx

/-- The compliance levels at which the response vanishes. -/
def zeroSet (x : ℝ) : Set ℝ :=
  Sanctions.ZeroLevel.zeroSet (fun x a => E.response E.VS01 x a) x

/-- **The zero level** `a*(x)`: the least compliance at which the response
vanishes (`Foundations/ZeroLevel`). -/
def zeroLevel (x : ℝ) : ℝ := Sanctions.ZeroLevel.level (fun x a => E.response E.VS01 x a) x

theorem zeroLevel_eq_sInf (x : ℝ) : E.zeroLevel x = sInf (E.zeroSet x) := rfl

theorem zeroSet_bddBelow (x : ℝ) : BddBelow (E.zeroSet x) :=
  Sanctions.ZeroLevel.zeroSet_bddBelow x

theorem one_mem_zeroSet (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) :
    (1 : ℝ) ∈ E.zeroSet x :=
  ⟨⟨zero_le_one, le_rfl⟩, E.ρ01_one hP hx⟩

theorem zeroLevel_mem (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.zeroLevel x ∈ Sanctions.I :=
  Sanctions.ZeroLevel.level_mem (ρ := fun x a => E.response E.VS01 x a)
    (E.ρ01_continuous_a hx).continuousOn (E.ρ01_one hP hx)

theorem ρ01_zeroLevel (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.response E.VS01 x (E.zeroLevel x) = 0 :=
  Sanctions.ZeroLevel.rho_level (ρ := fun x a => E.response E.VS01 x a)
    (E.ρ01_continuous_a hx).continuousOn (E.ρ01_one hP hx)

theorem ρ01_pos_of_lt (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < E.zeroLevel x) : 0 < E.response E.VS01 x a :=
  Sanctions.ZeroLevel.rho_pos_of_lt (ρ := fun x a => E.response E.VS01 x a)
    (E.response_mem E.VS01 x a).1 ha0 (ha.le.trans (E.zeroLevel_mem hP hx).2) ha

theorem ρ01_eq_zero_of_ge (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : E.zeroLevel x ≤ a) (ha1 : a ≤ 1) : E.response E.VS01 x a = 0 :=
  Sanctions.ZeroLevel.rho_eq_zero_of_ge (ρ := fun x a => E.response E.VS01 x a)
    (E.ρ01_continuous_a hx).continuousOn (E.ρ01_one hP hx)
    (E.response_antitoneOn_a E.VS01_mem hx) ha ha1

/-- **The forward-looking Sender is still sanctioning at the myopic
placation level**: at `a⁰⁰(x)` the stage is flat at zero up to the curvature
ceiling, `U_S(x, a⁰⁰, ε) − U_S(x, a⁰⁰, 0) ≥ −(Q̄/2)ε²`, but the continuation
wedge `β_S·g_S·d_lo·ε` makes a small positive sanction strictly better. -/
theorem ρ01_pos_at_myopicPolicy (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) :
    0 < E.response E.VS01 x (E.myopicPolicy x) := by
  set a := E.myopicPolicy x with ha
  have hQ := E.Qbar_pos
  set ε := min (1 : ℝ) (E.β_S * E.gS * E.dlo / E.Qbar) with hε
  have hgain : 0 < E.β_S * E.gS * E.dlo := mul_pos (mul_pos E.hβS0 E.gS_pos) E.hdlo0
  have hε0 : 0 < ε := lt_min one_pos (div_pos hgain hQ)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεq : E.Qbar * ε ≤ E.β_S * E.gS * E.dlo := by
    have := min_le_right (1 : ℝ) (E.β_S * E.gS * E.dlo / E.Qbar)
    calc E.Qbar * ε ≤ E.Qbar * (E.β_S * E.gS * E.dlo / E.Qbar) :=
          mul_le_mul_of_nonneg_left this hQ.le
      _ = E.β_S * E.gS * E.dlo := by
          rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ hQ.ne'
  have hεI : ε ∈ Sanctions.I := ⟨hε0.le, hε1⟩
  -- the objective at ε beats the objective at 0
  have hbetter : E.senderObj E.VS01 x a 0 < E.senderObj E.VS01 x a ε := by
    have hstage : -(E.Qbar / 2 * ε ^ 2) ≤ E.U_S x a ε - E.U_S x a 0 := by
      have h := E.stage_flat_at_zeroLevel00 E.placationCeiling (E.uhi_lt_k hP) hx hεI
      rw [ha, E.myopicPolicy_eq hx]
      exact h
    have hF0 : E.F x 0 ∈ Icc (0:ℝ) 1 := E.F_mem _ _ hx zero_mem_I
    have hFε : E.F x ε ∈ Icc (0:ℝ) 1 := E.F_mem _ _ hx hεI
    have hchord : E.dlo * ε ≤ E.F x ε - E.F x 0 := by
      have := E.hSlo hx zero_mem_I hεI hε0.le
      simpa using this
    have hFle : E.F x 0 ≤ E.F x ε := E.F_mono_s x hε0.le
    have hslope := E.clip_lowerSlope E.VS01_mem.1 _ hF0 _ hFε hFle
    have hgain' : E.β_S * E.gS * (E.dlo * ε)
        ≤ E.β_S * (E.VS01 (Sanctions.clipS' (E.F x ε))
          - E.VS01 (Sanctions.clipS' (E.F x 0))) := by
      have h1 := mul_le_mul_of_nonneg_left hchord E.gS_pos.le
      have h2 := mul_le_mul_of_nonneg_left (h1.trans hslope) E.hβS0.le
      linarith [h2]
    have hkey : E.Qbar / 2 * ε ^ 2 < E.β_S * E.gS * (E.dlo * ε) := by
      nlinarith [mul_le_mul_of_nonneg_left hεq hε0.le, hgain, hε0]
    unfold senderObj
    linarith [hstage, hgain', hkey]
  by_contra hne
  have h0 : E.response E.VS01 x a = 0 :=
    le_antisymm (le_of_not_gt hne) (E.response_mem E.VS01 x a).1
  have hmax := E.response_isMaxOn E.VS01 x a hεI
  simp only at hmax
  rw [h0] at hmax
  exact absurd hmax (not_le.mpr hbetter)

/-- **The zero level lies strictly above the myopic placation level.** -/
theorem myopicPolicy_lt_zeroLevel (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.myopicPolicy x < E.zeroLevel x := by
  by_contra hcon
  have hle : E.zeroLevel x ≤ E.myopicPolicy x := le_of_not_gt hcon
  have h := (E.ρ01_eq_zero_of_ge hP) hx hle ((E.myopicPolicy_lt_one (E.uhi_lt_k hP)) hx).le
  exact absurd h (E.ρ01_pos_at_myopicPolicy hP hx).ne'

theorem zeroLevel_pos (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) : 0 < E.zeroLevel x :=
  lt_trans (E.myopicPolicy_pos (E.uhi_lt_k hP) hx) ((E.myopicPolicy_lt_zeroLevel hP) hx)

/-! ### The sharp relief rate (round I, doc 75 R1)

Read as a quadratic lower support at the interior maximiser
(`Foundations/SemiconvexArgmaxShift`, sharp tilt form), the sanction
semiconvexity gives the rate `k_lo·Δa/M_tot` between any two compliance levels
strictly below the zero level, where both responses are interior; a one-sided
limit (`Foundations/ZeroLevel`) then bounds the response by
`k_lo(a* − a)/M_tot`. -/

/-- **Sharp relief rate.** Between two compliance levels strictly below the zero
level, extra compliance lowers the sanction by at least `k_lo·Δa/M_tot`. -/
theorem ρ01_shift_ge_linear (hInt : E.Interior) (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) {a
    a' : ℝ}
    (ha : 0 ≤ a) (haa' : a < a') (ha' : a' < E.zeroLevel x) :
    E.klo * (a' - a) / E.Mtot ≤ E.response E.VS01 x a - E.response E.VS01 x a' := by
  have hz1 := (E.zeroLevel_mem hP hx).2
  have haI : a ∈ Sanctions.I := ⟨ha, by linarith⟩
  have ha'I : a' ∈ Sanctions.I := ⟨by linarith, by linarith⟩
  have hint := E.ρ01_pos_of_lt hP hx ha'I.1 ha'
  exact Sanctions.SemiconvexArgmaxShift.argmax_shift_ge_tilt_of_semiconvex_interior
    E.Mtot_pos (E.senderObj_semiconvex hx ha'I) (E.senderObj_semiconvex hx haI) hint
    (E.response_lt_one hInt E.VS01_mem hx ha'I) (E.response_isMaxOn _ x a')
    (mul_pos E.hklo (by linarith)) (E.response_mem _ x a)
    (E.response_lt_one hInt E.VS01_mem hx haI) (E.response_isMaxOn _ x a)
    (fun u₁ hu₁ u₂ hu₂ hu => by
      have hdd := E.hUS_placLo x hx a haI a' ha'I u₁ hu₁ u₂ hu₂ haa'.le hu
      simp only [senderObj]
      nlinarith [hdd])

/-- **The response below the zero level is bounded below linearly:**
`ρ(a) ≥ k_lo(a* − a)/M_tot`. A one-sided limit of the sharp rate; no continuity
of the response is used. -/
theorem ρ01_ge_of_lt_sharp (hInt : E.Interior) (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) {a
    : ℝ}
    (ha0 : 0 ≤ a) (ha : a < E.zeroLevel x) :
    E.klo * (E.zeroLevel x - a) / E.Mtot ≤ E.response E.VS01 x a := by
  have h : E.klo / E.Mtot * (E.zeroLevel x - a) ≤ E.response E.VS01 x a :=
    Sanctions.ZeroLevel.rho_ge_of_lt (ρ := fun x a => E.response E.VS01 x a)
      (div_pos E.hklo E.Mtot_pos)
      (fun a' h1 h2 => by
        have hs := E.ρ01_shift_ge_linear hInt hP hx ha0 h1 h2
        have heq : E.klo / E.Mtot * (a' - a) = E.klo * (a' - a) / E.Mtot := by ring
        show E.klo / E.Mtot * (a' - a) ≤ E.response E.VS01 x a - E.response E.VS01 x a'
        linarith)
      (fun a' _ _ => (E.response_mem E.VS01 x a').1) ha
  have heq : E.klo / E.Mtot * (E.zeroLevel x - a) = E.klo * (E.zeroLevel x - a) / E.Mtot := by
    ring
  linarith

/-- The two-branch relief margin implies the sharp one. -/
theorem reliefSharp_of_relief (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) :
    E.ℓhi * E.Mtot < E.klo * E.plo := by
  have h1 : E.Mtot ≤ max E.Mtot E.klo := le_max_left _ _
  have h2 : 0 ≤ E.ℓhi * E.Mtot := mul_nonneg E.ℓhi_pos.le E.Mtot_pos.le
  nlinarith [mul_le_mul_of_nonneg_left h1 E.ℓhi_pos.le]

/-- **The sharp relief margin implies the stage relief margin** (renovation item BG3.2,
2026-10-06). The Sender's stage curvature is at most its whole dynamic curvature,
`Q̄ ≤ M_tot` (`Qbar_le_Mtot`), and `ℓ_hi > 0`, so
`ℓ_hi·Q̄ ≤ ℓ_hi·M_tot < k_lo·p_lo`. In words: if a unit of compliance buys enough sanction
relief to be worth its cost against the curvature `M_tot` of the forward-looking Sender, it
does so against the smaller stage curvature `Q̄` of the myopic one. So the myopic reading's
margin `StageRelief` is never a separate condition beside the sharp relief margin. General
in `F`: it compares constants of the class. -/
theorem stageRelief_of_reliefSharp (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) :
    E.StageRelief :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_left E.Qbar_le_Mtot E.ℓhi_pos.le) hrelief

/-- **A larger discharger of the sharp relief margin** (round J, doc 77 K4): when
the sanction floor times the curvature ceiling is at most the placation rate,
`b·M_tot ≤ k_lo`, the sharp relief margin follows from the stage flip
`ℓ_hi < b·p_lo` alone: `ℓ_hi·M_tot < b·p_lo·M_tot ≤ k_lo·p_lo`. A sufficient
condition, not an implication of curvature and closure: a loose sanction-section
modulus raises `M_tot` without changing the game. -/
theorem reliefSharp_of_scaled_Mtot_le (hflip : E.ℓhi < E.sfloor * E.plo)
    (h : E.sfloor * E.Mtot ≤ E.klo) :
    E.ℓhi * E.Mtot < E.klo * E.plo := by
  have hM := E.Mtot_pos
  have hp := E.hplo
  have h1 : E.ℓhi * E.Mtot < E.sfloor * E.plo * E.Mtot := mul_lt_mul_of_pos_right hflip hM
  have h2 : E.sfloor * E.Mtot * E.plo ≤ E.klo * E.plo := mul_le_mul_of_nonneg_right h hp.le
  nlinarith [h1, h2]

/-- **Where the continuation adds no sanction curvature and the stage curvature
is exact** (`M_tot = q`: the affine law and every member with `σ_C = 0`,
`M_cs = 0`, `Q̄ = q`), the sharp relief margin is a consequence of the stage
flip and placability: the floor is at most the cap `A/q`, so `b·q ≤ A ≤ k_lo`. -/
theorem reliefSharp_of_Mtot_eq_q (hP : E.Placable) (hflip : E.ℓhi < E.sfloor * E.plo)
    (hMq : E.Mtot = E.q) :
    E.ℓhi * E.Mtot < E.klo * E.plo := by
  apply E.reliefSharp_of_scaled_Mtot_le hflip
  rw [hMq]
  have hcap := E.sfloor_le_cap
  have hq := E.hq
  have hA : E.cap * E.q = E.A := by unfold cap; field_simp
  have hAk : E.A ≤ E.klo := E.A_le_k hP
  nlinarith [mul_le_mul_of_nonneg_right hcap hq.le]

/-! ## 5. The myopic Target against the forward-looking Sender -/

/-- The Target's stage objective against the response. -/
def tObj01 (x a : ℝ) : ℝ := E.toParams.U_T x a (E.response E.VS01 x a)

/-- Below the zero level, more compliance is worth it (sharp form): the relief
`k_lo(a* − a)/M_tot` at pain rate at least `p_lo` exceeds the cost, at most
`ℓ_hi(a* − a)`, under the sharp relief margin `ℓ_hi·M_tot < k_lo·p_lo`. -/
theorem tObj01_lt_of_lt' (hInt : E.Interior) (hP : E.Placable)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < E.zeroLevel x) :
    E.tObj01 x a < E.tObj01 x (E.zeroLevel x) := by
  unfold tObj01
  rw [(E.ρ01_zeroLevel hP) hx]
  have hzI := E.zeroLevel_mem hP hx
  have haI : a ∈ Sanctions.I := ⟨ha0, by linarith [hzI.2]⟩
  have hρm := E.response_mem E.VS01 x a
  have hstage := E.UT_sub_ge hx haI hzI hρm zero_mem_I ha.le hρm.1
  have hρ := (E.ρ01_ge_of_lt_sharp hInt hP) hx ha0 ha
  have hM := E.Mtot_pos
  have hgap : 0 < E.zeroLevel x - a := by linarith
  have h1 : E.klo * (E.zeroLevel x - a) / E.Mtot * E.plo
      ≤ E.response E.VS01 x a * E.plo := mul_le_mul_of_nonneg_right hρ E.hplo.le
  have h2 : E.ℓhi * (E.zeroLevel x - a) < E.klo * (E.zeroLevel x - a) / E.Mtot * E.plo := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hM]
    have := mul_lt_mul_of_pos_right hrelief hgap
    nlinarith [this]
  have hkey : E.ℓhi * (E.zeroLevel x - a) < E.plo * (E.response E.VS01 x a - 0) := by
    nlinarith [h1, h2]
  linarith

/-- Below the zero level, more compliance is worth it, under the two-branch
relief margin: a corollary of the sharp form through `reliefSharp_of_relief`. -/
theorem tObj01_lt_of_lt (hInt : E.Interior) (hP : E.Placable)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < E.zeroLevel x) :
    E.tObj01 x a < E.tObj01 x (E.zeroLevel x) :=
  (E.tObj01_lt_of_lt' hInt hP) (E.reliefSharp_of_relief hrelief) hx ha0 ha

/-- Above the zero level, compliance buys nothing and costs at least `ℓ_lo` per
unit. -/
theorem tObj01_lt_of_gt (hP : E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : E.zeroLevel x < a) (ha1 : a ≤ 1) : E.tObj01 x a < E.tObj01 x (E.zeroLevel x) := by
  unfold tObj01
  rw [(E.ρ01_zeroLevel hP) hx, (E.ρ01_eq_zero_of_ge hP) hx ha.le ha1]
  have hzI := E.zeroLevel_mem hP hx
  have haI : a ∈ Sanctions.I := ⟨by linarith [hzI.1], ha1⟩
  have h := E.hUT_costLo x hx 0 zero_mem_I (E.zeroLevel x) hzI a haI ha.le
  have := mul_pos E.hℓlo (by linarith : (0:ℝ) < a - E.zeroLevel x)
  linarith

theorem zeroLevel_isMaxOn' (hInt : E.Interior) (hP : E.Placable) (hrelief : E.ℓhi * E.Mtot < E.klo
    * E.plo)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => E.tObj01 x a) Sanctions.I (E.zeroLevel x) := by
  rw [isMaxOn_iff]
  intro a ha
  rcases lt_trichotomy a (E.zeroLevel x) with h | h | h
  · exact ((E.tObj01_lt_of_lt' hInt hP) hrelief hx ha.1 h).le
  · rw [h]
  · exact ((E.tObj01_lt_of_gt hP) hx h ha.2).le

theorem zeroLevel_isMaxOn (hInt : E.Interior) (hP : E.Placable)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => E.tObj01 x a) Sanctions.I (E.zeroLevel x) :=
  (E.zeroLevel_isMaxOn' hInt hP) (E.reliefSharp_of_relief hrelief) hx

theorem zeroLevel_argmax_unique' (hInt : E.Interior) (hP : E.Placable) (hrelief : E.ℓhi * E.Mtot <
    E.klo * E.plo)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.tObj01 x b) Sanctions.I a) : a = E.zeroLevel x := by
  rcases lt_trichotomy a (E.zeroLevel x) with h | h | h
  · exfalso
    have h1 := (E.tObj01_lt_of_lt' hInt hP) hrelief hx ha.1 h
    have h2 := hmax ((E.zeroLevel_mem hP) hx)
    exact absurd h2 (not_le.mpr h1)
  · exact h
  · exfalso
    have h1 := (E.tObj01_lt_of_gt hP) hx h ha.2
    have h2 := hmax ((E.zeroLevel_mem hP) hx)
    exact absurd h2 (not_le.mpr h1)

theorem zeroLevel_argmax_unique (hInt : E.Interior) (hP : E.Placable)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.tObj01 x b) Sanctions.I a) : a = E.zeroLevel x :=
  (E.zeroLevel_argmax_unique' hInt hP) (E.reliefSharp_of_relief hrelief) hx ha hmax

/-! ## 6. Continuity of the zero level -/

/-- **The zero level is continuous in the state** (`Foundations/ZeroLevel`, with
the sharp relief rate `k_lo/M_tot`). -/
theorem zeroLevel_continuousOn (hInt : E.Interior) (hP : E.Placable) : ContinuousOn E.zeroLevel
    Sanctions.I :=
  Sanctions.ZeroLevel.level_continuousOn (ρ := fun x a => E.response E.VS01 x a)
    (c := E.klo / E.Mtot) (div_pos E.hklo E.Mtot_pos)
    (E.ρ01_continuousOn.mono (Set.prod_mono subset_rfl (Set.subset_univ _)))
    (fun _ hx => E.ρ01_one hP hx)
    (fun _ hx => E.response_antitoneOn_a E.VS01_mem hx)
    (fun x hx a ha h => by
      have h' := E.ρ01_ge_of_lt_sharp hInt hP hx ha.1 h
      have heq : E.klo / E.Mtot * (E.zeroLevel x - a)
          = E.klo * (E.zeroLevel x - a) / E.Mtot := by ring
      show E.klo / E.Mtot * (E.zeroLevel x - a) ≤ E.response E.VS01 x a
      linarith)

/-- The Target policy of the reading, defined on all of `ℝ` through the clip. -/
def α01 (x : ℝ) : ℝ := E.zeroLevel (Sanctions.clipS x)

theorem α01_eq {x : ℝ} (hx : x ∈ Sanctions.I) : E.α01 x = E.zeroLevel x := by
  unfold α01
  rw [Sanctions.TransitionExtension.clipS_of_mem hx]

theorem α01_continuous (hInt : E.Interior) (hP : E.Placable) : Continuous E.α01 :=
  (E.zeroLevel_continuousOn hInt hP).comp_continuous Sanctions.clipS_continuous
    (fun x => Sanctions.clipS_mem x)

theorem α01_mem (hP : E.Placable) (x : ℝ) : E.α01 x ∈ Sanctions.I :=
  (E.zeroLevel_mem hP) (Sanctions.clipS_mem x)

/-! ## 7. The Target's value and the equilibrium -/

/-- **The myopic Target's value against the forward-looking Sender**: its stage
payoff at the zero level and zero sanction, `U_T(x, a*(x), 0)`. -/
def VT01 (hInt : E.Interior) (hP : E.Placable) : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) => E.toParams.U_T y.val (E.zeroLevel y.val) 0, by
      have hz : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.zeroLevel y.val) :=
        continuousOn_iff_continuous_restrict.mp (E.zeroLevel_continuousOn hInt hP)
      exact E.toParams.U_T_continuous.comp
        (continuous_subtype_val.prodMk (hz.prodMk continuous_const))⟩

theorem VT01_apply (hInt : E.Interior) (hP : E.Placable) (y : ↥(Sanctions.S : Set ℝ)) :
    (E.VT01 hInt hP) y = E.toParams.U_T y.val (E.zeroLevel y.val) 0 := rfl

theorem pS_integrandS (V : Val) (y s : ℝ) :
    E.pS.integrandS E.α01 (fun z => V z) (y, s) = E.senderObj V y (E.α01 y) s := rfl

theorem pS_joint_T_top_integrand (V_T V_S : Val) (y a : ℝ) :
    E.pS.joint_T_top_integrand V_T V_S y a
      = E.toParams.U_T y a (E.toParams.σ_dyn_top V_S y a) := by
  simp only [AbstractGame.Params.joint_T_top_integrand, E.pS_σ_dyn_top]
  simp [AbstractGame.Params.profileβ_T, ContinuationProfile.p01]

theorem pS_joint_eq_tObj01 (V_T : Val) {y : ℝ} (hy : y ∈ Sanctions.I) (a : ℝ) :
    E.pS.joint_T_top_integrand V_T E.VS01 y a = E.tObj01 y a := by
  rw [E.pS_joint_T_top_integrand, tObj01, E.response_eq_top E.VS01_mem hy]

/-- **The Sender-only equilibrium of a chord economy**: a top-selector feedback
Stackelberg equilibrium at the `01` view. The Sender's value is the
zero-sanction value, the Target's is `U_T(x, a*(x), 0)`, the policy is the zero
level, derived as the unique argmax given the sharp relief margin
`ℓ_hi·M_tot < k_lo·p_lo`. Zero-sanction neutrality `hN` is what makes the
zero-sanction value the Sender's Bellman value at the zero level. Rule 15:
constructed. -/
def senderOnlyEquilibriumTop' (hInt : E.Interior) (hP : E.Placable) (hrelief : E.ℓhi * E.Mtot <
    E.klo * E.plo)
    (hN : E.ZeroSanctionNeutral) :
    E.toParams.RegimeEquilibrium ContinuationProfile.p01 where
  V_T := (E.VT01 hInt hP)
  V_S := E.VS01
  α := E.α01
  hα := (E.α01_continuous hInt hP)
  α_mem := fun x _ => (E.α01_mem hP) x
  V_S_fix := by
    ext y
    change E.VS01 y = sSup ((fun s => E.pS.integrandS E.α01 (fun z => E.VS01 z)
      (y.val, s)) '' Sanctions.I)
    have hα : E.α01 y.val = E.zeroLevel y.val := E.α01_eq y.property
    have hgt : IsGreatest ((fun s => E.pS.integrandS E.α01 (fun z => E.VS01 z)
        (y.val, s)) '' Sanctions.I)
        (E.senderObj E.VS01 y.val (E.α01 y.val) (E.response E.VS01 y.val (E.α01 y.val))) := by
      refine ⟨⟨_, E.response_mem E.VS01 y.val (E.α01 y.val), E.pS_integrandS _ _ _⟩, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [E.pS_integrandS]
      exact E.response_isMaxOn E.VS01 y.val (E.α01 y.val) hs
    rw [hgt.csSup_eq, hα, (E.ρ01_zeroLevel hP) y.property]
    have h := congrArg (fun V : Val => V y) E.VS01_fix
    simp only at h
    rw [relaxOp_apply] at h
    unfold senderObj
    rw [hN y.val y.property (E.zeroLevel y.val) ((E.zeroLevel_mem hP) y.property)]
    exact h.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => E.pS.joint_T_top_integrand (E.VT01 hInt hP) E.VS01 y.val a)
        '' Sanctions.I)
        (E.pS.joint_T_top_integrand (E.VT01 hInt hP) E.VS01 y.val (E.zeroLevel y.val)) := by
      refine ⟨⟨_, (E.zeroLevel_mem hP) y.property, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      dsimp only
      rw [E.pS_joint_eq_tObj01 _ y.property, E.pS_joint_eq_tObj01 _ y.property]
      exact (E.zeroLevel_isMaxOn' hInt hP) hrelief y.property ha
    rw [hgt.csSup_eq, E.pS_joint_eq_tObj01 _ y.property, tObj01,
      (E.ρ01_zeroLevel hP) y.property, VT01_apply]
  α_opt_top := by
    intro x hx
    rw [isMaxOn_iff]
    intro a ha
    rw [E.pS_joint_eq_tObj01 _ hx, E.pS_joint_eq_tObj01 _ hx, E.α01_eq hx]
    exact (E.zeroLevel_isMaxOn' hInt hP) hrelief hx ha

/-- **The Sender-only equilibrium under the two-branch relief margin**: the same
construction, through `reliefSharp_of_relief`. -/
def senderOnlyEquilibriumTop (hInt : E.Interior) (hP : E.Placable)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    E.toParams.RegimeEquilibrium ContinuationProfile.p01 :=
  (E.senderOnlyEquilibriumTop' hInt hP) (E.reliefSharp_of_relief hrelief) hN

/-- **Uniqueness of the zero level at the constructed equilibrium** (sharp margin). -/
theorem senderOnlyEquilibriumTop_argmax_unique' (hInt : E.Interior) (hP : E.Placable)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.pS.joint_T_top_integrand
      ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN).V_T
      ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN).V_S x b) Sanctions.I a) :
    a = ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN).α x := by
  change a = E.α01 x
  rw [E.α01_eq hx]
  apply (E.zeroLevel_argmax_unique' hInt hP) hrelief hx ha
  intro b hb
  have := hmax hb
  simp only [Set.mem_setOf_eq] at this ⊢
  change E.pS.joint_T_top_integrand (E.VT01 hInt hP) E.VS01 x b
    ≤ E.pS.joint_T_top_integrand (E.VT01 hInt hP) E.VS01 x a at this
  rwa [E.pS_joint_eq_tObj01 _ hx, E.pS_joint_eq_tObj01 _ hx] at this

/-- **Uniqueness of the zero level at the constructed equilibrium.** -/
theorem senderOnlyEquilibriumTop_argmax_unique (hInt : E.Interior) (hP : E.Placable)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.pS.joint_T_top_integrand
      ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).V_T
      ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).V_S x b) Sanctions.I a) :
    a = ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).α x :=
  (E.senderOnlyEquilibriumTop_argmax_unique' hInt hP) (E.reliefSharp_of_relief hrelief) hN hx ha
      hmax

/-- **The realised sanction is zero** (sharp margin). -/
theorem senderOnlyRule_eq_zero' (hInt : E.Interior) (hP : E.Placable) (hrelief : E.ℓhi * E.Mtot <
    E.klo * E.plo)
    (hN : E.ZeroSanctionNeutral) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN) x = 0 := by
  change E.pS.σ_dyn_top E.VS01 x (E.α01 x) = 0
  rw [E.pS_σ_dyn_top, ← E.response_eq_top E.VS01_mem hx, E.α01_eq hx]
  exact (E.ρ01_zeroLevel hP) hx

/-- **The realised sanction is zero.** -/
theorem senderOnlyRule_eq_zero (hInt : E.Interior) (hP : E.Placable)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN) x = 0 :=
  (E.senderOnlyRule_eq_zero' hInt hP) (E.reliefSharp_of_relief hrelief) hN hx

/-! ## 8. The path, the price, and the four cells -/

/-- The state path under the Sender-only equilibrium (sharp margin). -/
def senderOnlyPath' (hInt : E.Interior) (hP : E.Placable) (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo)
    (hN : E.ZeroSanctionNeutral) (x₀ : ℝ) (t : ℕ) : ℝ :=
  E.toParams.rulePathF
    (E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN)) x₀ t

/-- The state path under the Sender-only equilibrium. -/
def senderOnlyPath (hInt : E.Interior) (hP : E.Placable) (hrelief : 2 * E.ℓhi * max E.Mtot E.klo <
    E.klo * E.plo)
    (hN : E.ZeroSanctionNeutral) (x₀ : ℝ) (t : ℕ) : ℝ :=
  (E.senderOnlyPath' hInt hP) (E.reliefSharp_of_relief hrelief) hN x₀ t

theorem senderOnlyPath_le_geom' (hInt : E.Interior) (hP : E.Placable) (hrelief : E.ℓhi * E.Mtot <
    E.klo * E.plo)
    (hN : E.ZeroSanctionNeutral) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E.senderOnlyPath' hInt hP) hrelief hN x₀ t ≤ (1 - E.dlo) ^ t * x₀ :=
  E.toParams.rulePathF_le_geom_of_zero_rule E.hSlo
    (fun _ hx => (E.senderOnlyRule_eq_zero' hInt hP) hrelief hN hx) hx₀

theorem senderOnlyPath_le_geom (hInt : E.Interior) (hP : E.Placable)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E.senderOnlyPath hInt hP) hrelief hN x₀ t ≤ (1 - E.dlo) ^ t * x₀ :=
  (E.senderOnlyPath_le_geom' hInt hP) (E.reliefSharp_of_relief hrelief) hN hx₀

theorem senderOnlyPath_tendsto_zero' (hInt : E.Interior) (hP : E.Placable)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Tendsto ((E.senderOnlyPath' hInt hP) hrelief hN x₀) atTop (𝓝 0) :=
  E.toParams.rulePathF_tendsto_zero_of_zero_rule E.hdlo0 E.hSlo
    (fun _ hx => (E.senderOnlyRule_eq_zero' hInt hP) hrelief hN hx) hx₀

theorem senderOnlyPath_tendsto_zero (hInt : E.Interior) (hP : E.Placable)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Tendsto ((E.senderOnlyPath hInt hP) hrelief hN x₀) atTop (𝓝 0) :=
  (E.senderOnlyPath_tendsto_zero' hInt hP) (E.reliefSharp_of_relief hrelief) hN hx₀

/-- **The Sender-only reading, general in `F` and in the payoffs, under the
sharp relief margin** `ℓ_hi·M_tot < k_lo·p_lo` and zero-sanction neutrality:
(i) the same primitives; (ii) the Target's unique optimum is the zero level,
strictly above the myopic placation level, and the realised sanction is zero;
(iii) the state washes out from every start. -/
theorem sender_only_regime_generalF' (hInt : E.Interior) (hP : E.Placable)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    (E.pS.U_T = E.toParams.U_T ∧ E.pS.U_S = E.toParams.U_S ∧ E.pS.F = E.toParams.F) ∧
    (∀ x ∈ Sanctions.I,
      E.myopicPolicy x < ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN).α x ∧
      ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN).α x ∈ Sanctions.I ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pS.joint_T_top_integrand
          ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN).V_T
          ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN).V_S x b) Sanctions.I a →
          a = ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN).α x) ∧
      E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN) x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, (E.senderOnlyPath' hInt hP) hrelief hN x₀ t ≤ (1 - E.dlo) ^ t * x₀) ∧
      Tendsto ((E.senderOnlyPath' hInt hP) hrelief hN x₀) atTop (𝓝 0)) := by
  refine ⟨⟨rfl, rfl, rfl⟩, fun x hx => ⟨?_, (E.α01_mem hP) x,
    fun _ ha hmax => (E.senderOnlyEquilibriumTop_argmax_unique' hInt hP) hrelief hN hx ha hmax,
    (E.senderOnlyRule_eq_zero' hInt hP) hrelief hN hx⟩,
    fun _ hx₀ => ⟨(E.senderOnlyPath_le_geom' hInt hP) hrelief hN hx₀,
      (E.senderOnlyPath_tendsto_zero' hInt hP) hrelief hN hx₀⟩⟩
  change E.myopicPolicy x < E.α01 x
  rw [E.α01_eq hx]
  exact (E.myopicPolicy_lt_zeroLevel hP) hx

/-- **The Sender-only reading, general in `F`** (the fourth cell), under the
two-branch relief margin: a corollary of `sender_only_regime_generalF'`. -/
theorem sender_only_regime_generalF (hInt : E.Interior) (hP : E.Placable)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    (E.pS.U_T = E.toParams.U_T ∧ E.pS.U_S = E.toParams.U_S ∧ E.pS.F = E.toParams.F) ∧
    (∀ x ∈ Sanctions.I,
      E.myopicPolicy x < ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).α x ∧
      ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).α x ∈ Sanctions.I ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pS.joint_T_top_integrand
          ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).V_T
          ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).V_S x b) Sanctions.I a →
          a = ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN).α x) ∧
      E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN) x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, (E.senderOnlyPath hInt hP) hrelief hN x₀ t ≤ (1 - E.dlo) ^ t * x₀) ∧
      Tendsto ((E.senderOnlyPath hInt hP) hrelief hN x₀) atTop (𝓝 0)) :=
  (E.sender_only_regime_generalF' hInt hP) (E.reliefSharp_of_relief hrelief) hN

/-- **The four cells, general in `F` and in the payoffs, under the sharp relief margin
and a nondecreasing response** (renovation item BH4.1, 2026-10-06). This is
`four_cell_generalF'` with the rally margin replaced by a response `responsePath VSstar`
that is nondecreasing on `[0, 1]`; the `11` cell is read at the constructed equilibrium
`equilibriumTop hTM hmono` and its path `dynamicPathOf hTM hmono`. Under the readings in
which the Target does not look ahead (`00`, `01`) the state washes out from every start;
under the readings in which it does (`10`, `11`) the state converges to a positive limit,
a fixed point `z₁₀` of the stage selector when the Sender is myopic and a strictly higher
one when it looks ahead. The rally margin entered only the `11` cell, and only to make
the response nondecreasing; the other cells never read it. -/
theorem four_cell_generalF'_of_response_monotone (hInt : E.Interior) (hTM : E.LossOffset)
    (hP : E.Placable) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    (∀ x₀ ∈ Sanctions.I, Tendsto
      ((E.myopicPath hInt (E.stageRelief_of_reliefSharp hrelief) hP) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((E.senderOnlyPath' hInt hP) hrelief hN x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ 0 < z₁₀ ∧ z₁₀ < z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto (E.dynamicPathOf hTM hmono x₀) atTop (𝓝 z)) := by
  refine ⟨fun _ hx₀ =>
      (E.myopicPath_tendsto_zero hInt (E.stageRelief_of_reliefSharp hrelief) hP) hx₀,
    fun _ hx₀ => (E.senderOnlyPath_tendsto_zero' hInt hP) hrelief hN hx₀, fun x₀ hx₀ => ?_⟩
  obtain ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, hlt, ht₁₀, ht⟩ :=
    E.targetOnly_limit_lt_dynamic_limit_of_response_monotone (E.uhi_lt_q hInt) hTM hmono hx₀
  have hpos : 0 < z₁₀ := by
    rw [← hfix₁₀]; exact E.stage_argmax_pos hz₁₀
  exact ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, hpos, hlt, ht₁₀, ht⟩

/-- **The four cells, general in `F` and in the payoffs, under the sharp relief
margin.** Under the readings in which the Target does not look ahead (`00`,
`01`) the state washes out from every start; under the readings in which it does
(`10`, `11`) the state converges to a positive limit — a fixed point `z₁₀` of
the stage selector when the Sender is myopic, and a strictly higher one when it
looks ahead. The Target channel produces entrenchment; the Sender channel
raises it.

The myopic cell's stage relief margin is not a hypothesis (renovation item BG3.2,
2026-10-06): the sharp relief margin `hrelief` implies it (`stageRelief_of_reliefSharp`),
so the binder `hSR` was dropped and the myopic path is read at that derived margin. The
rally-margin form of `four_cell_generalF'_of_response_monotone` (BH4.1). -/
theorem four_cell_generalF' (hInt : E.Interior) (hTM : E.LossOffset) (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    (∀ x₀ ∈ Sanctions.I, Tendsto
      ((E.myopicPath hInt (E.stageRelief_of_reliefSharp hrelief) hP) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((E.senderOnlyPath' hInt hP) hrelief hN x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ 0 < z₁₀ ∧ z₁₀ < z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z)) :=
  E.four_cell_generalF'_of_response_monotone hInt hTM hP
    (E.responsePath_monotoneOn_of_margin hmargin) hrelief hN

/-- **The four cells, general in `F`**, under the two-branch relief margin: a
corollary of `four_cell_generalF'`. A pinned headline, so its statement still carries the
stage relief margin `hSR`, although `four_cell_generalF'` no longer needs it (BG3.2). -/
theorem four_cell_generalF (hInt : E.Interior) (hSR : E.StageRelief) (hTM : E.LossOffset) (hP :
    E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    (∀ x₀ ∈ Sanctions.I, Tendsto ((E.myopicPath hInt hSR hP) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((E.senderOnlyPath hInt hP) hrelief hN x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ 0 < z₁₀ ∧ z₁₀ < z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z)) :=
  (E.four_cell_generalF' hInt hTM hP) hmargin (E.reliefSharp_of_relief hrelief) hN

/-- **The long-run difference in differences, under the sharp relief margin**
(doc 65, D4; sharp form round J, doc 77 K1). Writing `L⁰⁰, L⁰¹, L¹⁰, L¹¹` for
the four limits from a common start, `(L¹¹ − L¹⁰) − (L⁰¹ − L⁰⁰) = L¹¹ − L¹⁰ > 0`.
A restatement of `four_cell_generalF'` for the one outcome "long-run state": it
is not strategic supermodularity, it says nothing about other outcomes, and it
does not say either channel is necessary for entrenchment (`10` alone
entrenches). General in `F`. The stage relief margin is no longer a hypothesis
(BG3.2, 2026-10-06): it follows from `hrelief` (`stageRelief_of_reliefSharp`). -/
theorem four_cell_longrun_difference' (hInt : E.Interior) (hTM : E.LossOffset)
    (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    ∀ x₀ ∈ Sanctions.I, ∃ L00 L01 L10 L11 : ℝ,
      Tendsto ((E.myopicPath hInt (E.stageRelief_of_reliefSharp hrelief) hP) x₀) atTop
        (𝓝 L00) ∧
      Tendsto ((E.senderOnlyPath' hInt hP) hrelief hN x₀) atTop (𝓝 L01) ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 L10) ∧
      Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 L11) ∧
      0 < (L11 - L10) - (L01 - L00) := by
  intro x₀ hx₀
  obtain ⟨h00, h01, h1x⟩ := (E.four_cell_generalF' hInt hTM hP) hmargin hrelief hN
  obtain ⟨z₁₀, _, z, _, _, _, _, hlt, h10, h11⟩ := h1x x₀ hx₀
  exact ⟨0, 0, z₁₀, z, h00 x₀ hx₀, h01 x₀ hx₀, h10, h11, by linarith⟩

/-- **The long-run difference in differences** under the two-branch relief
margin: a corollary of `four_cell_longrun_difference'`. General in `F`. No stage relief
margin (BG3.2): the two-branch margin implies the sharp one, which implies it. -/
theorem four_cell_longrun_difference (hInt : E.Interior) (hTM : E.LossOffset)
    (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    ∀ x₀ ∈ Sanctions.I, ∃ L00 L01 L10 L11 : ℝ,
      Tendsto ((E.myopicPath hInt
        (E.stageRelief_of_reliefSharp (E.reliefSharp_of_relief hrelief)) hP) x₀) atTop
        (𝓝 L00) ∧
      Tendsto ((E.senderOnlyPath hInt hP) hrelief hN x₀) atTop (𝓝 L01) ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 L10) ∧
      Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 L11) ∧
      0 < (L11 - L10) - (L01 - L00) :=
  (E.four_cell_longrun_difference' hInt hTM hP) hmargin (E.reliefSharp_of_relief hrelief) hN

/-- **The common-state rule difference in differences, under the sharp relief
margin** (doc 70, L2; sharp form round J, doc 77 K1). At every feasible state,
writing `R⁰⁰, R⁰¹, R¹⁰, R¹¹` for the realised sanction rules of the four
constructed regime equilibria, `(R¹¹ − R¹⁰) − (R⁰¹ − R⁰⁰) > 0`. It follows from
the four rule identities — `R⁰⁰ = R⁰¹ = 0`, `R¹⁰ = σ(x, 0)` (the stage
selector), `R¹¹ > σ(x, 0)` — and nothing else. A common-state comparison of the
constructed rules: not strategic supermodularity, not a welfare ranking, and
not a statement that either channel is necessary for entrenchment. General in `F`. The
stage relief margin is no longer a hypothesis (BG3.2, 2026-10-06): it follows from
`hrelief` (`stageRelief_of_reliefSharp`). -/
theorem four_cell_rule_difference_at_state' (hInt : E.Interior) (hTM : E.LossOffset)
    (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    ∀ x ∈ Sanctions.I,
      0 < (E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x
            - E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x)
          - (E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN) x
            - E.pM.dynamicEquilibriumRule
              (E.myopicEquilibriumTop hInt (E.stageRelief_of_reliefSharp hrelief) hP) x) := by
  intro x hx
  rw [(E.dynamicRule_eq_responsePath hTM) hmargin hx, (E.targetOnlyRule_eq_stage hTM) hx,
    (E.senderOnlyRule_eq_zero' hInt hP) hrelief hN hx,
    (E.myopicRule_eq_zero hInt (E.stageRelief_of_reliefSharp hrelief) hP) hx]
  linarith [E.responsePath_gt_stage (E.uhi_lt_q hInt) E.VSstar_mem hx]

/-- **The common-state rule difference in differences** under the two-branch
relief margin: a corollary of `four_cell_rule_difference_at_state'`. General in `F`. No
stage relief margin (BG3.2): the two-branch margin implies the sharp one, which implies
it. -/
theorem four_cell_rule_difference_at_state (hInt : E.Interior) (hTM : E.LossOffset)
    (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : 2 * E.ℓhi * max E.Mtot E.klo < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    ∀ x ∈ Sanctions.I,
      0 < (E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x
            - E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x)
          - (E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop hInt hP) hrelief hN) x
            - E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTop hInt
              (E.stageRelief_of_reliefSharp (E.reliefSharp_of_relief hrelief)) hP) x) :=
  (E.four_cell_rule_difference_at_state' hInt hTM hP) hmargin (E.reliefSharp_of_relief hrelief)
      hN

/-- **The common-state rule chain across the four cells** (round L, doc 80 M10):
at every state, the realised sanction is zero in the two cells where the Target
looks ahead and complies (`00`, `01`), equals the positive stage selector
`σ(x, 0)` when only the Target looks ahead (`10`), and lies strictly above it and
strictly below one when both look ahead (`11`). The Sender's foresight raises
the sanction against a defiant forward-looking Target and, by
`myopicPolicy_lt_zeroLevel`, extracts more compliance from a myopic one — the
direction Eaton and Engers (1992) associate with a patient Sender, stated here
as a comparison of constructed equilibrium rules at a common state, not as their
toughness parameter. General in `F`. The stage relief margin is no longer a hypothesis
(BG3.2, 2026-10-06): it follows from `hrelief` (`stageRelief_of_reliefSharp`). The rally
margin only names the `11` equilibrium: the chain holds with the `11` cell read at any
full-defiance equilibrium and no rally margin (`four_cell_rule_chain_of_policy_zero`,
renovation item BH3.3, in `PlacableSenderDefianceEpisode.lean`). -/
theorem four_cell_rule_chain (hInt : E.Interior) (hTM : E.LossOffset) (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral) :
    ∀ x ∈ Sanctions.I,
      E.pM.dynamicEquilibriumRule
          (E.myopicEquilibriumTop hInt (E.stageRelief_of_reliefSharp hrelief) hP) x = 0 ∧
      E.pS.dynamicEquilibriumRule ((E.senderOnlyEquilibriumTop' hInt hP) hrelief hN) x = 0 ∧
      0 < E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x ∧
      E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x
        < E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x ∧
      E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x < 1 := by
  intro x hx
  refine ⟨(E.myopicRule_eq_zero hInt (E.stageRelief_of_reliefSharp hrelief) hP) hx,
      (E.senderOnlyRule_eq_zero' hInt hP) hrelief hN hx, ?_, ?_, ?_⟩
  · rw [(E.targetOnlyRule_eq_stage hTM) hx]
    exact E.stage_argmax_pos hx
  · rw [(E.dynamicRule_eq_responsePath hTM) hmargin hx, (E.targetOnlyRule_eq_stage hTM) hx]
    exact E.responsePath_gt_stage (E.uhi_lt_q hInt) E.VSstar_mem hx
  · rw [(E.dynamicRule_eq_responsePath hTM) hmargin hx]
    exact lt_of_le_of_lt (E.responsePath_le_cap E.VSstar_mem hx) (E.cap_lt_one hInt)

end ChordEconomyCs

/-- **The scaled discharger is maximal for the uniform implication** (round L,
doc 80 M11; the reader's document 03 §3). With `q, k, M, C > 0`, the stage
flip `ℓq < u₀C` implies the sharp relief margin `ℓM < kC` for *every* positive
compliance cost `ℓ` exactly when `u₀·M ≤ k·q`. No sign of `u₀` is needed: when
`u₀ ≤ 0` no positive cost passes the flip and `u₀M ≤ kq` holds, so both sides
are true. So `reliefSharp_of_scaled_Mtot_le` states the largest condition on the
other coefficients under which the flip alone discharges (RL) whatever the cost:
outside it, the midpoint of `(kC/M, u₀C/q)` is a cost that passes the flip and
fails relief. On a chord economy it applies with `u₀/q = b` the sanction floor,
`M = M_tot`, `k = k_lo` and `C = p_lo`. A relation between coefficient
certificates; it does not make (RL) necessary for accommodation. -/
theorem ChordEconomyCs.reliefSharp_uniform_iff {q u₀ k M C : ℝ} (hq : 0 < q) (hk : 0 < k)
    (hM : 0 < M) (hC : 0 < C) :
    (∀ ℓ : ℝ, 0 < ℓ → ℓ * q < u₀ * C → ℓ * M < k * C) ↔ u₀ * M ≤ k * q := by
  constructor
  · intro h
    by_contra hlt
    have hlt : k * q < u₀ * M := not_le.mp hlt
    have hX : k * C / M * M = k * C := div_mul_cancel₀ _ hM.ne'
    have hY : u₀ * C / q * q = u₀ * C := div_mul_cancel₀ _ hq.ne'
    -- `kq < u₀M` puts `kC/M` strictly below `u₀C/q`.
    have hA : k * C / M < u₀ * C / q := by
      by_contra hge
      have hge : u₀ * C / q ≤ k * C / M := not_lt.mp hge
      have := mul_le_mul_of_nonneg_right hge (mul_pos hM hq).le
      nlinarith [this, hX, hY, hlt, hC]
    set ℓ := (k * C / M + u₀ * C / q) / 2 with hℓ
    have hXℓ : k * C / M < ℓ := by rw [hℓ]; linarith
    have hℓY : ℓ < u₀ * C / q := by rw [hℓ]; linarith
    have hℓ0 : 0 < ℓ := lt_trans (by positivity) hXℓ
    have h1 : ℓ * q < u₀ * C := by
      have := mul_lt_mul_of_pos_right hℓY hq
      linarith
    have h2 : k * C < ℓ * M := by
      have := mul_lt_mul_of_pos_right hXℓ hM
      linarith
    exact absurd (h ℓ hℓ0 h1) (not_lt.mpr h2.le)
  · intro h ℓ hℓ hflip
    have h1 : ℓ * q * M < u₀ * C * M := mul_lt_mul_of_pos_right hflip hM
    have h2 : u₀ * M * C ≤ k * q * C := mul_le_mul_of_nonneg_right h hC.le
    nlinarith [h1, h2, hq]

/-! ## 9. The quadratic–linear family: the four cells in closed form (sign-off M6)

On the family the `10` limit is the unique fixed point `u₀/(q − r)` of the
vertex, so the four-cell theorem takes its original closed form. -/

namespace PlacableEconomyFcs

variable (E : PlacableEconomyFcs)

/-- **The four cells on the quadratic–linear family**, in closed form: wash-out
under `00` and `01`, convergence to `u₀/(q − r)` under `10` from every start, and
a strictly higher forward-looking limit under `11`. Renovation item BJ2.3 (2026-10-07):
the family's interiority is the hypothesis `hInt` (it was a field), and the myopic
cell's stage relief margin, also no longer a field, comes from the sharp relief margin
`hrelief` (`stageRelief_of_reliefSharp`, BG3.2), so no stage relief hypothesis is added.
General in the family's transition `F`. -/
theorem four_cell_closedForm (hInt : E.Interior) (hTM : E.LossOffset) (hP : E.Placable)
    (hmargin : E.βS * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.r)
    (hrelief : E.ℓ * E.toChordCs.Mtot < E.k * (E.c - E.n)) :
    (∀ x₀ ∈ Sanctions.I,
      Tendsto ((E.toChord.myopicPath (E.toChord_interior hInt)
          (E.toChordCs.stageRelief_of_reliefSharp hrelief) (E.toChord_placable hP)) x₀)
        atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I,
      Tendsto ((E.toChordCs.senderOnlyPath' (E.toChordCs_interior hInt) (E.toChord_placable hP)
        hrelief E.toChord_zeroSanctionNeutral) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I,
      Tendsto (E.toChord.targetOnlyPath (E.toChord_lossOffset (E.u₀_le_q hInt) hTM) x₀) atTop
        (𝓝 E.steady10)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.toChord.responsePath E.toChord.VSstar z = z ∧
      E.steady10 < z ∧
      Tendsto (E.toChord.dynamicPath (E.toChord_lossOffset (E.u₀_le_q hInt) hTM)
        (E.toChord_margin hmargin) x₀) atTop (𝓝 z)) ∧
    0 < E.steady10 :=
  ⟨fun _ hx₀ => E.toChord.myopicPath_tendsto_zero (E.toChord_interior hInt)
      (E.toChordCs.stageRelief_of_reliefSharp hrelief) _ hx₀,
   fun _ hx₀ => E.toChordCs.senderOnlyPath_tendsto_zero' (E.toChordCs_interior hInt) _ hrelief _
      hx₀,
   fun _ hx₀ => E.toPlacableEconomyF.targetOnlyPath_tendsto hInt hTM hx₀,
   fun _ hx₀ => E.toPlacableEconomyF.targetOnly_steady_lt_dynamic_steady hInt hTM hmargin hx₀,
   E.toPlacableEconomyF.steady10_pos hInt⟩

end PlacableEconomyFcs

/-! ## 10. The relief margin and the four cells at both witnesses -/

theorem placableAffine_Mtot : placableAffineCs.toChordCs.Mtot = 3 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineCs, placableAffine]

theorem placableQuadDiag_Mtot : placableQuadDiagCs.toChordCs.Mtot = 45 / 14 := by
  norm_num [ChordEconomyCs.Mtot, ChordEconomyTwoSided.SigC, chSigC, ChordEconomy.KS, chKS,
    PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagCs,
    placableQuadDiag]

/-- The two-branch relief margin at the affine member: `6 < 12`. -/
theorem placableAffine_relief :
    2 * placableAffineCs.toChordCs.ℓhi
        * max placableAffineCs.toChordCs.Mtot placableAffineCs.toChordCs.klo
      < placableAffineCs.toChordCs.klo * placableAffineCs.toChordCs.plo := by
  rw [placableAffine_Mtot]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableAffineCs,
    placableAffine]

/-- The two-branch relief margin at the non-affine member: `45/7 < 12`. -/
theorem placableQuadDiag_relief :
    2 * placableQuadDiagCs.toChordCs.ℓhi
        * max placableQuadDiagCs.toChordCs.Mtot placableQuadDiagCs.toChordCs.klo
      < placableQuadDiagCs.toChordCs.klo * placableQuadDiagCs.toChordCs.plo := by
  rw [placableQuadDiag_Mtot]
  norm_num [PlacableEconomyFcs.toChordCs, PlacableEconomyF.toChord, placableQuadDiagCs,
    placableQuadDiag]

/-- The affine member's rally margin in the family's own form, discharged by
flatness (`σ_C = 0`, `M_mix = 0`). -/
theorem placableAffine_familyMargin :
    placableAffine.βS * (placableAffine.SigC * placableAffine.ghi * placableAffine.dhi
      + (placableAffine.KS + 2 * placableAffine.SigC) * placableAffine.Mmix) ≤ placableAffine.r :=
          by
  have h := placableAffine.toChord.margin_of_flat rfl rfl rfl
  rw [PlacableEconomyF.toChord_SigC] at h
  exact h

/-- The non-affine member's rally margin in the family's own form. -/
theorem placableQuadDiag_familyMargin :
    placableQuadDiag.βS * (placableQuadDiag.SigC * placableQuadDiag.ghi * placableQuadDiag.dhi
      + (placableQuadDiag.KS + 2 * placableQuadDiag.SigC) * placableQuadDiag.Mmix)
      ≤ placableQuadDiag.r := by
  have h := placableQuadDiag.toChord.margin_of_flat rfl rfl rfl
  rw [PlacableEconomyF.toChord_SigC] at h
  exact h

/-- The four cells at the affine member (rally margin empty, relief margin
`3 < 12`), in closed form. -/
theorem placableAffine_four_cells :
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableAffine.toChord.myopicPath
        (placableAffine.toChord_interior placableAffine_interior)
        (placableAffine.toChord_stageRelief placableAffine_stageRelief)
      (placableAffine.toChord_placable placableAffine_placable)) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableAffineCs.toChordCs.senderOnlyPath'
        (placableAffineCs.toChordCs_interior placableAffine_interior)
      (placableAffine.toChord_placable placableAffine_placable)
      (placableAffineCs.toChordCs.reliefSharp_of_relief placableAffine_relief)
      placableAffine.toChord_zeroSanctionNeutral) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto (placableAffine.toChord.targetOnlyPath
      (placableAffine.toChord_lossOffset (placableAffine.u₀_le_q placableAffine_interior)
        placableAffine_margin) x₀) atTop
      (𝓝 placableAffine.steady10)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I,
      placableAffine.toChord.responsePath placableAffine.toChord.VSstar z = z ∧
      placableAffine.steady10 < z ∧
      Tendsto (placableAffine.toChord.dynamicPath
        (placableAffine.toChord_lossOffset (placableAffine.u₀_le_q placableAffine_interior)
          placableAffine_margin)
        (placableAffine.toChord_margin placableAffine_familyMargin) x₀)
        atTop (𝓝 z)) ∧
    0 < placableAffine.steady10 :=
  placableAffineCs.four_cell_closedForm placableAffine_interior placableAffine_margin
    placableAffine_placable placableAffine_familyMargin
    (placableAffineCs.toChordCs.reliefSharp_of_relief placableAffine_relief)

/-- The four cells at the non-affine member (rally margin empty, relief margin
`45/14 < 12`), in closed form. -/
theorem placableQuadDiag_four_cells :
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableQuadDiag.toChord.myopicPath
        (placableQuadDiag.toChord_interior placableQuadDiag_interior)
        (placableQuadDiag.toChord_stageRelief placableQuadDiag_stageRelief)
      (placableQuadDiag.toChord_placable placableQuadDiag_placable)) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((placableQuadDiagCs.toChordCs.senderOnlyPath'
        (placableQuadDiagCs.toChordCs_interior placableQuadDiag_interior)
      (placableQuadDiag.toChord_placable placableQuadDiag_placable)
      (placableQuadDiagCs.toChordCs.reliefSharp_of_relief placableQuadDiag_relief)
      placableQuadDiag.toChord_zeroSanctionNeutral) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto (placableQuadDiag.toChord.targetOnlyPath
      (placableQuadDiag.toChord_lossOffset (placableQuadDiag.u₀_le_q placableQuadDiag_interior)
        placableQuadDiag_margin) x₀) atTop
      (𝓝 placableQuadDiag.steady10)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I,
      placableQuadDiag.toChord.responsePath placableQuadDiag.toChord.VSstar z = z ∧
      placableQuadDiag.steady10 < z ∧
      Tendsto (placableQuadDiag.toChord.dynamicPath
        (placableQuadDiag.toChord_lossOffset (placableQuadDiag.u₀_le_q placableQuadDiag_interior)
          placableQuadDiag_margin)
        (placableQuadDiag.toChord_margin placableQuadDiag_familyMargin) x₀)
        atTop (𝓝 z)) ∧
    0 < placableQuadDiag.steady10 :=
  placableQuadDiagCs.four_cell_closedForm placableQuadDiag_interior placableQuadDiag_margin
    placableQuadDiag_placable placableQuadDiag_familyMargin
    (placableQuadDiagCs.toChordCs.reliefSharp_of_relief placableQuadDiag_relief)

end

/-! ## Rule 10 -/

#print axioms Sanctions.Examples.ChordEconomyCs.VS01_fix
#print axioms Sanctions.Examples.ChordEconomyCs.zeroLevel_continuousOn
#print axioms Sanctions.Examples.ChordEconomyCs.senderOnlyEquilibriumTop
#print axioms Sanctions.Examples.ChordEconomyCs.sender_only_regime_generalF
#print axioms Sanctions.Examples.ChordEconomyCs.four_cell_generalF
#print axioms Sanctions.Examples.ChordEconomyCs.senderOnlyEquilibriumTop'
#print axioms Sanctions.Examples.ChordEconomyCs.sender_only_regime_generalF'
#print axioms Sanctions.Examples.ChordEconomyCs.four_cell_generalF'
#print axioms Sanctions.Examples.ChordEconomyCs.four_cell_generalF'_of_response_monotone
#print axioms Sanctions.Examples.ChordEconomyCs.reliefSharp_of_Mtot_eq_q
#print axioms Sanctions.Examples.ChordEconomyCs.reliefSharp_of_scaled_Mtot_le
#print axioms Sanctions.Examples.ChordEconomyCs.four_cell_longrun_difference
#print axioms Sanctions.Examples.ChordEconomyCs.four_cell_rule_difference_at_state
#print axioms Sanctions.Examples.ChordEconomyCs.four_cell_longrun_difference'
#print axioms Sanctions.Examples.ChordEconomyCs.four_cell_rule_difference_at_state'
#print axioms Sanctions.Examples.ChordEconomyCs.four_cell_rule_chain
#print axioms Sanctions.Examples.ChordEconomyCs.stageRelief_of_reliefSharp
#print axioms Sanctions.Examples.ChordEconomyCs.reliefSharp_uniform_iff
#print axioms Sanctions.Examples.PlacableEconomyFcs.four_cell_closedForm
#print axioms Sanctions.Examples.placableAffine_four_cells
#print axioms Sanctions.Examples.placableQuadDiag_four_cells

end Examples
end Sanctions
