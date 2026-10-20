/-
Sanctions/Examples/PlacableSenderTargetLipschitz.lean

**A two-sided Target value on a chord economy: the equilibrium Target value
is Lipschitz in the state, with the Hinderer 4.2(c) constant** (round AJ,
2026-09-22; doc 98 B9 and §5.2, on the user's word; on the abstract payoffs
since round AV, 2026-09-25, doc 104).

The chord economy's Target carrier `carrierT` is a sup-norm ball with a
*lower* state slope `g_T` and nothing else (`PlacableSenderEquilibrium.lean`);
the symbolic family's Target carrier is two-sided (`valLipGainBall`). Doc 98
§5.2 verified that the missing upper bound is absent from this family and not
from the project, and that the external theorem is Hinderer (2005) Theorem
4.2(c): a Lipschitz recursion `K ↦ L_U + β_T·γ_T·K` whose fixed point
`K_T = L_U/(1 − β_T·γ_T)` is preserved by the Bellman operator when
`β_T·γ_T < 1` (`hinderer_lipschitz_invariance`, already in the tree). This file
supplies the two ingredients and composes them.

* **The successor's state modulus** at the equilibrium Sender value is the
  sharp loop constant `γ_T = g_hi + d_hi·L_resp/μ` (`successor_lipschitz_sharp`,
  round Q; `LloopSharp`), from the response's `L_resp/μ`-Lipschitz dependence
  on the state.
* **The Target stage payoff along the response** is
  `L_U = max(v_hi, v_hi + n_hi) + c·L_resp/μ` Lipschitz in the state
  (`targetStage_lipschitz`): the state rate `v_hi + n_hi·s` of the upper state
  bound (T6u) at its largest over `s ∈ [0,1]`, plus the pain rate `c` (T2)
  times the response's state modulus. On the quadratic–linear family `n_hi = n ≥ 0`,
  so the maximum is `v + n`.
* **The constant** `K_T = L_U/(1 − β_T·γ_T)` (`KT`). The set of `K_T`-Lipschitz
  values is closed, nonempty and invariant under the Target operator whenever
  `β_T·γ_T < 1` (`targetOp_lipschitz`).
* **The Target operator's fixed point is `K_T`-Lipschitz** (`targetFix_lipschitz`):
  the operator is a contraction on the whole value space, so the invariant closed
  set contains its unique fixed point. Only `β_T·γ_T < 1` is read.
* **The equilibrium Target value is `K_T`-Lipschitz** (`VTstar_lipschitz`): `VTstar`
  is that fixed point.
* **The two-sided sanction bracket on the Target's continuation** at the
  equilibrium (`VTstar_continuation_bracket`): for `s₁ ≤ s₂`,
  `β_T·g_T·d_lo·(s₂ − s₁) ≤ β_T·(V_T(F(y,s₂)) − V_T(F(y,s₁))) ≤ β_T·K_T·d_hi·(s₂ − s₁)`.
  The lower half is the loss-offset margin's ingredient (defiance); the upper
  half is the new one, the prerequisite of a relief-side condition under a
  general transition.

Renovation item BH3.11(b) (2026-10-06). The two-sided carrier
`carrierTL = carrierT ∩ {K_T-Lipschitz}` and its four lemmas are gone. Its `carrierT`
half needed the loss-offset margin and a monotone response, and only the Lipschitz half
was ever used, so `VTstar_lipschitz` now goes through `targetFix_lipschitz`, which reads
`β_T·γ_T < 1` alone. The halves of the bracket at the defiance-profile value `VTdef`, each
with only the hypotheses it reads, are `VTdef_continuation_upper` and
`VTdef_continuation_lower` (`PlacableSenderBracket.lean`).

**What is not here.** The bracket in the Target's discount factor itself — a
condition under which defiance is *not* optimal, `ℓ < (c − n − β_T·d_hi·K_T)·κ`
with `κ` a lower bound on the response's relief rate in compliance — needs the
enriched subclass's sanction-section modulus for `κ` (`ChordEconomyCs`,
`PlacableSenderRegime01`) and is the next step, not this file's.

**Rule 3.** No field is added: `β_T·γ_T < 1` is a hypothesis `hγ` of the
theorems that read it, in the pattern of the rally margin `hmargin`. Symbol
economy: `γ_T` is `LloopSharp`, already named; `L_U` and `K_T` are closed forms
in existing constants. Rule 22: general in the transition, through the chord
constants only.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.
-/
import Sanctions.Examples.PlacableSenderRegimes
import Sanctions.Foundations.Hinderer
import Sanctions.Theory.Bellman.InvariantLipBall

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-! ## The constants -/

/-- The Target stage payoff's state-Lipschitz constant along the response:
`max(v_hi, v_hi + n_hi) + c·L_resp/μ`. -/
def LUT : ℝ := max E.vhi (E.vhi + E.nhi) + E.c * (E.Lresp / E.mu)

/-- The upper state rate `v_hi + n_hi·s` is at most `max(v_hi, v_hi + n_hi)` on
`[0,1]`: an affine function of `s` is at most its larger endpoint. -/
theorem vhi_rate_le_max {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    E.vhi + E.nhi * s ≤ max E.vhi (E.vhi + E.nhi) := by
  have h : E.vhi + E.nhi * s = (1 - s) * E.vhi + s * (E.vhi + E.nhi) := by ring
  rw [h]
  have h1 := mul_le_mul_of_nonneg_left (le_max_left E.vhi (E.vhi + E.nhi))
    (sub_nonneg.mpr hs.2)
  have h2 := mul_le_mul_of_nonneg_left (le_max_right E.vhi (E.vhi + E.nhi)) hs.1
  nlinarith [h1, h2]

theorem vhi_max_pos : 0 < max E.vhi (E.vhi + E.nhi) := by
  have h := E.vlo_le_vhi 0 zero_mem_I
  simp only [mul_zero, add_zero] at h
  exact lt_of_lt_of_le (lt_of_lt_of_le E.hvlo h) (le_max_left _ _)

theorem LUT_nonneg : 0 ≤ E.LUT := by
  unfold LUT
  have := E.vhi_max_pos
  have := mul_nonneg E.c_pos.le (div_nonneg E.Lresp_nonneg E.mu_pos.le)
  linarith

/-- **The Target value's Lipschitz constant, Hinderer 4.2(c)**:
`K_T = L_U/(1 − β_T·γ_T)` with `γ_T = g_hi + d_hi·L_resp/μ` the sharp loop
constant. Meaningful when `β_T·γ_T < 1`. -/
def KT : ℝ := E.LUT / (1 - E.β_T * E.LloopSharp)

theorem one_sub_βT_γ_pos (hγ : E.β_T * E.LloopSharp < 1) : 0 < 1 - E.β_T * E.LloopSharp := by
  linarith

theorem KT_nonneg (hγ : E.β_T * E.LloopSharp < 1) : 0 ≤ E.KT :=
  div_nonneg E.LUT_nonneg (E.one_sub_βT_γ_pos hγ).le

/-- The Hinderer fixed-point identity: `L_U + β_T·γ_T·K_T = K_T`. -/
theorem KT_fix (hγ : E.β_T * E.LloopSharp < 1) : E.LUT + E.β_T * E.LloopSharp * E.KT = E.KT := by
  have h := (E.one_sub_βT_γ_pos hγ).ne'
  unfold KT
  field_simp
  ring

theorem glo_le_LloopSharp : E.glo ≤ E.LloopSharp := by
  unfold LloopSharp
  have := mul_nonneg E.dhi_nonneg (div_nonneg E.Lresp_nonneg E.mu_pos.le)
  linarith [E.hglo_ghi]

/-- `g_T ≤ K_T`: the lower slope is below the Lipschitz constant. -/
theorem gT_le_KT (hγ : E.β_T * E.LloopSharp < 1) : E.gT ≤ E.KT := by
  have hden := E.one_sub_βT_γ_pos hγ
  have hglo : 0 < 1 - E.β_T * E.glo := by
    have := mul_le_mul_of_nonneg_left E.glo_le_LloopSharp E.hβT0.le
    linarith
  have hnum : E.vlo + E.nlo * E.sfloor ≤ E.LUT := by
    unfold LUT
    have h1 := E.vlo_le_vhi E.sfloor E.sfloor_mem
    have h2 := E.vhi_rate_le_max E.sfloor_mem
    have := mul_nonneg E.c_pos.le (div_nonneg E.Lresp_nonneg E.mu_pos.le)
    linarith
  have hgT : E.gT = (E.vlo + E.nlo * E.sfloor) / (1 - E.β_T * E.glo) := by
    have := E.gT_mul
    rw [← this]
    field_simp
  rw [hgT]
  unfold KT
  apply div_le_div₀ E.LUT_nonneg hnum hden
  have := mul_le_mul_of_nonneg_left E.glo_le_LloopSharp E.hβT0.le
  linarith

/-! ## The stage payoff along the response is Lipschitz in the state -/

/-- **The Target's stage payoff at defiance and the realised response is
`L_U`-Lipschitz in the state.** -/
theorem targetStage_lipschitz {y₁ y₂ : ℝ} (hy₁ : y₁ ∈ Icc (0 : ℝ) 1) (hy₂ : y₂ ∈ Icc (0 : ℝ) 1) :
    |E.toParams.U_T y₂ 0 (E.responsePath E.VSstar y₂)
        - E.toParams.U_T y₁ 0 (E.responsePath E.VSstar y₁)| ≤ E.LUT * |y₂ - y₁| := by
  set R₁ := E.responsePath E.VSstar y₁ with hR₁
  set R₂ := E.responsePath E.VSstar y₂ with hR₂
  have hR₁m := E.responsePath_mem E.VSstar y₁
  have hR₂m := E.responsePath_mem E.VSstar y₂
  have hRL : |R₂ - R₁| ≤ E.Lresp * |y₂ - y₁| / E.mu := E.responsePath_lipschitz_sharp hy₂ hy₁
  -- The sanction leg (T2): pain at most `c` per unit.
  have hs := E.UT_sanction_lip hy₂ zero_mem_I hR₁m hR₂m
  -- The state leg (T6u) at the sanction `R₁`.
  have hx := E.hUT_stateHi 0 zero_mem_I R₁ hR₁m y₁ hy₁ y₂ hy₂
  have hrate := E.vhi_rate_le_max hR₁m
  have hmu := E.mu_pos
  have hx' : |E.U_T y₂ 0 R₁ - E.U_T y₁ 0 R₁| ≤ max E.vhi (E.vhi + E.nhi) * |y₂ - y₁| :=
    hx.trans (mul_le_mul_of_nonneg_right hrate (abs_nonneg _))
  have hs' : |E.U_T y₂ 0 R₂ - E.U_T y₂ 0 R₁| ≤ E.c * (E.Lresp * |y₂ - y₁| / E.mu) :=
    hs.trans (mul_le_mul_of_nonneg_left hRL E.c_pos.le)
  change |E.U_T y₂ 0 R₂ - E.U_T y₁ 0 R₁| ≤ E.LUT * |y₂ - y₁|
  calc |E.U_T y₂ 0 R₂ - E.U_T y₁ 0 R₁|
      = |(E.U_T y₂ 0 R₂ - E.U_T y₂ 0 R₁) + (E.U_T y₂ 0 R₁ - E.U_T y₁ 0 R₁)| := by ring_nf
    _ ≤ |E.U_T y₂ 0 R₂ - E.U_T y₂ 0 R₁| + |E.U_T y₂ 0 R₁ - E.U_T y₁ 0 R₁| := abs_add_le _ _
    _ ≤ E.c * (E.Lresp * |y₂ - y₁| / E.mu) + max E.vhi (E.vhi + E.nhi) * |y₂ - y₁| :=
        add_le_add hs' hx'
    _ = E.LUT * |y₂ - y₁| := by unfold LUT; field_simp; ring

/-! ## The Lipschitz clause is invariant -/

/-- **The Target operator preserves the `K_T`-Lipschitz clause** at the
equilibrium Sender value, when `β_T·γ_T < 1`. -/
theorem targetOp_lipschitz (hγ : E.β_T * E.LloopSharp < 1) {V_T : Val}
    (hV : Params.ValueLipschitzWith V_T E.KT) :
    Params.ValueLipschitzWith (E.targetOp E.VSstar_mem V_T) E.KT := by
  intro y₁ y₂
  rw [targetOp_apply, targetOp_apply]
  have hy₁ := y₁.property
  have hy₂ := y₂.property
  have hd : dist y₁ y₂ = |y₂.val - y₁.val| := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
  rw [hd]
  have hstage := E.targetStage_lipschitz hy₁ hy₂
  have hF₁ : E.toParams.F y₁.val (E.responsePath E.VSstar y₁.val) ∈ Icc (0 : ℝ) 1 :=
    E.F_mem _ _ hy₁ (E.responsePath_mem E.VSstar y₁.val)
  have hF₂ : E.toParams.F y₂.val (E.responsePath E.VSstar y₂.val) ∈ Icc (0 : ℝ) 1 :=
    E.F_mem _ _ hy₂ (E.responsePath_mem E.VSstar y₂.val)
  have hsucc : |E.toParams.F y₂.val (E.responsePath E.VSstar y₂.val)
      - E.toParams.F y₁.val (E.responsePath E.VSstar y₁.val)|
      ≤ (E.ghi + E.dhi * (E.Lresp / E.mu)) * |y₂.val - y₁.val| :=
    E.successor_lipschitz_sharp hy₂ hy₁
  have hV' := hV (Sanctions.clipS' (E.toParams.F y₁.val (E.responsePath E.VSstar y₁.val)))
    (Sanctions.clipS' (E.toParams.F y₂.val (E.responsePath E.VSstar y₂.val)))
  have hdc : dist (Sanctions.clipS' (E.toParams.F y₁.val (E.responsePath E.VSstar y₁.val)))
      (Sanctions.clipS' (E.toParams.F y₂.val (E.responsePath E.VSstar y₂.val)))
      = |E.toParams.F y₂.val (E.responsePath E.VSstar y₂.val)
          - E.toParams.F y₁.val (E.responsePath E.VSstar y₁.val)| := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hF₁,
        Sanctions.clipS'_val_eq_of_mem hF₂, abs_sub_comm]
  rw [hdc] at hV'
  have hKT := E.KT_nonneg hγ
  have hβ := E.hβT0.le
  have hcont : |V_T (Sanctions.clipS' (E.toParams.F y₂.val (E.responsePath E.VSstar y₂.val)))
      - V_T (Sanctions.clipS' (E.toParams.F y₁.val (E.responsePath E.VSstar y₁.val)))|
      ≤ E.KT * (E.LloopSharp * |y₂.val - y₁.val|) := by
    refine le_trans hV' ?_
    apply mul_le_mul_of_nonneg_left _ hKT
    unfold LloopSharp
    exact hsucc
  have hfix := E.KT_fix hγ
  calc |E.toParams.U_T y₂.val 0 (E.responsePath E.VSstar y₂.val)
          + E.β_T * V_T (Sanctions.clipS' (E.toParams.F y₂.val (E.responsePath E.VSstar y₂.val)))
        - (E.toParams.U_T y₁.val 0 (E.responsePath E.VSstar y₁.val)
          + E.β_T * V_T (Sanctions.clipS' (E.toParams.F y₁.val (E.responsePath E.VSstar y₁.val))))|
      = |(E.toParams.U_T y₂.val 0 (E.responsePath E.VSstar y₂.val)
          - E.toParams.U_T y₁.val 0 (E.responsePath E.VSstar y₁.val))
        + E.β_T * (V_T (Sanctions.clipS' (E.toParams.F y₂.val (E.responsePath E.VSstar y₂.val)))
          - V_T (Sanctions.clipS' (E.toParams.F y₁.val (E.responsePath E.VSstar y₁.val))))| := by
        ring_nf
    _ ≤ |E.toParams.U_T y₂.val 0 (E.responsePath E.VSstar y₂.val)
          - E.toParams.U_T y₁.val 0 (E.responsePath E.VSstar y₁.val)|
        + E.β_T * |V_T (Sanctions.clipS' (E.toParams.F y₂.val (E.responsePath E.VSstar y₂.val)))
          - V_T (Sanctions.clipS' (E.toParams.F y₁.val (E.responsePath E.VSstar y₁.val)))| := by
        have := abs_add_le (E.toParams.U_T y₂.val 0 (E.responsePath E.VSstar y₂.val)
          - E.toParams.U_T y₁.val 0 (E.responsePath E.VSstar y₁.val))
          (E.β_T * (V_T (Sanctions.clipS' (E.toParams.F y₂.val (E.responsePath E.VSstar y₂.val)))
          - V_T (Sanctions.clipS' (E.toParams.F y₁.val (E.responsePath E.VSstar y₁.val)))))
        rw [abs_mul, abs_of_nonneg hβ] at this
        exact this
    _ ≤ E.LUT * |y₂.val - y₁.val| + E.β_T * (E.KT * (E.LloopSharp * |y₂.val - y₁.val|)) :=
        add_le_add hstage (mul_le_mul_of_nonneg_left hcont hβ)
    _ = E.KT * |y₂.val - y₁.val| := by linear_combination |y₂.val - y₁.val| * hfix

/-! ## The Target operator's fixed point is Lipschitz -/

/-- **The fixed point of the Target operator at `VSstar` is `K_T`-Lipschitz in the
state**, under `β_T·γ_T < 1` alone (renovation item BH3.11(b), 2026-10-06). The set of
`K_T`-Lipschitz values is closed, contains `0` and is invariant under the operator
(`targetOp_lipschitz`); the operator contracts on the whole value space, so its unique
fixed point lies in that set. No loss-offset margin and no monotone response are read:
those fed only the `carrierT` half of the former two-sided carrier `carrierTL`, and no
result used that half. This fixed point is the defiance-profile Target value `VTdef`
(`PlacableSenderBracket.lean`). General in `F`. -/
theorem targetFix_lipschitz (hγ : E.β_T * E.LloopSharp < 1) :
    Params.ValueLipschitzWith (E.targetOp_contracting E.VSstar_mem).fixedPoint E.KT := by
  have hcontr := E.targetOp_contracting E.VSstar_mem
  obtain ⟨W, hW, hWmem⟩ := StokeyLucas.fixedPoint_mem_of_mapsTo hcontr.1 _ hcontr.2
    {V : Val | Params.ValueLipschitzWith V E.KT}
    (Params.valueLipschitz_isClosed _) ⟨0, fun y₁ y₂ => by
      simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, sub_zero, abs_zero]
      exact mul_nonneg (E.KT_nonneg hγ) dist_nonneg⟩
    (fun V hV => E.targetOp_lipschitz hγ hV)
  have h1 : W = hcontr.fixedPoint := hcontr.fixedPoint_unique hW
  change Params.ValueLipschitzWith hcontr.fixedPoint E.KT
  rw [← h1]
  exact hWmem

/-! ## The equilibrium Target value is Lipschitz -/

/-- **The equilibrium Target value is `K_T`-Lipschitz in the state.** `VTstar` is the
Target operator's unique fixed point, so this is `targetFix_lipschitz` (renovation item
BH3.11(b), 2026-10-06; until then it went through the two-sided carrier `carrierTL`, whose
invariance read the margin and the monotone response). Only `β_T·γ_T < 1` is used: `hTM`
and `hmono` stay in the statement because `VTstar` needs them to exist. General in `F`. -/
theorem VTstar_lipschitz (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hγ : E.β_T * E.LloopSharp < 1) : Params.ValueLipschitzWith (E.VTstar hTM hmono) E.KT := by
  rw [(E.targetOp_contracting E.VSstar_mem).fixedPoint_unique (E.VTstar_fix hTM hmono)]
  exact E.targetFix_lipschitz hγ

/-- **The two-sided bracket on the Target's discounted continuation gain from a
higher sanction** at the equilibrium value: at least `β_T·g_T·d_lo·(s₂ − s₁)`
and at most `β_T·K_T·d_hi·(s₂ − s₁)`. Each half at the defiance-profile value `VTdef`,
with only the hypotheses it reads (`β_T·γ_T < 1` for the upper half; a monotone response,
a slope `g ≥ 0` and the balance for the lower), is `VTdef_continuation_upper` and
`VTdef_continuation_lower` (`PlacableSenderBracket.lean`, renovation item BH3.11(c)). -/
theorem VTstar_continuation_bracket (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hγ : E.β_T * E.LloopSharp < 1) {y s₁ s₂ : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hs₁ : s₁ ∈ Icc (0 : ℝ) 1) (hs₂ : s₂ ∈ Icc (0 : ℝ) 1) (hle : s₁ ≤ s₂) :
    E.β_T * E.gT * E.dlo * (s₂ - s₁)
      ≤ E.β_T * (E.VTstar hTM hmono (Sanctions.clipS' (E.F y s₂))
          - E.VTstar hTM hmono (Sanctions.clipS' (E.F y s₁))) ∧
    E.β_T * (E.VTstar hTM hmono (Sanctions.clipS' (E.F y s₂))
          - E.VTstar hTM hmono (Sanctions.clipS' (E.F y s₁)))
      ≤ E.β_T * E.KT * E.dhi * (s₂ - s₁) := by
  have hF₁ := E.F_mem _ _ hy hs₁
  have hF₂ := E.F_mem _ _ hy hs₂
  have hz : E.F y s₁ ≤ E.F y s₂ := E.F_mono_s _ hle
  have hβ := E.hβT0.le
  constructor
  · have hlo := E.clipT_lowerSlope (E.VTstar_mem hTM hmono) _ hF₁ _ hF₂ hz
    have hchord := E.hSlo hy hs₁ hs₂ hle
    have h1 : E.gT * (E.dlo * (s₂ - s₁)) ≤ E.gT * (E.F y s₂ - E.F y s₁) :=
      mul_le_mul_of_nonneg_left hchord E.gT_pos.le
    have := mul_le_mul_of_nonneg_left (le_trans h1 hlo) hβ
    linarith
  · have hlip := ((E.VTstar_lipschitz hTM) hmono hγ) (Sanctions.clipS' (E.F y s₁))
      (Sanctions.clipS' (E.F y s₂))
    have hdc : dist (Sanctions.clipS' (E.F y s₁)) (Sanctions.clipS' (E.F y s₂))
        = E.F y s₂ - E.F y s₁ := by
      rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hF₁,
          Sanctions.clipS'_val_eq_of_mem hF₂, abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hdc] at hlip
    have hchord := E.hShi hy hs₁ hs₂ hle
    have hKT := E.KT_nonneg hγ
    have h1 : E.KT * (E.F y s₂ - E.F y s₁) ≤ E.KT * (E.dhi * (s₂ - s₁)) :=
      mul_le_mul_of_nonneg_left hchord hKT
    have h2 := (abs_le.mp hlip).2
    have := mul_le_mul_of_nonneg_left (le_trans h2 h1) hβ
    linarith

end ChordEconomyRelief

end

#print axioms Sanctions.Examples.ChordEconomyRelief.targetStage_lipschitz
#print axioms Sanctions.Examples.ChordEconomyRelief.targetFix_lipschitz
#print axioms Sanctions.Examples.ChordEconomyRelief.VTstar_lipschitz
#print axioms Sanctions.Examples.ChordEconomyRelief.VTstar_continuation_bracket

end Examples
end Sanctions
