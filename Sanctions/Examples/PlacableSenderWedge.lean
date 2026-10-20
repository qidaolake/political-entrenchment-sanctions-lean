/-
Sanctions/Examples/PlacableSenderWedge.lean

**The Sender-foresight wedge, along the realised paths, and after imposed
relief** (round AB, 2026-09-19; the reader's family-welfare challenge of
2026-09-19, nodes P2–P4; on the abstract payoffs since round AV, 2026-09-25,
doc 104).

The forward-looking Sender's sanction at defiance sits *strictly above* the
stage selector (`responsePath_gt_stage`). Its size is available from what the
chord economy already proves:

* every Sender carrier value rises by at least `g_S = w_lo/(1 − β_S·g_lo)` per
  unit of state on the whole unit interval (`clip_lowerSlope`);
* the transition rises by at least `d_lo` per unit of sanction (`hSlo`);
* so the discounted continuation term `β_S·V(F(x,s))` rises by at least
  `β_S·g_S·d_lo` per unit of sanction, and the shifted-argmax bound for a
  `Q̄`-semiconvex objective with an interior maximiser
  (`Foundations/QuadraticArgmaxLowerBound.lean`,
  `min_one_shifted_argmax_le_of_semiconvex`) puts every maximiser at least
  `min 1 (σ(x,0) + β_S·g_S·d_lo/Q̄)`;
* the interior cap `A/q < 1` (`responsePath_le_cap`) removes the clip.

Hence, at every carrier value and every state,

  `R¹¹(x) ≥ R¹⁰(x) + β_S·w_lo·d_lo / (Q̄·(1 − β_S·g_lo))`,

with the **upper** curvature `Q̄` (the cap `A/q` uses the lower one). The
abbreviation `wedge` is a Lean-internal handle, not a paper-facing scalar
(Rule 3, symbol economy).

Carried to the paths (Rule 1: both rules are the constructed equilibria's own
realised rules): from a common start the forward-looking path dominates the
Target-only path at every date and the realised sanctions differ by at least the
same wedge at every date; the two zero-sanction cells `00` and `01` share one
state path. After any feasible imposed schedule — relief included — the resumed
forward-looking equilibrium sanctions at least `σ(x,0) + wedge` at every date and
its state converges to a fixed point of the response strictly above the floor
`b = σ(0,0)`: temporary relief does not end the constructed forward-looking
regime.

**The long-run gap.** A fixed point `z` of the forward-looking response
satisfies `z ≥ σ(z,0) + wedge`, and the stage selector rises by at least
`(r_lo/Q̄)·Δx` (its lower slope band: the lower cross rate S8 against the upper
curvature S5); so against the Target-only limit `z₁₀ = σ(z₁₀,0)` from the same
start, `z − z₁₀ ≥ β_S·g_S·d_lo/(Q̄ − r_lo)` (`fixedPoint_ge_limit10_add_gap`,
`dynamicPath_limit_ge_limit10_add_gap`), where `r_lo < Q̄` is derived
(`rlo_lt_Qbar`). On the quadratic–linear family `z₁₀ = u₀/(q − r)` and the gap is
`β_S·w·d_lo/((q − r)(1 − β_S·g_lo))` (§ family). It is a bound at the constructed
equilibrium; it is not a comparative static of re-solved equilibria in `β_S`.

Rule 22: general in `F` (chord conditions only). Rule 9: nothing here is a
witness; every statement is parametric in the economy.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation item BH3.1 (2026-10-06): `rlo_lt_Qbar`, `stage_argmax_sub_ge` and
`steadyGap_eq` read interiority only through its stage part `u_hi < q`, so they take
that stage appetite as the binder `hS`. The wedge bound itself keeps `hInt`: it
reads the interior cap `A/q < 1`.

Renovation item BH4.1 (2026-10-06): along the paths and in the long-run gap the rally
margin is read only to make the forward-looking realised rule nondecreasing
(`dynamicRule_monotoneOn`). The `_of_response_monotone` forms take a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` in its place, at the constructed
equilibrium `equilibriumTop hTM hmono` and its path `dynamicPathOf hTM hmono`. The margin
forms keep their statements and are corollaries at
`hmono := responsePath_monotoneOn_of_margin hmargin`.

Renovation item BJ3.1 (2026-10-07): the rally margin reads the two-sided curvature data,
which left the base class, so the margin forms are stated on `ChordEconomyTwoSided`; the
`_of_response_monotone` forms and the wedge bounds stay on `ChordEconomy`.
-/
import Sanctions.Examples.PlacableSenderRegime01
import Sanctions.Examples.PlacableSenderEpisode
import Sanctions.Foundations.QuadraticArgmaxLowerBound

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-- The Sender-foresight wedge, `β_S·g_S·d_lo/Q̄` (a proof abbreviation of
existing fields; `wedge_eq` is its closed form in the primitives). -/
def wedge : ℝ := E.β_S * E.gS * E.dlo / E.Qbar

theorem wedge_pos : 0 < E.wedge :=
  div_pos (mul_pos (mul_pos E.hβS0 E.gS_pos) E.hdlo0) E.Qbar_pos

/-- The wedge in the primitives: `β_S·w_lo·d_lo / (Q̄·(1 − β_S·g_lo))`. -/
theorem wedge_eq : E.wedge = E.β_S * E.wlo * E.dlo / (E.Qbar * (1 - E.β_S * E.glo)) := by
  unfold wedge gS chGS
  rw [mul_div_assoc', div_mul_eq_mul_div, div_div, mul_comm (1 - E.β_S * E.glo) E.Qbar]

/-- **The lower cross rate is below the upper curvature**, `r_lo < Q̄`: the cross
difference over the unit square is at most the appetite at the top state less
the floor at the bottom one (S8, S11, S12), and `u_hi < q ≤ Q̄`, `u_lo > 0`. General
in `F`. Under the stage appetite `u_hi < q` (BH3.1, 2026-10-06: the binder was
interiority `A < q`, read only through `u_hi < q`). -/
theorem rlo_lt_Qbar (hS : E.uhi < E.q) : E.rlo < E.Qbar := by
  have h1 := E.hUS_crossLo 0 zero_mem_I 1 one_mem_I 0 zero_mem_I 1 one_mem_I zero_le_one
    zero_le_one
  have h2 := E.hUS_appetite 1 one_mem_I 0 zero_mem_I 1 one_mem_I zero_le_one
  have h3 := E.hUS_floor 0 zero_mem_I 0 zero_mem_I 1 one_mem_I zero_le_one
  have h4 := hS
  have h5 := E.q_le_Qbar
  have h6 := E.hulo
  simp only [sub_zero, mul_one, one_mul, add_zero] at h1 h2 h3
  linarith

/-- **The lower slope band of the stage selector**: across `x ≤ x'` in `[0,1]` the
stage selector at defiance rises by at least `(r_lo/Q̄)(x' − x)`: the stage
objective at `x'` is the one at `x` tilted by a function of lower slope
`r_lo(x' − x)` (S8), and the one at `x` is `Q̄`-semiconvex with an interior
maximiser. General in `F`. The interior maximiser needs only the stage appetite
`u_hi < q` (BH3.1, 2026-10-06: the binder was interiority `A < q`). -/
theorem stage_argmax_sub_ge (hS : E.uhi < E.q) {x x' : ℝ} (hx : x ∈ Sanctions.I) (hx' : x' ∈
    Sanctions.I)
    (hxx' : x ≤ x') : E.rlo / E.Qbar * (x' - x) ≤ E.σ x' 0 - E.σ x 0 := by
  have hQ := E.Qbar_pos
  rcases (mul_nonneg E.hrlo (sub_nonneg.mpr hxx')).lt_or_eq with hpos | hzero
  · have hmono := E.stage_argmax_mono hx hx' hxx'
    have h := Sanctions.Foundations.QuadraticArgmax.min_one_shifted_argmax_le_of_semiconvex
      (g := fun u => E.U_S x 0 u) (H := fun u => E.U_S x' 0 u - E.U_S x 0 u)
      hQ (E.hUS_convex x hx 0 zero_mem_I) (E.stage_argmax_pos hx)
      (E.stage_argmax_lt_one hS hx).le (E.σ_isMaxOn_U_S x 0) hpos
      (fun s₁ hs₁ s₂ hs₂ hle => by
        have := E.hUS_crossLo x hx x' hx' s₁ hs₁ s₂ hs₂ hxx' hle
        nlinarith [this])
      (E.σ_mem x' 0) (by
        have hm := E.σ_isMaxOn_U_S x' 0
        intro u hu
        have := hm hu
        simp only [Set.mem_setOf_eq] at this ⊢
        linarith)
    have hlt1 := E.stage_argmax_lt_one hS hx'
    have hmin : min 1 (E.σ x 0 + E.rlo * (x' - x) / E.Qbar) = E.σ x 0 + E.rlo * (x' - x) / E.Qbar :=
        by
      apply min_eq_right
      by_contra hcon
      have := min_eq_left (not_le.mp hcon).le
      rw [this] at h
      linarith
    rw [hmin] at h
    have heq : E.rlo / E.Qbar * (x' - x) = E.rlo * (x' - x) / E.Qbar := by ring
    linarith
  · rw [div_mul_eq_mul_div, ← hzero, zero_div]
    exact sub_nonneg.mpr (E.stage_argmax_mono hx hx' hxx')

/-- **The quantitative Sender channel**: at every Sender carrier value and every
state the forward-looking response to defiance is at least the stage selector
plus the wedge. -/
theorem responsePath_ge_stage_add_wedge (hInt : E.Interior) {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) :
    E.σ x 0 + E.wedge ≤ E.responsePath V x := by
  have hmem : E.responsePath V x ∈ Icc (0 : ℝ) 1 := E.responsePath_mem V x
  have hlt1 : E.responsePath V x < 1 :=
    lt_of_le_of_lt (E.responsePath_le_cap hV hx) (E.cap_lt_one hInt)
  have hL : 0 < E.β_S * E.gS * E.dlo := mul_pos (mul_pos E.hβS0 E.gS_pos) E.hdlo0
  -- the continuation term has lower slope `β_S g_S d_lo`
  have hslope : ∀ s₁ ∈ Icc (0 : ℝ) 1, ∀ s₂ ∈ Icc (0 : ℝ) 1, s₁ ≤ s₂ →
      E.β_S * E.gS * E.dlo * (s₂ - s₁)
        ≤ E.β_S * V (Sanctions.clipS' (E.F x s₂)) - E.β_S * V (Sanctions.clipS' (E.F x s₁)) := by
    intro s₁ hs₁ s₂ hs₂ hle
    have hFle : E.F x s₁ ≤ E.F x s₂ := E.F_mono_s x hle
    have hFchord : E.dlo * (s₂ - s₁) ≤ E.F x s₂ - E.F x s₁ := E.hSlo hx hs₁ hs₂ hle
    have hgain : E.gS * (E.F x s₂ - E.F x s₁)
        ≤ V (Sanctions.clipS' (E.F x s₂)) - V (Sanctions.clipS' (E.F x s₁)) :=
      E.clip_lowerSlope hV.1 _ (E.F_mem _ _ hx hs₁) _ (E.F_mem _ _ hx hs₂) hFle
    have h1 : E.gS * (E.dlo * (s₂ - s₁)) ≤ E.gS * (E.F x s₂ - E.F x s₁) :=
      mul_le_mul_of_nonneg_left hFchord E.gS_pos.le
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hgain) E.hβS0.le
    nlinarith [h2]
  have h := Sanctions.Foundations.QuadraticArgmax.min_one_shifted_argmax_le_of_semiconvex
    (g := fun u => E.U_S x 0 u) (H := fun u => E.β_S * V (Sanctions.clipS' (E.F x u)))
    E.Qbar_pos (E.hUS_convex x hx 0 zero_mem_I) (E.stage_argmax_pos hx)
    (E.stage_argmax_lt_one (E.uhi_lt_q hInt) hx).le (E.σ_isMaxOn_U_S x 0) hL hslope hmem
    (E.response_isMaxOn V x 0)
  have hmin : min 1 (E.σ x 0 + E.β_S * E.gS * E.dlo / E.Qbar)
      = E.σ x 0 + E.β_S * E.gS * E.dlo / E.Qbar := by
    apply min_eq_right
    by_contra hcon
    have := min_eq_left (not_le.mp hcon).le
    rw [this] at h
    linarith
  rw [hmin] at h
  exact h

/-- **The wedge between the two constructed realised rules, given a nondecreasing
response** (renovation item BH4.1, 2026-10-06), at every state: the realised sanction of
the forward-looking equilibrium `equilibriumTop hTM hmono` exceeds the Target-only
equilibrium's by at least the wedge. General in `F`. The nondecreasing response only
names the equilibrium; the bound reads interiority's cap through
`responsePath_ge_stage_add_wedge`. -/
theorem targetOnlyRule_add_wedge_le_dynamicRule_of_response_monotone (hInt : E.Interior)
    (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x + E.wedge
      ≤ E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono) x := by
  rw [(E.targetOnlyRule_eq_stage hTM) hx,
    E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hx]
  exact E.responsePath_ge_stage_add_wedge hInt E.VSstar_mem hx

/-- **The forward-looking realised rule is monotone on the unit interval, given a
nondecreasing response** (BH4.1, 2026-10-06). General in `F`. At
`equilibriumTop hTM hmono` the realised rule is the response (`responsePath VSstar`), so
it inherits `hmono`; this is where the rally margin was used, through
`responsePath_monotoneOn_of_margin`. -/
theorem dynamicRule_monotoneOn_of_response_monotone (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    MonotoneOn (E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono))
      Sanctions.I := by
  intro x hx y hy hxy
  rw [E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hx,
    E.dynamicRule_eq_responsePath_of_response_monotone hTM hmono hy]
  exact hmono hx hy hxy

/-- **Ordered realised state paths, given a nondecreasing response** (BH4.1, 2026-10-06):
from a common start the path of `equilibriumTop hTM hmono` dominates the Target-only path
at every date. General in `F`. The forward-looking rule lies above the Target-only rule
(the wedge) and is nondecreasing (`hmono`), so the comparison carries along the paths. -/
theorem targetOnlyPath_le_dynamicPath_of_response_monotone (hInt : E.Interior)
    (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E.targetOnlyPath hTM) x₀ t ≤ E.dynamicPathOf hTM hmono x₀ t :=
  E.toParams.rulePathF_le_of_rule_le_and_upper_mono
    (fun _ hx => (E.targetOnlyRule_mem hTM) hx) (E.dynamicRule_mem_of_response_monotone hTM hmono)
    (E.dynamicRule_monotoneOn_of_response_monotone hTM hmono)
    (fun x hx => by
      have := E.targetOnlyRule_add_wedge_le_dynamicRule_of_response_monotone hInt hTM hmono hx
      linarith [E.wedge_pos]) hx₀

/-- **The wedge along the realised paths, given a nondecreasing response** (renovation
item BH4.1, 2026-10-06): from a common start, at every date, the realised sanction of the
forward-looking equilibrium `equilibriumTop hTM hmono` exceeds the Target-only
equilibrium's by at least the wedge. General in `F`. This is
`targetOnlySanction_add_wedge_le_dynamicSanction` with the rally margin replaced by the
nondecreasing response it was used to obtain: that monotonicity orders the two state
paths, and the cross-state step uses the monotone stage selector, not an order between
the two games' value functions. -/
theorem targetOnlySanction_add_wedge_le_dynamicSanction_of_response_monotone
    (hInt : E.Interior) (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) ((E.targetOnlyPath hTM) x₀ t)
        + E.wedge
      ≤ E.toParams.dynamicEquilibriumRule (E.equilibriumTop hTM hmono)
          (E.dynamicPathOf hTM hmono x₀ t) := by
  have h10 : (E.targetOnlyPath hTM) x₀ t ∈ Sanctions.I :=
    E.toParams.rulePathF_mem_I (fun _ hx => (E.targetOnlyRule_mem hTM) hx) hx₀ t
  have h11 : E.dynamicPathOf hTM hmono x₀ t ∈ Sanctions.I :=
    E.toParams.rulePathF_mem_I (E.dynamicRule_mem_of_response_monotone hTM hmono) hx₀ t
  have hle := E.targetOnlyPath_le_dynamicPath_of_response_monotone hInt hTM hmono hx₀ t
  have hv : E.σ ((E.targetOnlyPath hTM) x₀ t) 0 ≤ E.σ (E.dynamicPathOf hTM hmono x₀ t) 0 :=
    E.stage_argmax_mono h10 h11 hle
  rw [(E.targetOnlyRule_eq_stage hTM) h10]
  have := E.targetOnlyRule_add_wedge_le_dynamicRule_of_response_monotone hInt hTM hmono h11
  rw [(E.targetOnlyRule_eq_stage hTM) h11] at this
  linarith

/-! ## The long-run gap -/

/-- **A fixed point of the forward-looking response exceeds a fixed point of the
stage selector below it by at least `β_S g_S d_lo/(Q̄ − r_lo)`**: from
`z ≥ σ(z,0) + wedge` and the lower slope band `σ(z,0) − z₁₀ ≥ (r_lo/Q̄)(z − z₁₀)`. -/
theorem fixedPoint_ge_limit10_add_gap (hInt : E.Interior) {z z₁₀ : ℝ} (hz : z ∈ Sanctions.I)
    (hz₁₀ : z₁₀ ∈ Sanctions.I) (hfix : E.responsePath E.VSstar z = z)
    (hfix₁₀ : E.σ z₁₀ 0 = z₁₀) (hle : z₁₀ ≤ z) :
    z₁₀ + E.β_S * E.gS * E.dlo / (E.Qbar - E.rlo) ≤ z := by
  have h := E.responsePath_ge_stage_add_wedge hInt E.VSstar_mem hz
  rw [hfix] at h
  have hband := E.stage_argmax_sub_ge (E.uhi_lt_q hInt) hz₁₀ hz hle
  rw [hfix₁₀] at hband
  have hQ := E.Qbar_pos
  have hQr : 0 < E.Qbar - E.rlo := sub_pos.mpr (E.rlo_lt_Qbar (E.uhi_lt_q hInt))
  -- `(1 − r_lo/Q̄)(z − z₁₀) ≥ wedge`, cleared of denominators
  have hkey : E.β_S * E.gS * E.dlo ≤ (E.Qbar - E.rlo) * (z - z₁₀) := by
    have e1 : E.rlo / E.Qbar * (z - z₁₀) * E.Qbar = E.rlo * (z - z₁₀) := by field_simp
    have e2 : E.wedge * E.Qbar = E.β_S * E.gS * E.dlo := by unfold wedge; field_simp
    have h1 : (E.σ z 0 + E.wedge) * E.Qbar ≤ z * E.Qbar := mul_le_mul_of_nonneg_right h hQ.le
    have h2 : E.rlo / E.Qbar * (z - z₁₀) * E.Qbar ≤ (E.σ z 0 - z₁₀) * E.Qbar :=
      mul_le_mul_of_nonneg_right hband hQ.le
    nlinarith [h1, h2, e1, e2]
  rw [← sub_nonneg]
  have : E.β_S * E.gS * E.dlo / (E.Qbar - E.rlo) ≤ z - z₁₀ := by
    rw [div_le_iff₀ hQr]; linarith
  linarith

/-- The long-run gap in the primitives:
`β_S g_S d_lo/(Q̄ − r_lo) = β_S·w_lo·d_lo / ((Q̄ − r_lo)·(1 − β_S·g_lo))`. General in
`F`. Under the stage appetite `u_hi < q`, which gives `r_lo < Q̄` (BH3.1, 2026-10-06:
the binder was interiority `A < q`). -/
theorem steadyGap_eq (hS : E.uhi < E.q) :
    E.β_S * E.gS * E.dlo / (E.Qbar - E.rlo)
      = E.β_S * E.wlo * E.dlo / ((E.Qbar - E.rlo) * (1 - E.β_S * E.glo)) := by
  have hQr : E.Qbar - E.rlo ≠ 0 := (sub_pos.mpr (E.rlo_lt_Qbar hS)).ne'
  have h1 : 1 - E.β_S * E.glo ≠ 0 := E.one_sub_βS_glo_pos.ne'
  unfold gS chGS
  field_simp

/-- **The long-run gap at the constructed equilibria, given a nondecreasing response**
(renovation item BH4.1, 2026-10-06). From every feasible start the Target-only path
converges to a fixed point `z₁₀` of the stage selector and the path of the forward-looking
equilibrium `equilibriumTop hTM hmono` to a fixed point `z` of the response, and
`z ≥ z₁₀ + β_S·w_lo·d_lo/((Q̄ − r_lo)(1 − β_S·g_lo))`. General in `F`. This is
`dynamicPath_limit_ge_limit10_add_gap` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]`: the margin was used only to
order and converge the paths. -/
theorem dynamicPath_limit_ge_limit10_add_gap_of_response_monotone (hInt : E.Interior)
    (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧
      z₁₀ + E.β_S * E.wlo * E.dlo / ((E.Qbar - E.rlo) * (1 - E.β_S * E.glo)) ≤ z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto (E.dynamicPathOf hTM hmono x₀) atTop (𝓝 z) := by
  obtain ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, hlt, ht₁₀, ht⟩ :=
    E.targetOnly_limit_lt_dynamic_limit_of_response_monotone (E.uhi_lt_q hInt) hTM hmono hx₀
  refine ⟨z₁₀, hz₁₀, z, hz, hfix₁₀, hfix, ?_, ht₁₀, ht⟩
  rw [← E.steadyGap_eq (E.uhi_lt_q hInt)]
  exact E.fixedPoint_ge_limit10_add_gap hInt hz hz₁₀ hfix hfix₁₀ hlt.le

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-! ### The rally-margin forms, on the two-sided extension (renovation item BJ3.1)

The rally margin reads the two-sided curvature data `τ_x`, `M_cx`, `M_mix`, so since
2026-10-07 the margin forms below are stated on `ChordEconomyTwoSided`; until then they
were on `ChordEconomy`, otherwise unchanged. Each is general in `F`. -/

/-- **The wedge between the two constructed realised rules**, at every state:
the forward-looking equilibrium's sanction exceeds the Target-only equilibrium's
by at least the wedge. General in `F`. The rally-margin form of
`targetOnlyRule_add_wedge_le_dynamicRule_of_response_monotone` (BH4.1). -/
theorem targetOnlyRule_add_wedge_le_dynamicRule (hInt : E.Interior) (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) x + E.wedge
      ≤ E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x :=
  E.targetOnlyRule_add_wedge_le_dynamicRule_of_response_monotone hInt hTM
    (E.responsePath_monotoneOn_of_margin hmargin) hx

/-- The forward-looking rule is monotone on the unit interval under the margin. General
in `F`. The rally-margin form of `dynamicRule_monotoneOn_of_response_monotone` (BH4.1). -/
theorem dynamicRule_monotoneOn (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    MonotoneOn (E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin))
      Sanctions.I :=
  E.dynamicRule_monotoneOn_of_response_monotone hTM (E.responsePath_monotoneOn_of_margin hmargin)

/-- **Ordered realised state paths**: from a common start the forward-looking
path dominates the Target-only path at every date. General in `F`. The rally-margin form
of `targetOnlyPath_le_dynamicPath_of_response_monotone` (BH4.1). -/
theorem targetOnlyPath_le_dynamicPath (hInt : E.Interior) (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, (E.targetOnlyPath hTM) x₀ t ≤ (E.dynamicPath hTM) hmargin x₀ t :=
  E.targetOnlyPath_le_dynamicPath_of_response_monotone hInt hTM
    (E.responsePath_monotoneOn_of_margin hmargin) hx₀

/-- **The wedge along the realised paths**: from a common start, at every date,
the forward-looking equilibrium's realised sanction exceeds the Target-only
equilibrium's by at least the wedge. The cross-state step uses the monotone
stage selector, not an order between the two games' value functions. General in `F`. The
rally-margin form of `targetOnlySanction_add_wedge_le_dynamicSanction_of_response_monotone`
(BH4.1). -/
theorem targetOnlySanction_add_wedge_le_dynamicSanction (hInt : E.Interior) (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    E.pT.dynamicEquilibriumRule (E.targetOnlyEquilibriumTop hTM) ((E.targetOnlyPath hTM) x₀ t)
        + E.wedge
      ≤ E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin)
          ((E.dynamicPath hTM) hmargin x₀ t) :=
  E.targetOnlySanction_add_wedge_le_dynamicSanction_of_response_monotone hInt hTM
    (E.responsePath_monotoneOn_of_margin hmargin) hx₀ t

/-! ## Resumption after an imposed schedule (relief included) -/

/-- The forward-looking path is the general-`F` lock-in path of the constructed
equilibrium (both are the same iterate). -/
theorem dynamicPath_eq_lockInPathF (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (x₀ : ℝ) (n : ℕ) :
    (E.dynamicPath hTM) hmargin x₀ n
      = E.toParams.dynamicTopLockInPathF ((E.equilibriumTop_of_margin hTM) hmargin).V_S
          ((E.equilibriumTop_of_margin hTM) hmargin).α x₀ n := rfl

/-- **Temporary relief does not end the constructed forward-looking regime.**
After *any* feasible imposed sanction schedule `u` of any length `T` — zero
sanctions included — the resumed equilibrium (the same optimising equilibrium,
restarted at the episode-end state) sanctions at least the stage selector plus
the wedge at every later date, and its state converges to a fixed point of the
response strictly above the floor `b = σ(0,0)`. The limit may depend on the
episode-end state unless the closed loop contracts. -/
theorem placable_resumption_after_episode (hInt : E.Interior) (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {u : ℕ → ℝ} (hu : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n, E.σ (E.toParams.splicedPath ((E.equilibriumTop_of_margin hTM) hmargin).V_S
              ((E.equilibriumTop_of_margin hTM) hmargin).α u T x₀ (T + n)) 0 + E.wedge
        ≤ E.toParams.splicedSanction ((E.equilibriumTop_of_margin hTM) hmargin).V_S
            ((E.equilibriumTop_of_margin hTM) hmargin).α u T x₀ (T + n)) ∧
    ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧
      Tendsto (fun n => E.toParams.splicedPath ((E.equilibriumTop_of_margin hTM) hmargin).V_S
          ((E.equilibriumTop_of_margin hTM) hmargin).α u T x₀ (T + n)) atTop (𝓝 z) := by
  have hend : E.toParams.episodePath u x₀ T ∈ Sanctions.I :=
    E.toParams.episodePath_mem hu hx₀ T
  have hpath : ∀ n, E.toParams.splicedPath ((E.equilibriumTop_of_margin hTM) hmargin).V_S
      ((E.equilibriumTop_of_margin hTM) hmargin).α u T x₀ (T + n)
        = (E.dynamicPath hTM) hmargin (E.toParams.episodePath u x₀ T) n := fun n => by
    rw [E.toParams.splicedPath_add, (E.dynamicPath_eq_lockInPathF hTM)]
  refine ⟨fun n => ?_, ?_⟩
  · have hmemn : (E.dynamicPath hTM) hmargin (E.toParams.episodePath u x₀ T) n ∈ Sanctions.I :=
      E.toParams.rulePathF_mem_I ((E.dynamicRule_mem hTM) hmargin) hend n
    rw [E.toParams.splicedSanction_add, hpath n]
    have h := E.responsePath_ge_stage_add_wedge hInt E.VSstar_mem hmemn
    rw [← (E.dynamicRule_eq_responsePath hTM) hmargin hmemn] at h
    exact h
  · obtain ⟨z, hz, hfix, hgt, _, htend⟩ :=
      (E.dynamicPath_tendsto (E.uhi_lt_q hInt) hTM) hmargin hend
    exact ⟨z, hz, hfix, hgt, by simpa [hpath] using htend⟩

/-! ### The long-run gap, rally-margin form

The margin form of the long-run gap; the `_of_response_monotone` form and the fixed-point
bound are in the section on the long-run gap above, on `ChordEconomy`. -/

/-- **The long-run gap at the constructed equilibria.** From every feasible start
the Target-only path converges to a fixed point `z₁₀` of the stage selector and
the forward-looking path to a fixed point `z` of the response, and
`z ≥ z₁₀ + β_S·w_lo·d_lo/((Q̄ − r_lo)(1 − β_S·g_lo))`. General in `F`. The rally-margin
form of `dynamicPath_limit_ge_limit10_add_gap_of_response_monotone` (BH4.1). -/
theorem dynamicPath_limit_ge_limit10_add_gap (hInt : E.Interior) (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧
      z₁₀ + E.β_S * E.wlo * E.dlo / ((E.Qbar - E.rlo) * (1 - E.β_S * E.glo)) ≤ z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z) :=
  E.dynamicPath_limit_ge_limit10_add_gap_of_response_monotone hInt hTM
    (E.responsePath_monotoneOn_of_margin hmargin) hx₀

end ChordEconomyTwoSided

namespace ChordEconomyCs

variable (E : ChordEconomyCs)

/-- **The two zero-sanction cells share one state path**: under the sharp relief
margin, the fully myopic path and the Sender-only path coincide from every
feasible start (both realised rules are zero on the unit interval). General in `F`.
No stage relief hypothesis (renovation item BG3.2, 2026-10-06): the myopic path is read
at the stage relief margin that the sharp relief margin implies
(`stageRelief_of_reliefSharp`). -/
theorem myopicPath_eq_senderOnlyPath_of_reliefSharp (hInt : E.Interior) (hP : E.Placable)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    (E.myopicPath hInt (E.stageRelief_of_reliefSharp hrelief) hP) x₀ t
      = (E.senderOnlyPath' hInt hP) hrelief hN x₀ t := by
  have h0 : ∀ t, (E.myopicPath hInt (E.stageRelief_of_reliefSharp hrelief) hP) x₀ t
      = E.toParams.rulePathF (fun _ => 0) x₀ t :=
    E.toParams.rulePathF_congr_on
      (fun x hx => by
        rw [(E.myopicRule_eq_zero hInt (E.stageRelief_of_reliefSharp hrelief) hP) hx]
        exact ⟨le_rfl, zero_le_one⟩)
      (fun x hx => (E.myopicRule_eq_zero hInt (E.stageRelief_of_reliefSharp hrelief) hP) hx)
      hx₀
  have h1 : ∀ t, (E.senderOnlyPath' hInt hP) hrelief hN x₀ t
      = E.toParams.rulePathF (fun _ => 0) x₀ t :=
    E.toParams.rulePathF_congr_on
      (fun x hx => by
        rw [(E.senderOnlyRule_eq_zero' hInt hP) hrelief hN hx]; exact ⟨le_rfl, zero_le_one⟩)
      (fun x hx => (E.senderOnlyRule_eq_zero' hInt hP) hrelief hN hx) hx₀
  rw [h0 t, h1 t]

/-- **The two zero-sanction cells share one state path**, with the stage relief margin as
an explicit binder: a corollary of `myopicPath_eq_senderOnlyPath_of_reliefSharp`, kept for
its callers. The binder `hSR` is redundant beside `hrelief` (BG3.2). General in `F`. -/
theorem myopicPath_eq_senderOnlyPath' (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    (E.myopicPath hInt hSR hP) x₀ t = (E.senderOnlyPath' hInt hP) hrelief hN x₀ t :=
  E.myopicPath_eq_senderOnlyPath_of_reliefSharp hInt hP hrelief hN hx₀ t

end ChordEconomyCs

/-! ## The quadratic–linear family: the long-run gap in closed form (sign-off M6)

Renovation item BJ2.3 (2026-10-07): the family no longer carries the interiority field, so
each result here takes the family's interiority as the hypothesis `hInt : E.Interior`; it is
what makes the stage selector the vertex and keeps `r < q`. General in `F`. -/

namespace PlacableEconomyF

variable (E : PlacableEconomyF)

/-- **Every fixed point of the family's forward-looking response exceeds the
Target-only steady state `u₀/(q − r)` by at least `q·wedge/(q − r)`**: on the
family the stage selector is the vertex `(u₀ + r·x)/q`. Interiority is the hypothesis
`hInt` since renovation item BJ2.3 (it was a field). General in `F`. -/
theorem fixedPoint_ge_steady10_add_gap (hInt : E.Interior) {z : ℝ} (hz : z ∈ Sanctions.I)
    (hfix : E.toChord.responsePath E.toChord.VSstar z = z) :
    E.steady10 + E.q * E.toChord.wedge / (E.q - E.r) ≤ z := by
  have h := E.toChord.responsePath_ge_stage_add_wedge (E.toChord_interior hInt)
    E.toChord.VSstar_mem hz
  rw [hfix, E.toChord_σ_zero hInt hz] at h
  have hqr : 0 < E.q - E.r := sub_pos.mpr (E.r_lt_q hInt)
  have hmul : E.u₀ + E.r * z ≤ (z - E.toChord.wedge) * E.q := by
    apply (div_le_iff₀ E.hq).mp
    change E.vertex z ≤ z - E.toChord.wedge
    linarith
  change E.u₀ / (E.q - E.r) + E.q * E.toChord.wedge / (E.q - E.r) ≤ z
  rw [← add_div, div_le_iff₀ hqr]
  nlinarith

/-- The family's long-run gap in its primitives:
`q·wedge/(q − r) = β_S·w·d_lo / ((q − r)·(1 − β_S·g_lo))`. Interiority (`r < q`) is the
hypothesis `hInt` since renovation item BJ2.3. General in `F`. -/
theorem steadyGap_eq (hInt : E.Interior) :
    E.q * E.toChord.wedge / (E.q - E.r)
      = E.βS * E.w * E.dlo / ((E.q - E.r) * (1 - E.βS * E.glo)) := by
  have hq : E.q ≠ 0 := E.hq.ne'
  have hqr : E.q - E.r ≠ 0 := (sub_pos.mpr (E.r_lt_q hInt)).ne'
  have h1 : 1 - E.βS * E.glo ≠ 0 := E.toChord.one_sub_βS_glo_pos.ne'
  rw [E.toChord.wedge_eq]
  change E.q * (E.βS * E.w * E.dlo / (E.q * (1 - E.βS * E.glo))) / (E.q - E.r) = _
  field_simp

/-- **The long-run gap at the family's constructed equilibrium, given a nondecreasing
response** (renovation item BH4.1, 2026-10-06). From every feasible start the path of the
forward-looking equilibrium `equilibriumTop` of the member's chord economy converges to a
fixed point of the response that exceeds the Target-only steady state `u₀/(q − r)` by at
least the closed-form gap `β_S·w·d_lo/((q − r)(1 − β_S·g_lo))`. On the quadratic–linear
family, general in the family's transition `F`. This is
`dynamicPath_limit_ge_steady10_add_gap` with the rally margin replaced by a nondecreasing
response `responsePath VSstar`; the margin was used only to order and converge the
paths. Interiority is the hypothesis `hInt` since renovation item BJ2.3 (it was a
field). -/
theorem dynamicPath_limit_ge_steady10_add_gap_of_response_monotone (hInt : E.Interior)
    (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.toChord.responsePath E.toChord.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z ∈ Sanctions.I, E.toChord.responsePath E.toChord.VSstar z = z ∧
      E.steady10 + E.βS * E.w * E.dlo / ((E.q - E.r) * (1 - E.βS * E.glo)) ≤ z ∧
      Tendsto (E.toChord.dynamicPathOf (E.toChord_lossOffset (E.u₀_le_q hInt) hTM) hmono x₀)
        atTop (𝓝 z) := by
  obtain ⟨z, hz, hfix, _, htend⟩ :=
    E.targetOnly_steady_lt_dynamic_steady_of_response_monotone hInt hTM hmono hx₀
  refine ⟨z, hz, hfix, ?_, htend⟩
  rw [← E.steadyGap_eq hInt]
  exact E.fixedPoint_ge_steady10_add_gap hInt hz hfix

/-- **The long-run gap at the family's constructed equilibrium.** From every
feasible start the forward-looking path converges to a fixed point of the
response that exceeds the Target-only steady state by at least the closed-form
gap. The rally-margin form of `dynamicPath_limit_ge_steady10_add_gap_of_response_monotone`
(BH4.1). Interiority is the hypothesis `hInt` since renovation item BJ2.3 (it was a
field). General in `F`. -/
theorem dynamicPath_limit_ge_steady10_add_gap (hInt : E.Interior) (hTM : E.LossOffset)
    (hmargin : E.βS * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.r)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z ∈ Sanctions.I, E.toChord.responsePath E.toChord.VSstar z = z ∧
      E.steady10 + E.βS * E.w * E.dlo / ((E.q - E.r) * (1 - E.βS * E.glo)) ≤ z ∧
      Tendsto (E.toChord.dynamicPath (E.toChord_lossOffset (E.u₀_le_q hInt) hTM)
        (E.toChord_margin hmargin) x₀) atTop (𝓝 z) :=
  E.dynamicPath_limit_ge_steady10_add_gap_of_response_monotone hInt hTM
    (E.toChord.responsePath_monotoneOn_of_margin (E.toChord_margin hmargin)) hx₀

end PlacableEconomyF

end

#print axioms ChordEconomy.wedge_eq
#print axioms ChordEconomy.rlo_lt_Qbar
#print axioms ChordEconomy.stage_argmax_sub_ge
#print axioms ChordEconomy.responsePath_ge_stage_add_wedge
#print axioms ChordEconomyTwoSided.targetOnlyRule_add_wedge_le_dynamicRule
#print axioms ChordEconomyTwoSided.targetOnlyPath_le_dynamicPath
#print axioms ChordEconomyTwoSided.targetOnlySanction_add_wedge_le_dynamicSanction
#print axioms ChordEconomyTwoSided.placable_resumption_after_episode
#print axioms ChordEconomy.fixedPoint_ge_limit10_add_gap
#print axioms ChordEconomyTwoSided.dynamicPath_limit_ge_limit10_add_gap
#print axioms ChordEconomyCs.myopicPath_eq_senderOnlyPath'
#print axioms ChordEconomyCs.myopicPath_eq_senderOnlyPath_of_reliefSharp
#print axioms PlacableEconomyF.fixedPoint_ge_steady10_add_gap
#print axioms PlacableEconomyF.dynamicPath_limit_ge_steady10_add_gap
#print axioms ChordEconomy.targetOnlySanction_add_wedge_le_dynamicSanction_of_response_monotone
#print axioms ChordEconomy.dynamicPath_limit_ge_limit10_add_gap_of_response_monotone
#print axioms PlacableEconomyF.dynamicPath_limit_ge_steady10_add_gap_of_response_monotone

end Examples
end Sanctions
