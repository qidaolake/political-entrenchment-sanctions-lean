/-
Sanctions/Theory/LockIn/SenderStakeSign.lean

**The sign of the Sender's stake: the quantitative mirrors of the forward-looking Sender
channel** (step 2, target 2b, 2026-10-10; referee M2(a)).

`DynamicStake.lean` proves the weak mirror of the dominance comparison: under a Sender value
that does not rise with the political state, the greatest forward-looking sanction is at
most the greatest stage maximiser. This file proves the quantitative mirrors, for a Sender
whose value **falls** with the political state (a *hostile* stake: the Sender's coalition
loses when hard-liners in the Target gain), together with the zero-stake equality.

## What is proved (all at the level of an arbitrary economy `p : Params`)

* **N7, the reverse wedge** (`σ_dyn_top_le_stage_sub_wedge`, `dynamicArgmax_le_stage_sub_wedge`):
  against a continuation value that falls at rate at least `h`, every forward-looking
  sanction at compliance `a` is at most `max 0 (σ(x,a) − β_S·h·d_lo/M)`, where `M` is the
  stage payoff's curvature ceiling in the sanction and `d_lo` the transition's sanction chord.
* **N8, zero stake** (`dynamicTopRealizedRule_eq_stageTopRule_of_stateFree`): if the Sender's
  stage payoff along the Target's policy does not depend on the state, the forward-looking
  Sender plays the greatest stage maximiser — it acts myopically.
* **N9, cheaper relief** (`σ_dyn_top_eq_zero_of_placation_gap`, `zeroLevel_le_of_placation_gap`,
  `zeroLevel_lt_of_placation_gap`): at a continuation value falling at rate `h`, the least
  compliance that ends the forward-looking sanction is at most
  `max 0 (z − β_S·h·d_lo/k_hi) < z`, where `z` is a compliance level at which zero sanction is
  a stage optimum (the myopic zero level) and `k_hi` the placation ceiling.
* **N11, the residual floor** (`dynamicArgmax_ge_residual`, `σ_dyn_top_pos_of_residual`): if
  the continuation falls at most at rate `K` and the marginal return to the first unit of
  sanction is at least `u_lo` (chord form, curvature `M`), every forward-looking sanction is at
  least `min 1 ((u_lo − β_S·K·d_hi)/M)`; it is positive under the residual appetite
  `u_lo > β_S·K·d_hi`.
* **N13 at equilibrium** (`equilibrium_V_S_eq_reliefValue`): in every equilibrium whose realised
  sanction is zero and in which compliance is worth nothing to the Sender at zero sanction, the
  Sender's value is the relief value of `SenderUpperSlopeCone.lean`.
* **N10, every full-defiance equilibrium with a hostile stake**
  (`hostileRule_le_stage_sub_wedge`, `hostilePath_le_stagePath`,
  `hostileSanction_le_stage_sub_wedge`, `hostileLimit_le_stageLimit_sub_gap`): if the Target
  fully defies and the Sender's payoff at defiance falls in the state at rate at least `w` at
  every sanction level, the realised sanction rule lies below the stage rule less the wedge;
  from a common start the state path lies below the path under the stage rule at every date
  (no monotone forward-looking response is needed); the realised sanctions lie below the
  stage-rule sanctions less the wedge; and every limit of the path is at most
  `max 0 (z₁₀ − β_S·h·d_lo/(M − r))`, `z₁₀` the stage rule's limit and `r/M` its lower slope.

**The stake bound must hold at every sanction level** (plan, Section 4, D2): measured at zero
sanction only, the reverse wedge is false when the Sender's rally term `r` is positive. The
binders of N10 are therefore uniform in the sanction.

Rule 1: every sanction is an argmax object (`σ_dyn_top`, the greatest maximiser), the
Target's full defiance is the equilibrium's own policy. Rule 3: the hostile stake bound
(approved hypothesis 3) and the residual appetite (approved hypothesis 4) are theorem binders
over the existing `U_S`, `F`, `σ`; no field, no structure, no new `Prop`. Rule 15: every value
is a constructed Banach fixed point, identified with an equilibrium's by uniqueness. Rule 22:
general in `F`.
-/
import Sanctions.Theory.LockIn.DynamicStake
import Sanctions.Theory.Bellman.SenderUpperSlopeCone
import Sanctions.Foundations.ZeroLevel
import Sanctions.Foundations.TransitionChords

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Helper: a falling continuation along the successor range -/

/-- **A continuation value falling at rate `h ≥ 0` falls along the successor range at rate
`h·d_lo`**: for `s₁ ≤ s₂` in `[0,1]`,
`V(F(x,s₂)) − V(F(x,s₁)) ≤ −h·d_lo·(s₂ − s₁)` when the transition's sanction chord at `x` is
`d_lo`.
Scope: general class (any `Params`, any continuation value that falls in the state). -/
theorem continuation_sub_le_of_negLowerSlope {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {h dl x : ℝ} (hx : x ∈ Sanctions.I)
    (hV : LowerSlopeOnValueOn (-V) (Set.Icc (0 : ℝ) 1) h) (hh : 0 ≤ h)
    (hSlo : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
      dl * (s₂ - s₁) ≤ p.F x s₂ - p.F x s₁)
    {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Sanctions.I) (hs₂ : s₂ ∈ Sanctions.I) (hle : s₁ ≤ s₂) :
    V (Sanctions.clipS' (p.F x s₂)) - V (Sanctions.clipS' (p.F x s₁))
      ≤ -(h * dl * (s₂ - s₁)) := by
  have hF₁ : p.F x s₁ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem _ _ hx hs₁
  have hF₂ : p.F x s₂ ∈ Set.Icc (0 : ℝ) 1 := p.F_mem _ _ hx hs₂
  have hFle : p.F x s₁ ≤ p.F x s₂ := p.F_mono_s x hle
  have hVs := hV (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
    (by rw [Sanctions.clipS'_val_eq_of_mem hF₁]; exact hF₁)
    (by rw [Sanctions.clipS'_val_eq_of_mem hF₂]; exact hF₂) (Sanctions.clipS'_mono hFle)
  have hdF : dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
      = p.F x s₂ - p.F x s₁ := by
    rw [Sanctions.AbstractGame.Params.clipS'_dist_eq_of_mem hF₁ hF₂, abs_sub_comm]
    exact abs_of_nonneg (by linarith)
  rw [hdF] at hVs
  simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply] at hVs
  have hch := mul_le_mul_of_nonneg_left (hSlo s₁ hs₁ s₂ hs₂ hle) hh
  nlinarith [hVs, hch]

/-! ## N7. The reverse wedge -/

/-- **The reverse wedge, at every forward-looking maximiser (N7).** Against a continuation
value `V` that falls in the state at rate at least `h ≥ 0`, if the stage payoff
`U_S(x,a,·)` is `M`-semiconvex on `[0,1]` (`M > 0`, the curvature ceiling), its stage
maximiser `σ(x,a)` is below `1`, the transition's sanction chord at `x` is `d_lo`, and
`β_S·h·d_lo > 0`, then every maximiser of the forward-looking objective
`U_S(x,a,s) + β_S·V(F(x,s))` is at most `max 0 (σ(x,a) − β_S·h·d_lo/M)`: the Sender's
foresight lowers the sanction by at least the wedge, down to zero. The mirror of
`responsePath_ge_stage_add_wedge`; the proof is the reflected shifted-argmax bound.
At the Sender's value against full defiance the fall comes from approved hypothesis 3.
Scope: general class (any `Params`, any continuation value that falls in the state). -/
theorem dynamicArgmax_le_stage_sub_wedge {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {h dl M x a : ℝ} (hx : x ∈ Sanctions.I)
    (hV : LowerSlopeOnValueOn (-V) (Set.Icc (0 : ℝ) 1) h) (hh : 0 ≤ h)
    (hSlo : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
      dl * (s₂ - s₁) ≤ p.F x s₂ - p.F x s₁)
    (hM : 0 < M)
    (hconv : Sanctions.Semiconcave.SemiconvexOnSet (fun s => p.U_S x a s) (Set.Icc (0 : ℝ) 1) M)
    (hσ1 : p.σ x a < 1) (hL : 0 < p.β_S * h * dl)
    {s : ℝ} (hs : s ∈ p.dynamicArgmaxSet V x a) :
    s ≤ max 0 (p.σ x a - p.β_S * h * dl / M) := by
  have hβ : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hH : ∀ s₁ ∈ Set.Icc (0 : ℝ) 1, ∀ s₂ ∈ Set.Icc (0 : ℝ) 1, s₁ ≤ s₂ →
      p.β_S * V (Sanctions.clipS' (p.F x s₂)) - p.β_S * V (Sanctions.clipS' (p.F x s₁))
        ≤ -(p.β_S * h * dl * (s₂ - s₁)) := by
    intro s₁ hs₁ s₂ hs₂ hle
    have hc := p.continuation_sub_le_of_negLowerSlope hx hV hh hSlo hs₁ hs₂ hle
    have := mul_le_mul_of_nonneg_left hc hβ
    nlinarith [this]
  exact Sanctions.Foundations.ReflectedArgmax.argmax_le_max_zero_shifted_of_semiconvex
    (g := fun u => p.U_S x a u) (H := fun u => p.β_S * V (Sanctions.clipS' (p.F x u)))
    hM hconv (p.σ_mem x a).1 hσ1 (p.σ_isMaxOn_U_S x a) hL hH hs.1 hs.2

/-- **The reverse wedge (N7).** Against a continuation value falling in the state at rate at
least `h ≥ 0`, the greatest forward-looking sanction at `(x, a)` is at most
`max 0 (σ(x,a) − β_S·h·d_lo/M)`. At the Sender's value against full defiance, `h` is the
compounded hostile rate `w/(1 − β_S·g_lo)` (`V_S_negLowerSlope_of_stateChords`), which gives
the hostile wedge `R ≤ max 0 (σᴹ − β_S·ḡ_S·d_lo/Q̄)`.
At the Sender's value against full defiance the fall comes from approved hypothesis 3.
Scope: general class (any `Params`, any continuation value that falls in the state). -/
theorem σ_dyn_top_le_stage_sub_wedge {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {h dl M x a : ℝ} (hx : x ∈ Sanctions.I)
    (hV : LowerSlopeOnValueOn (-V) (Set.Icc (0 : ℝ) 1) h) (hh : 0 ≤ h)
    (hSlo : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
      dl * (s₂ - s₁) ≤ p.F x s₂ - p.F x s₁)
    (hM : 0 < M)
    (hconv : Sanctions.Semiconcave.SemiconvexOnSet (fun s => p.U_S x a s) (Set.Icc (0 : ℝ) 1) M)
    (hσ1 : p.σ x a < 1) (hL : 0 < p.β_S * h * dl) :
    p.σ_dyn_top V x a ≤ max 0 (p.σ x a - p.β_S * h * dl / M) :=
  p.dynamicArgmax_le_stage_sub_wedge hx hV hh hSlo hM hconv hσ1 hL
    (p.σ_dyn_top_mem_dynamicArgmaxSet V x a)

/-! ## N8. Zero stake: the Sender acts myopically -/

/-- **A Sender with no state stake acts myopically (N8).** If the Sender's stage payoff read
along the Target's policy does not depend on the political state —
`U_S(y, α y, s) = U_S(x, α x, s)` for all feasible states and sanctions — then at every state
the greatest forward-looking sanction against the constructed Sender value equals the greatest
stage maximiser. The sharp form of DYNAMIC-STAKE: `≤` is
`no_dynamic_floor_of_antitone_state_chord`, `≥` is `stageTopRule_le_dynamicTopRealizedRule`
at the (then monotone) constructed value.
Scope: general class (any `Params`, any continuous Target policy). -/
theorem dynamicTopRealizedRule_eq_stageTopRule_of_stateFree {α : ℝ → ℝ} (hα : Continuous α)
    (hflat : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      p.U_S y (α y) s = p.U_S x (α x) s) (x : ℝ) :
    p.dynamicTopRealizedRule (p.V_S α hα) α x = p.stageTopRule α x := by
  apply le_antisymm
  · exact p.no_dynamic_floor_of_antitone_state_chord hα
      (fun s hs x hx y hy _ => le_of_eq (hflat s hs x hx y hy)) x
  · have hmono := p.V_S_monotone_of_integrand_monotone hα
      (fun s hs x hx y hy _ => le_of_eq (hflat s hs y hy x hx))
    exact p.stageTopRule_le_dynamicTopRealizedRule (p.V_S α hα) (fun _ _ hab => hmono hab) α x

/-! ## N9. The relief price falls with a hostile stake -/

/-- **A placation gap below the stage zero level ends the forward-looking sanction (N9,
`Params` step).** Let zero sanction be a stage optimum at compliance `z`
(`IsMaxOn (U_S(x,z,·)) [0,1] 0`), let compliance `a` raise the Sender's stage return to a
sanction `s` by at most `k_hi·(z − a)·s` relative to `z` (the placation ceiling), let the
continuation value fall in the state at rate `h ≥ 0`, and let the transition's sanction chord at
`x` be `d_lo`. If `k_hi·(z − a) < β_S·h·d_lo`, the forward-looking Sender does not sanction at
`(x, a)`. No curvature is used: every positive sanction loses at least
`(β_S·h·d_lo − k_hi·(z − a))·s`.
At the relief value the fall comes from approved hypothesis 3 at zero sanction.
Scope: general class (any `Params`, any continuation value that falls in the state). -/
theorem σ_dyn_top_eq_zero_of_placation_gap {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {h dl khi x a z : ℝ} (hx : x ∈ Sanctions.I)
    (hzmax : IsMaxOn (fun s => p.U_S x z s) Sanctions.I 0)
    (hPC : ∀ s ∈ Sanctions.I,
      (p.U_S x a s - p.U_S x a 0) - (p.U_S x z s - p.U_S x z 0) ≤ khi * (z - a) * s)
    (hV : LowerSlopeOnValueOn (-V) (Set.Icc (0 : ℝ) 1) h) (hh : 0 ≤ h)
    (hSlo : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
      dl * (s₂ - s₁) ≤ p.F x s₂ - p.F x s₁)
    (hgap : khi * (z - a) < p.β_S * h * dl) :
    p.σ_dyn_top V x a = 0 := by
  have hβ : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  set r := p.σ_dyn_top V x a with hr
  have hrI : r ∈ Sanctions.I := p.σ_dyn_top_mem_I V x a
  by_contra hne
  have hrpos : 0 < r := lt_of_le_of_ne hrI.1 (Ne.symm hne)
  have hmax := p.σ_dyn_top_isMaxOn V x a h0I
  simp only [Set.mem_setOf_eq] at hmax
  rw [← hr] at hmax
  have hc := p.continuation_sub_le_of_negLowerSlope hx hV hh hSlo h0I hrI hrI.1
  have hcβ := mul_le_mul_of_nonneg_left hc hβ
  have hz := hzmax hrI
  simp only [Set.mem_setOf_eq] at hz
  have hpc := hPC r hrI
  have hneg : (khi * (z - a) - p.β_S * h * dl) * r < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hrpos
  nlinarith [hmax, hcβ, hz, hpc, hneg]

/-- **The relief price falls with a hostile stake (N9).** Under the hypotheses of
`σ_dyn_top_eq_zero_of_placation_gap` at every compliance `a ≤ z`, with `z ∈ [0,1]`,
`k_hi > 0` and `β_S·h·d_lo > 0`, the least compliance at which the forward-looking sanction
vanishes — the zero level `a*(x)` of `a ↦ σ_dyn_top V x a` — satisfies
`a*(x) ≤ max 0 (z − β_S·h·d_lo/k_hi)`. With `z = a⁰⁰(x)` the myopic zero level and `V` the
relief value, this is the cheaper relief price of a hostile Sender.
At the relief value the fall comes from approved hypothesis 3 at zero sanction.
Scope: general class (any `Params`, any continuation value that falls in the state). -/
theorem zeroLevel_le_of_placation_gap {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {h dl khi x z : ℝ} (hx : x ∈ Sanctions.I) (hz : z ∈ Sanctions.I)
    (hzmax : IsMaxOn (fun s => p.U_S x z s) Sanctions.I 0)
    (hPC : ∀ a ∈ Sanctions.I, a ≤ z → ∀ s ∈ Sanctions.I,
      (p.U_S x a s - p.U_S x a 0) - (p.U_S x z s - p.U_S x z 0) ≤ khi * (z - a) * s)
    (hV : LowerSlopeOnValueOn (-V) (Set.Icc (0 : ℝ) 1) h) (hh : 0 ≤ h)
    (hSlo : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
      dl * (s₂ - s₁) ≤ p.F x s₂ - p.F x s₁)
    (hkhi : 0 < khi) (hL : 0 < p.β_S * h * dl) :
    Sanctions.ZeroLevel.level (fun x a => p.σ_dyn_top V x a) x
      ≤ max 0 (z - p.β_S * h * dl / khi) := by
  set c := p.β_S * h * dl / khi with hc_def
  have hc : 0 < c := div_pos hL hkhi
  have hkc : khi * c = p.β_S * h * dl := by rw [hc_def]; field_simp
  have key : ∀ a ∈ Sanctions.I, a ≤ z → z - c < a →
      Sanctions.ZeroLevel.level (fun x a => p.σ_dyn_top V x a) x ≤ a := by
    intro a ha haz hlt
    have hgap : khi * (z - a) < p.β_S * h * dl := by
      have := mul_lt_mul_of_pos_left (show z - a < c by linarith) hkhi
      linarith
    have h0 := p.σ_dyn_top_eq_zero_of_placation_gap hx hzmax (hPC a ha haz) hV hh hSlo hgap
    exact csInf_le (Sanctions.ZeroLevel.zeroSet_bddBelow x) ⟨ha, h0⟩
  rcases lt_or_ge (z - c) 0 with hneg | hnn
  · exact (key 0 ⟨le_rfl, zero_le_one⟩ hz.1 hneg).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    rcases le_or_gt a z with haz | hza
    · exact key a ⟨by linarith, haz.trans hz.2⟩ haz ha
    · exact (key z hz le_rfl (by linarith)).trans hza.le

/-- **The hostile relief price is strictly below the stage zero level (N9, strict form).**
Under the hypotheses of `zeroLevel_le_of_placation_gap` and `z > 0`,
`a*(x) ≤ max 0 (z − β_S·h·d_lo/k_hi) < z`.
At the relief value the fall comes from approved hypothesis 3 at zero sanction.
Scope: general class (any `Params`, any continuation value that falls in the state). -/
theorem zeroLevel_lt_of_placation_gap {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {h dl khi x z : ℝ} (hx : x ∈ Sanctions.I) (hz : z ∈ Sanctions.I)
    (hzmax : IsMaxOn (fun s => p.U_S x z s) Sanctions.I 0)
    (hPC : ∀ a ∈ Sanctions.I, a ≤ z → ∀ s ∈ Sanctions.I,
      (p.U_S x a s - p.U_S x a 0) - (p.U_S x z s - p.U_S x z 0) ≤ khi * (z - a) * s)
    (hV : LowerSlopeOnValueOn (-V) (Set.Icc (0 : ℝ) 1) h) (hh : 0 ≤ h)
    (hSlo : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
      dl * (s₂ - s₁) ≤ p.F x s₂ - p.F x s₁)
    (hkhi : 0 < khi) (hL : 0 < p.β_S * h * dl) (hz0 : 0 < z) :
    Sanctions.ZeroLevel.level (fun x a => p.σ_dyn_top V x a) x
        ≤ max 0 (z - p.β_S * h * dl / khi)
      ∧ max 0 (z - p.β_S * h * dl / khi) < z :=
  ⟨p.zeroLevel_le_of_placation_gap hx hz hzmax hPC hV hh hSlo hkhi hL,
    max_lt hz0 (by linarith [div_pos hL hkhi])⟩

/-! ## N11. The residual floor -/

/-- **The residual floor, at every forward-looking maximiser (N11).** If the continuation value
falls at most at rate `K ≥ 0` in the state (`V` lies in the lower-slope cone with slope `−K`),
the transition's sanction upper chord at `x` is `d_hi`, and the stage payoff rises at least as
fast as the chord `(s − t)·(u_lo − M(s + t)/2)` (`M > 0`), then every maximiser of the
forward-looking objective at `(x, a)` is at least `min 1 ((u_lo − β_S·K·d_hi)/M)`. The mirror of
`responsePath_le_cap`.
Scope: general class (any `Params`, any continuation value with a bounded fall rate). -/
theorem dynamicArgmax_ge_residual {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {K dh M ul x a : ℝ} (hx : x ∈ Sanctions.I)
    (hV : LowerSlopeOnValueOn V (Set.Icc (0 : ℝ) 1) (-K)) (hK : 0 ≤ K)
    (hShi : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
      p.F x s₂ - p.F x s₁ ≤ dh * (s₂ - s₁))
    (hM : 0 < M)
    (hfloor : ∀ t ∈ Sanctions.I, ∀ s ∈ Sanctions.I, t ≤ s →
      (s - t) * (ul - M * (s + t) / 2) ≤ p.U_S x a s - p.U_S x a t)
    {s : ℝ} (hs : s ∈ p.dynamicArgmaxSet V x a) :
    min 1 ((ul - p.β_S * K * dh) / M) ≤ s := by
  have hβ : (0 : ℝ) ≤ p.β_S := p.β_S_mem.1
  have hH : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1, t ≤ s →
      -(p.β_S * K * dh * (s - t))
        ≤ p.β_S * V (Sanctions.clipS' (p.F x s)) - p.β_S * V (Sanctions.clipS' (p.F x t)) := by
    intro t ht s hs' hle
    have hFt : p.F x t ∈ Set.Icc (0 : ℝ) 1 := p.F_mem _ _ hx ht
    have hFs : p.F x s ∈ Set.Icc (0 : ℝ) 1 := p.F_mem _ _ hx hs'
    have hFle : p.F x t ≤ p.F x s := p.F_mono_s x hle
    have hVs := hV (Sanctions.clipS' (p.F x t)) (Sanctions.clipS' (p.F x s))
      (by rw [Sanctions.clipS'_val_eq_of_mem hFt]; exact hFt)
      (by rw [Sanctions.clipS'_val_eq_of_mem hFs]; exact hFs) (Sanctions.clipS'_mono hFle)
    have hdF : dist (Sanctions.clipS' (p.F x t)) (Sanctions.clipS' (p.F x s))
        = p.F x s - p.F x t := by
      rw [Sanctions.AbstractGame.Params.clipS'_dist_eq_of_mem hFt hFs, abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    rw [hdF] at hVs
    have hch := mul_le_mul_of_nonneg_left (hShi t ht s hs' hle) hK
    have h1 : -(K * dh * (s - t))
        ≤ V (Sanctions.clipS' (p.F x s)) - V (Sanctions.clipS' (p.F x t)) := by
      nlinarith [hVs, hch]
    have := mul_le_mul_of_nonneg_left h1 hβ
    nlinarith [this]
  exact Sanctions.Foundations.ReflectedArgmax.min_one_floor_shifted_le_of_isMaxOn
    (g := fun u => p.U_S x a u) (H := fun u => p.β_S * V (Sanctions.clipS' (p.F x u)))
    hM hfloor hH hs.1 hs.2

/-- **The residual floor (N11).** Under the hypotheses of `dynamicArgmax_ge_residual`, the
greatest forward-looking sanction is at least `min 1 ((u_lo − β_S·K·d_hi)/M)`.
Scope: general class (any `Params`, any continuation value with a bounded fall rate). -/
theorem σ_dyn_top_ge_residual {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {K dh M ul x a : ℝ} (hx : x ∈ Sanctions.I)
    (hV : LowerSlopeOnValueOn V (Set.Icc (0 : ℝ) 1) (-K)) (hK : 0 ≤ K)
    (hShi : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
      p.F x s₂ - p.F x s₁ ≤ dh * (s₂ - s₁))
    (hM : 0 < M)
    (hfloor : ∀ t ∈ Sanctions.I, ∀ s ∈ Sanctions.I, t ≤ s →
      (s - t) * (ul - M * (s + t) / 2) ≤ p.U_S x a s - p.U_S x a t) :
    min 1 ((ul - p.β_S * K * dh) / M) ≤ p.σ_dyn_top V x a :=
  p.dynamicArgmax_ge_residual hx hV hK hShi hM hfloor (p.σ_dyn_top_mem_dynamicArgmaxSet V x a)

/-- **Under the residual appetite the forward-looking Sender still sanctions (N11,
positivity).** If moreover `β_S·K·d_hi < u_lo` — the direct return to the first unit of
sanction exceeds the discounted cost of the entrenchment it builds — the greatest
forward-looking sanction is positive.
The binder `β_S·K·d_hi < u_lo` is the residual appetite (approved hypothesis 4).
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 4. -/
theorem σ_dyn_top_pos_of_residual {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {K dh M ul x a : ℝ} (hx : x ∈ Sanctions.I)
    (hV : LowerSlopeOnValueOn V (Set.Icc (0 : ℝ) 1) (-K)) (hK : 0 ≤ K)
    (hShi : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ ≤ s₂ →
      p.F x s₂ - p.F x s₁ ≤ dh * (s₂ - s₁))
    (hM : 0 < M)
    (hfloor : ∀ t ∈ Sanctions.I, ∀ s ∈ Sanctions.I, t ≤ s →
      (s - t) * (ul - M * (s + t) / 2) ≤ p.U_S x a s - p.U_S x a t)
    (hres : p.β_S * K * dh < ul) :
    0 < p.σ_dyn_top V x a :=
  lt_of_lt_of_le (lt_min one_pos (div_pos (by linarith) hM))
    (p.σ_dyn_top_ge_residual hx hV hK hShi hM hfloor)

/-! ## N13 at equilibrium: the relief value is the Sender's value in every relief
equilibrium -/

/-- **The Sender's value in a relief equilibrium is the relief value.** In every top-selector
feedback Stackelberg equilibrium whose realised sanction is zero at every state, and along
whose Target policy compliance is worth nothing to the Sender at zero sanction
(`U_S(x, α x, 0) = U_S(x, 0, 0)`), the Sender's value is `p.reliefValue`: it satisfies the
zero-sanction recursion, whose fixed point is unique.
Zero-sanction neutrality along the policy is the existing `ZeroSanctionNeutral` read at the
equilibrium policy.
Scope: general class (any `Params`; no approved hypothesis). -/
theorem equilibrium_V_S_eq_reliefValue (E : p.FeedbackStackelbergEquilibriumTop)
    (hzero : ∀ x ∈ Sanctions.S, p.dynamicEquilibriumRule E x = 0)
    (hneutral : ∀ x ∈ Sanctions.S, p.U_S x (E.α x) 0 = p.U_S x 0 0) :
    E.V_S = p.reliefValue := by
  apply p.eq_reliefValue_of_fix
  ext y
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have hgt : IsGreatest ((fun s => p.integrandS E.α (fun z => E.V_S z) (y.val, s))
      '' Sanctions.I)
      (p.U_S y.val (E.α y.val) 0 + p.β_S * E.V_S (Sanctions.clipS' (p.F y.val 0))) := by
    refine ⟨⟨0, h0I, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hmax := p.σ_dyn_top_isMaxOn E.V_S y.val (E.α y.val) hs
    simp only [Set.mem_setOf_eq] at hmax
    have h0 : p.σ_dyn_top E.V_S y.val (E.α y.val) = 0 := hzero y.val y.property
    rw [h0] at hmax
    exact hmax
  have hV : E.V_S y
      = p.U_S y.val (E.α y.val) 0 + p.β_S * E.V_S (Sanctions.clipS' (p.F y.val 0)) :=
    calc E.V_S y = p.bellmanS_BCF E.α E.hα E.V_S y := congrArg (fun V => V y) E.V_S_fix
      _ = sSup ((fun s => p.integrandS E.α (fun z => E.V_S z) (y.val, s)) '' Sanctions.I) :=
        rfl
      _ = _ := hgt.csSup_eq
  rw [p.zeroSanctionOp_apply, hV, hneutral y.val y.property]

/-! ## N10. Every full-defiance equilibrium with a hostile stake -/

/-- **The realised rule of every full-defiance equilibrium lies below the stage rule less the
wedge (N10(a)).** Let `E` be a top-selector feedback Stackelberg equilibrium in which the Target
fully defies at every state. Suppose the Sender's payoff at defiance falls in the state at rate
at least `w ≥ 0` **at every sanction level** (the hostile stake bound), the transition rises in
the state at rate at least `g_lo` (`β_S·g_lo < 1`) and in the sanction at rate at least `d_lo`,
the stage payoff at defiance is `M`-semiconvex in the sanction with stage maximiser below `1`,
and `β_S·ḡ_S·d_lo > 0` with `ḡ_S = w/(1 − β_S·g_lo)`. Then at every feasible state the realised
sanction is at most `max 0 (σ(x,0) − β_S·ḡ_S·d_lo/M)`. Route: Banach identification
`E.V_S = p.V_S E.α E.hα`, the fall rate `ḡ_S` of the constructed value, the reverse wedge.
The stake bound is uniform in the sanction.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 3. -/
theorem hostileRule_le_stage_sub_wedge (E : p.FeedbackStackelbergEquilibriumTop)
    (hdef : ∀ x ∈ Sanctions.S, E.α x = 0) {w gl dl M : ℝ} (hw : 0 ≤ w)
    (hβgl : p.β_S * gl < 1)
    (hU : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ 0 s - p.U_S y₁ 0 s ≤ -(w * (y₂ - y₁)))
    (hF : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s)
    (hSlo : Sanctions.TransitionChords.SanctionLowerChord p.F dl) (hM : 0 < M)
    (hconv : ∀ x ∈ Sanctions.I,
      Sanctions.Semiconcave.SemiconvexOnSet (fun s => p.U_S x 0 s) (Set.Icc (0 : ℝ) 1) M)
    (hσ1 : ∀ x ∈ Sanctions.I, p.σ x 0 < 1)
    (hL : 0 < p.β_S * (w / (1 - p.β_S * gl)) * dl)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    p.dynamicEquilibriumRule E x
      ≤ max 0 (p.σ x 0 - p.β_S * (w / (1 - p.β_S * gl)) * dl / M) := by
  have hUα : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ (E.α y₂) s - p.U_S y₁ (E.α y₁) s ≤ -(w * (y₂ - y₁)) := by
    intro s hs y₁ hy₁ y₂ hy₂ hle
    rw [hdef y₁ hy₁, hdef y₂ hy₂]
    exact hU s hs y₁ hy₁ y₂ hy₂ hle
  have hpos : 0 < 1 - p.β_S * gl := by linarith
  have hVfall : LowerSlopeOnValueOn (-E.V_S) (Set.Icc (0 : ℝ) 1) (w / (1 - p.β_S * gl)) := by
    rw [p.equilibrium_V_S_eq_constructed E]
    exact p.V_S_negLowerSlope_of_stateChords E.hα hw hβgl hUα hF
  change p.σ_dyn_top E.V_S x (E.α x) ≤ _
  rw [hdef x hx]
  exact p.σ_dyn_top_le_stage_sub_wedge hx hVfall (div_nonneg hw hpos.le)
    (fun s₁ hs₁ s₂ hs₂ hle => hSlo hx hs₁ hs₂ hle) hM (hconv x hx) (hσ1 x hx) hL

/-- **Paths under a rule below the stage rule's shadow stay below the stage-rule path.** If a
feasible rule `R` satisfies `R x ≤ max 0 (σ(x,0) − c)` on `[0,1]` with `c ≥ 0`, and the stage
rule `x ↦ σ(x,0)` is nondecreasing on `[0,1]`, then from a common feasible start the state path
under `R` lies below the path under the stage rule at every date. No monotonicity of `R` is
used.
Scope: general class (any `Params`; a path comparison). -/
theorem rulePathF_le_stagePath_of_shadow {R : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hRmem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR : ∀ x ∈ Sanctions.I, R x ≤ max 0 (p.σ x 0 - c))
    (hmono : MonotoneOn (fun x => p.σ x 0) Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, p.rulePathF R x₀ t ≤ p.rulePathF (fun x => p.σ x 0) x₀ t :=
  p.rulePathF_le_of_rule_le_and_upper_mono hRmem (fun x _ => p.σ_mem x 0) hmono
    (fun x hx => (hR x hx).trans (max_le (p.σ_mem x 0).1 (by linarith))) hx₀

/-- **Sanctions under a rule below the stage rule's shadow** stay below the stage-rule
sanctions less `c`, date by date, from a common start: `R(x_t) ≤ max 0 (σ(x¹⁰_t, 0) − c)`, where
`x_t` and `x¹⁰_t` are the paths under `R` and under the stage rule.
Scope: general class (any `Params`; a path comparison). -/
theorem ruleSanction_le_stage_sub_of_shadow {R : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hRmem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR : ∀ x ∈ Sanctions.I, R x ≤ max 0 (p.σ x 0 - c))
    (hmono : MonotoneOn (fun x => p.σ x 0) Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    (t : ℕ) :
    R (p.rulePathF R x₀ t) ≤ max 0 (p.σ (p.rulePathF (fun x => p.σ x 0) x₀ t) 0 - c) := by
  have h1 : p.rulePathF R x₀ t ∈ Sanctions.I := p.rulePathF_mem_I hRmem hx₀ t
  have h2 : p.rulePathF (fun x => p.σ x 0) x₀ t ∈ Sanctions.I :=
    p.rulePathF_mem_I (fun x _ => p.σ_mem x 0) hx₀ t
  have hle := p.rulePathF_le_stagePath_of_shadow hc hRmem hR hmono hx₀ t
  have hσ : p.σ (p.rulePathF R x₀ t) 0 ≤ p.σ (p.rulePathF (fun x => p.σ x 0) x₀ t) 0 :=
    hmono h1 h2 hle
  exact (hR _ h1).trans (max_le_max le_rfl (by linarith))

/-- **Limits under a rule below the stage rule's shadow.** Let `R` be feasible with
`R x ≤ max 0 (σ(x,0) − L/M)` on `[0,1]` (`L ≥ 0`, `M > 0`), let the stage rule be continuous,
nondecreasing on `[0,1]`, with lower slope band `(r/M)·(x' − x) ≤ σ(x',0) − σ(x,0)` (`r < M`),
and let the transition's sanction chord be `d_lo > 0`. If from a common start the path under
`R` converges to `z` and the stage-rule path converges to a fixed point `z₁₀ = σ(z₁₀, 0)`, then
`z ≤ max 0 (z₁₀ − L/(M − r))`.
Scope: general class (any `Params` with a continuous static selector; a limit comparison). -/
theorem rulePathF_limit_le_of_shadow [p.StaticSelectorContinuous] {R : ℝ → ℝ}
    {L M rl dl : ℝ} (hL : 0 ≤ L) (hM : 0 < M) (hrl : rl < M) (hdl : 0 < dl)
    (hSlo : Sanctions.TransitionChords.SanctionLowerChord p.F dl)
    (hRmem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR : ∀ x ∈ Sanctions.I, R x ≤ max 0 (p.σ x 0 - L / M))
    (hmono : MonotoneOn (fun x => p.σ x 0) Sanctions.I)
    (hband : ∀ x ∈ Sanctions.I, ∀ x' ∈ Sanctions.I, x ≤ x' →
      rl / M * (x' - x) ≤ p.σ x' 0 - p.σ x 0)
    {x₀ z z₁₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    (htend : Tendsto (p.rulePathF R x₀) atTop (𝓝 z))
    (htend₁₀ : Tendsto (p.rulePathF (fun x => p.σ x 0) x₀) atTop (𝓝 z₁₀))
    (hfix₁₀ : p.σ z₁₀ 0 = z₁₀) :
    z ≤ max 0 (z₁₀ - L / (M - rl)) := by
  have hc : 0 ≤ L / M := div_nonneg hL hM.le
  have hmemR := p.rulePathF_mem_I hRmem hx₀
  have hmem₁₀ := p.rulePathF_mem_I (fun x _ => p.σ_mem x 0) hx₀
  have hz : z ∈ Sanctions.I := isClosed_Icc.mem_of_tendsto htend (Eventually.of_forall hmemR)
  have hz₁₀ : z₁₀ ∈ Sanctions.I :=
    isClosed_Icc.mem_of_tendsto htend₁₀ (Eventually.of_forall hmem₁₀)
  have hzz : z ≤ z₁₀ := le_of_tendsto_of_tendsto' htend htend₁₀
    (p.rulePathF_le_stagePath_of_shadow hc hRmem hR hmono hx₀)
  -- the shadow rule and its closed loop
  set ρ : ℝ → ℝ := fun x => max 0 (p.σ x 0 - L / M) with hρ_def
  have hσc : Continuous (fun x => p.σ x 0) :=
    p.σ_continuous.comp (continuous_id.prodMk continuous_const)
  have hρc : Continuous ρ := continuous_const.max (hσc.sub continuous_const)
  have hρI : ∀ x, ρ x ∈ Sanctions.I := fun x =>
    ⟨le_max_left _ _, max_le zero_le_one (by linarith [(p.σ_mem x 0).2])⟩
  have hstep : ∀ t, p.rulePathF R x₀ (t + 1)
      ≤ p.F (p.rulePathF R x₀ t) (ρ (p.rulePathF R x₀ t)) := by
    intro t
    rw [rulePathF_succ]
    exact p.F_mono_s _ (hR _ (hmemR t))
  have hnext : Tendsto (fun t => p.rulePathF R x₀ (t + 1)) atTop (𝓝 z) :=
    htend.comp (tendsto_add_atTop_nat 1)
  have hloop : Tendsto (fun t => p.F (p.rulePathF R x₀ t) (ρ (p.rulePathF R x₀ t)))
      atTop (𝓝 (p.F z (ρ z))) := by
    have hcl : Continuous (fun x => p.F x (ρ x)) :=
      p.F_continuous.comp (continuous_id.prodMk hρc)
    exact (hcl.tendsto z).comp htend
  have hzF : z ≤ p.F z (ρ z) := le_of_tendsto_of_tendsto' hnext hloop hstep
  -- the sanction chord forces `z ≤ ρ z`
  have hzρ : z ≤ ρ z := by
    by_contra hlt
    have hlt' : ρ z < z := not_le.mp hlt
    have hch := hSlo hz (hρI z) hz hlt'.le
    rw [p.F_diag z] at hch
    nlinarith [mul_pos hdl (show 0 < z - ρ z by linarith)]
  rcases le_total (p.σ z 0 - L / M) 0 with hneg | hpos
  · have : ρ z = 0 := max_eq_left hneg
    rw [this] at hzρ
    exact hzρ.trans (le_max_left _ _)
  · have hρz : ρ z = p.σ z 0 - L / M := max_eq_right hpos
    rw [hρz] at hzρ
    have hb := hband z hz z₁₀ hz₁₀ hzz
    rw [hfix₁₀] at hb
    refine le_trans ?_ (le_max_right _ _)
    have hMr : 0 < M - rl := by linarith
    -- `(M − r)(z₁₀ − z) ≥ L`
    have hkey : L ≤ (M - rl) * (z₁₀ - z) := by
      have e1 : rl / M * (z₁₀ - z) * M = rl * (z₁₀ - z) := by field_simp
      have e2 : L / M * M = L := by field_simp
      have h1 : z * M ≤ (p.σ z 0 - L / M) * M := mul_le_mul_of_nonneg_right hzρ hM.le
      have h2 : rl / M * (z₁₀ - z) * M ≤ (z₁₀ - p.σ z 0) * M :=
        mul_le_mul_of_nonneg_right hb hM.le
      nlinarith [h1, h2, e1, e2]
    have : L / (M - rl) ≤ z₁₀ - z := by rw [div_le_iff₀ hMr]; linarith
    linarith

/-- **From a common start the state path of every full-defiance equilibrium with a hostile
stake lies below the path under the stage rule (N10(b))**, at every date. The stage rule
`σ(·,0)` is the realised rule of the Target-only case (case 10); its monotonicity, not the
forward-looking response's, carries the comparison. Hypotheses as in
`hostileRule_le_stage_sub_wedge`, plus a nondecreasing stage rule.
The stake bound is uniform in the sanction.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 3. -/
theorem hostilePath_le_stagePath (E : p.FeedbackStackelbergEquilibriumTop)
    (hdef : ∀ x ∈ Sanctions.S, E.α x = 0) {w gl dl M : ℝ} (hw : 0 ≤ w)
    (hβgl : p.β_S * gl < 1)
    (hU : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ 0 s - p.U_S y₁ 0 s ≤ -(w * (y₂ - y₁)))
    (hF : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s)
    (hSlo : Sanctions.TransitionChords.SanctionLowerChord p.F dl) (hM : 0 < M)
    (hconv : ∀ x ∈ Sanctions.I,
      Sanctions.Semiconcave.SemiconvexOnSet (fun s => p.U_S x 0 s) (Set.Icc (0 : ℝ) 1) M)
    (hσ1 : ∀ x ∈ Sanctions.I, p.σ x 0 < 1)
    (hL : 0 < p.β_S * (w / (1 - p.β_S * gl)) * dl)
    (hmono : MonotoneOn (fun x => p.σ x 0) Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, p.rulePathF (p.dynamicEquilibriumRule E) x₀ t
      ≤ p.rulePathF (fun x => p.σ x 0) x₀ t :=
  p.rulePathF_le_stagePath_of_shadow (div_nonneg hL.le hM.le)
    (fun x _ => p.dynamicTopRealizedRule_mem E.V_S E.α x)
    (fun _ hx => p.hostileRule_le_stage_sub_wedge E hdef hw hβgl hU hF hSlo hM hconv hσ1 hL hx)
    hmono hx₀

/-- **The realised sanctions of every full-defiance equilibrium with a hostile stake lie below
the stage-rule sanctions less the wedge (N10(c))**: from a common start, at every date,
`s¹¹_t ≤ max 0 (s¹⁰_t − β_S·ḡ_S·d_lo/M)` with `s¹⁰_t = σ(x¹⁰_t, 0)`.
The stake bound is uniform in the sanction.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 3. -/
theorem hostileSanction_le_stage_sub_wedge (E : p.FeedbackStackelbergEquilibriumTop)
    (hdef : ∀ x ∈ Sanctions.S, E.α x = 0) {w gl dl M : ℝ} (hw : 0 ≤ w)
    (hβgl : p.β_S * gl < 1)
    (hU : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ 0 s - p.U_S y₁ 0 s ≤ -(w * (y₂ - y₁)))
    (hF : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s)
    (hSlo : Sanctions.TransitionChords.SanctionLowerChord p.F dl) (hM : 0 < M)
    (hconv : ∀ x ∈ Sanctions.I,
      Sanctions.Semiconcave.SemiconvexOnSet (fun s => p.U_S x 0 s) (Set.Icc (0 : ℝ) 1) M)
    (hσ1 : ∀ x ∈ Sanctions.I, p.σ x 0 < 1)
    (hL : 0 < p.β_S * (w / (1 - p.β_S * gl)) * dl)
    (hmono : MonotoneOn (fun x => p.σ x 0) Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    (t : ℕ) :
    p.dynamicEquilibriumRule E (p.rulePathF (p.dynamicEquilibriumRule E) x₀ t)
      ≤ max 0 (p.σ (p.rulePathF (fun x => p.σ x 0) x₀ t) 0
          - p.β_S * (w / (1 - p.β_S * gl)) * dl / M) :=
  p.ruleSanction_le_stage_sub_of_shadow (div_nonneg hL.le hM.le)
    (fun x _ => p.dynamicTopRealizedRule_mem E.V_S E.α x)
    (fun _ hx => p.hostileRule_le_stage_sub_wedge E hdef hw hβgl hU hF hSlo hM hconv hσ1 hL hx)
    hmono hx₀ t

/-- **Every limit of a full-defiance path with a hostile stake lies below the stage limit less
the long-run gap (N10(d)).** Under the hypotheses of `hostilePath_le_stagePath`, a continuous
static selector, a sanction chord `d_lo > 0` and the stage rule's lower slope band `r/M`
(`r < M`): if from a common start the path of the equilibrium converges to `z` and the
stage-rule path to a fixed point `z₁₀ = σ(z₁₀, 0)`, then
`z ≤ max 0 (z₁₀ − β_S·ḡ_S·d_lo/(M − r))`. The convergence of the hostile path is assumed, not
proved.
The stake bound is uniform in the sanction.
Scope: rare case: hostile Sender (hypotheses 3–4); uses approved hypothesis 3. -/
theorem hostileLimit_le_stageLimit_sub_gap [p.StaticSelectorContinuous]
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hdef : ∀ x ∈ Sanctions.S, E.α x = 0) {w gl dl M rl : ℝ} (hw : 0 ≤ w)
    (hβgl : p.β_S * gl < 1)
    (hU : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      p.U_S y₂ 0 s - p.U_S y₁ 0 s ≤ -(w * (y₂ - y₁)))
    (hF : ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s)
    (hSlo : Sanctions.TransitionChords.SanctionLowerChord p.F dl) (hdl : 0 < dl)
    (hM : 0 < M) (hrl : rl < M)
    (hconv : ∀ x ∈ Sanctions.I,
      Sanctions.Semiconcave.SemiconvexOnSet (fun s => p.U_S x 0 s) (Set.Icc (0 : ℝ) 1) M)
    (hσ1 : ∀ x ∈ Sanctions.I, p.σ x 0 < 1)
    (hL : 0 < p.β_S * (w / (1 - p.β_S * gl)) * dl)
    (hmono : MonotoneOn (fun x => p.σ x 0) Sanctions.I)
    (hband : ∀ x ∈ Sanctions.I, ∀ x' ∈ Sanctions.I, x ≤ x' →
      rl / M * (x' - x) ≤ p.σ x' 0 - p.σ x 0)
    {x₀ z z₁₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    (htend : Tendsto (p.rulePathF (p.dynamicEquilibriumRule E) x₀) atTop (𝓝 z))
    (htend₁₀ : Tendsto (p.rulePathF (fun x => p.σ x 0) x₀) atTop (𝓝 z₁₀))
    (hfix₁₀ : p.σ z₁₀ 0 = z₁₀) :
    z ≤ max 0 (z₁₀ - p.β_S * (w / (1 - p.β_S * gl)) * dl / (M - rl)) :=
  p.rulePathF_limit_le_of_shadow hL.le hM hrl hdl hSlo
    (fun x _ => p.dynamicTopRealizedRule_mem E.V_S E.α x)
    (fun _ hx => p.hostileRule_le_stage_sub_wedge E hdef hw hβgl hU hF hSlo hM hconv hσ1 hL hx)
    hmono hband hx₀ htend htend₁₀ hfix₁₀

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
