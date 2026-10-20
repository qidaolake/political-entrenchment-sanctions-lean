/-
Sanctions/Theory/Basin/PrimitiveHighBasin.lean

**Primitive-discharge layer for the high-sanction basin.**

The basin Prop `OneSidedSanctionPreferenceThresholds` requires:

* `target_likes_high_sanctions`: `s ↦ U_T(x, α x, s) + β_T · V_T(F(x, s))`
  is monotone non-decreasing on `[max x sbar, 1]`;
* `sender_likes_to_threshold`: `s ↦ U_S(x, α x, s) + β_S · V_S(F(x, s))`
  is strictly increasing on `[0, max x sbar]`.

The existing `of_stage_preferences` discharger lifts these from
*stage* monotonicity together with the **strong** assumption that the
continuation values `V_T` and `V_S` are themselves monotone on `↥S`.
The `Monotone V_T` assumption is the load-bearing piece a referee will
challenge: it bundles the conclusion of a forward-looking dynamic
analysis into a continuation-value monotonicity hypothesis.

This file removes the `Monotone V_T` requirement: under a primitive
**stage-payoff finite-difference margin** `m` and a **continuation-value
Lipschitz constant** `K`, satisfying the margin inequality

```
β · K · δ ≤ m         (Target, weak)
β · K · δ < m         (Sender, strict)
```

the dynamic objective inherits the monotonicity / strict monotonicity
from the stage objective. Concretely, for `s₁ ≤ s₂` on the threshold
range,

```
(stage U_T at s₂) − (stage U_T at s₁)         ≥ m · (s₂ − s₁)
(continuation V_T at F(s₂)) − (... at F(s₁)) ≥ −K · δ · (s₂ − s₁)
```

(the first bound is the `LowerSlopeOn` hypothesis; the second follows
from value-Lipschitz plus the 1-Lipschitz of `clipS'` and the
δ-Lipschitz of `s ↦ (1 − δ) x + δ s`). Summing and discounting,

```
(dynamic obj at s₂) − (dynamic obj at s₁) ≥ (m − β · K · δ) (s₂ − s₁)
```

which is `≥ 0` under the margin inequality.

This replaces a continuation-value postulate with a primitive
stage-payoff slope versus a primitive value-Lipschitz constant — the
right shape for an economically interpretable assumption.

All hypotheses are theorem-parameter primitives; no new fields are
added to `AbstractGame.Params`.
-/

import Sanctions.Theory.Basin.JointPreferenceBasin
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. Primitive predicates -/

/-- **Finite-difference lower-slope predicate.** A real-valued
function `f` has lower slope at least `m` on `D` if, for every
ordered pair `s₁ ≤ s₂` in `D`, the secant difference `f s₂ − f s₁` is
bounded below by `m · (s₂ − s₁)`. This is a finite-difference
(no-derivative) restatement of "`f' ≥ m` on `D`" and the right
primitive for discharging a high-basin sanction-preference. -/
def LowerSlopeOn (f : ℝ → ℝ) (D : Set ℝ) (m : ℝ) : Prop :=
  ∀ s₁ ∈ D, ∀ s₂ ∈ D, s₁ ≤ s₂ → m * (s₂ - s₁) ≤ f s₂ - f s₁

/-- **Value-Lipschitz predicate.** A BCF value function `V` on `↥S`
is `K`-Lipschitz if the secant absolute difference of `V` is bounded
by `K · dist`. This is a finite-difference (no-derivative) Lipschitz
restatement and is the right primitive for bounding adverse
continuation-value movements. -/
def ValueLipschitzWith
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (K : ℝ) : Prop :=
  ∀ y₁ y₂ : ↥(Sanctions.S : Set ℝ),
    |V y₂ - V y₁| ≤ K * dist y₁ y₂

/-- **A value-Lipschitz modulus over `S` is automatically nonnegative.**

`S = [0,1]` has two points at distance `1`, so the defining inequality at that
pair reads `|V 1 - V 0| ≤ K`, and the left side is a modulus. No hypothesis is
needed: any `K` that works at all is already nonnegative. -/
theorem ValueLipschitzWith.nonneg
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {K : ℝ} (h : ValueLipschitzWith V K) :
    0 ≤ K := by
  have h01 := h ⟨0, by simp⟩ ⟨1, by simp⟩
  have hd : dist (⟨0, by simp⟩ : ↥(Sanctions.S : Set ℝ)) ⟨1, by simp⟩ = 1 := by
    rw [Subtype.dist_eq]
    simp [Real.dist_eq]
  rw [hd, mul_one] at h01
  exact le_trans (abs_nonneg _) h01

/-- **Inherited-state regularity of the transition.**
`TransitionStateLipschitzWith γ_F` says that, holding the current
sanction fixed, a difference in inherited political states can change
the next state by at most `γ_F` times that difference.

This is the optional quantitative general-`F` counterpart of the
affine persistence coefficient `1 - δ`. It strengthens continuity and
monotonicity in the state coordinate, but is not part of the baseline
`Params` structure or of `StrictAdjustment`. -/
def TransitionStateLipschitzWith (γ_F : ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, ∀ s ∈ Sanctions.I,
    |p.F x₂ s - p.F x₁ s| ≤ γ_F * |x₂ - x₁|

/-- **Inherited-state regularity on the physical square** (doc 68, L6). The
same modulus, quantified over feasible inherited states only. This is the
condition the manuscript states as (F6-Q), and the one the Sender value-Lipschitz
route actually consumes: the Bellman estimate compares the operator at two
feasible states, and the successor states it feeds the value are feasible. The
global form above implies it; the converse fails, and the cube extension of
`Postulates/ParamsOfCube` does **not** carry a modulus below one outside the
square (`F̂(x, 0) = x` for `x < 0`), so a paper condition stated on the square
must be consumed on the square. -/
def TransitionStateLipschitzOnWith (γ_F : ℝ) : Prop :=
  ∀ x₁ ∈ Sanctions.I, ∀ x₂ ∈ Sanctions.I, ∀ s ∈ Sanctions.I,
    |p.F x₂ s - p.F x₁ s| ≤ γ_F * |x₂ - x₁|

/-- The global form restricts to the physical form. -/
theorem TransitionStateLipschitzWith.toOn {γ_F : ℝ}
    (h : p.TransitionStateLipschitzWith γ_F) : p.TransitionStateLipschitzOnWith γ_F :=
  fun x₁ _ x₂ _ s hs => h x₁ x₂ s hs

/-- **Monotonicity of `ValueLipschitzWith` in the Lipschitz constant.**
A `K`-Lipschitz value function is also `K'`-Lipschitz for any
`K' ≥ K`. Audit-45 Step 2: used to remove a per-equilibrium
value-Lipschitz hypothesis (`hV_S_lip_E` in the `valLipBall` route)
by replacing it with the scalar comparison `K_V ≤ KS`. -/
theorem ValueLipschitzWith.mono_constant
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {K K' : ℝ}
    (h : ValueLipschitzWith V K) (hK_le : K ≤ K') :
    ValueLipschitzWith V K' := by
  intro y₁ y₂
  have hdist_nonneg : 0 ≤ dist y₁ y₂ := dist_nonneg
  exact le_trans (h y₁ y₂)
    (mul_le_mul_of_nonneg_right hK_le hdist_nonneg)

/-! ## 2. Stage→dynamic lifting under primitive margins

The two pivotal theorems: the dynamic Target objective is monotone
when the stage slope dominates the discounted Lipschitz loss; the
dynamic Sender objective is strictly monotone under the strict version
of the same inequality. -/


/-- **General-`F` Sender strict monotonicity from an exact
transition-adjusted stage chord.**

For every ordered sanction pair, suppose the stage-payoff increase
strictly exceeds the worst possible discounted continuation loss,
measured using the actual transition displacement

`β_S * K * dist (clipS' (F x s₁)) (clipS' (F x s₂))`.

If the Sender value is `K`-Lipschitz, this exact chord condition makes
the full dynamic objective strictly increasing. No affine transition
and no additional Lipschitz modulus for `F` is assumed. -/
theorem senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {x sbar K : ℝ}
    (h_transition_adjusted_chord :
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
        ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar), s₁ < s₂ →
          p.β_S * K *
              dist (Sanctions.clipS' (p.F x s₁))
                   (Sanctions.clipS' (p.F x s₂))
            < p.U_S x (α x) s₂ - p.U_S x (α x) s₁)
    (hV_lip : ValueLipschitzWith V_S K) :
    StrictMonoOn
      (fun s => p.senderDynObjective V_S x (α x) s)
      (Set.Icc (0 : ℝ) (max x sbar)) := by
  intro s₁ hs₁ s₂ hs₂ hlt
  let y₁ := Sanctions.clipS' (p.F x s₁)
  let y₂ := Sanctions.clipS' (p.F x s₂)
  have hV_abs : |V_S y₂ - V_S y₁| ≤ K * dist y₁ y₂ := by
    simpa [y₁, y₂, abs_sub_comm] using hV_lip y₁ y₂
  have hV_lower : -(K * dist y₁ y₂) ≤ V_S y₂ - V_S y₁ := by
    linarith [neg_abs_le (V_S y₂ - V_S y₁)]
  have hβV_lower :
      -(p.β_S * K * dist y₁ y₂)
        ≤ p.β_S * (V_S y₂ - V_S y₁) := by
    calc
      -(p.β_S * K * dist y₁ y₂) =
          p.β_S * (-(K * dist y₁ y₂)) := by ring
      _ ≤ p.β_S * (V_S y₂ - V_S y₁) :=
        mul_le_mul_of_nonneg_left hV_lower p.β_S_mem.1
  have hstage :
      p.β_S * K * dist y₁ y₂ <
        p.U_S x (α x) s₂ - p.U_S x (α x) s₁ := by
    simpa [y₁, y₂] using
      h_transition_adjusted_chord s₁ hs₁ s₂ hs₂ hlt
  change p.U_S x (α x) s₁ + p.β_S * V_S y₁ <
    p.U_S x (α x) s₂ + p.β_S * V_S y₂
  linarith

/-- **Pivot-star form** (round M, doc 82 P3; the reader's round-I plan §6): one
comparison per sub-pivot sanction, against the pivot `max x sbar`, is enough for
the forward-looking objective at the pivot to beat every sanction below it —
which is what the basin object consumes. The pairwise chord above implies this
input (take `s₂ := max x sbar`); nothing here compares two sub-pivot sanctions
with each other. -/
theorem senderDynObjective_lt_pivot_of_star_chord_and_V_lipschitz
    {V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ}
    {x sbar K : ℝ}
    (h_star_chord :
      ∀ s₁ ∈ Set.Ico (0 : ℝ) (max x sbar),
        p.β_S * K *
            dist (Sanctions.clipS' (p.F x s₁))
                 (Sanctions.clipS' (p.F x (max x sbar)))
          < p.U_S x (α x) (max x sbar) - p.U_S x (α x) s₁)
    (hV_lip : ValueLipschitzWith V_S K) :
    ∀ s₁ ∈ Set.Ico (0 : ℝ) (max x sbar),
      p.senderDynObjective V_S x (α x) s₁
        < p.senderDynObjective V_S x (α x) (max x sbar) := by
  intro s₁ hs₁
  let y₁ := Sanctions.clipS' (p.F x s₁)
  let y₂ := Sanctions.clipS' (p.F x (max x sbar))
  have hV_abs : |V_S y₂ - V_S y₁| ≤ K * dist y₁ y₂ := by
    simpa [y₁, y₂, abs_sub_comm] using hV_lip y₁ y₂
  have hV_lower : -(K * dist y₁ y₂) ≤ V_S y₂ - V_S y₁ := by
    linarith [neg_abs_le (V_S y₂ - V_S y₁)]
  have hβV_lower :
      -(p.β_S * K * dist y₁ y₂)
        ≤ p.β_S * (V_S y₂ - V_S y₁) := by
    calc
      -(p.β_S * K * dist y₁ y₂) =
          p.β_S * (-(K * dist y₁ y₂)) := by ring
      _ ≤ p.β_S * (V_S y₂ - V_S y₁) :=
        mul_le_mul_of_nonneg_left hV_lower p.β_S_mem.1
  have hstage :
      p.β_S * K * dist y₁ y₂ <
        p.U_S x (α x) (max x sbar) - p.U_S x (α x) s₁ := by
    simpa [y₁, y₂] using h_star_chord s₁ hs₁
  change p.U_S x (α x) s₁ + p.β_S * V_S y₁ <
    p.U_S x (α x) (max x sbar) + p.β_S * V_S y₂
  linarith

/-- **The exact transition-adjusted chord also implies strict stage
monotonicity when its continuation-loss allowance is non-negative.**

If `β_S ≥ 0` and `K ≥ 0`, the term
`β_S * K * dist (F(x,s₁)) (F(x,s₂))` is non-negative. Therefore a
stage-payoff chord that strictly exceeds this term is itself strictly
positive. This helper lets the general-`F` exact chord discharge the
low-range stage-monotonicity field of the slim MS certificate as well
as the dynamic-objective field above. -/
theorem stageSenderObjective_strictMono_of_transition_adjusted_chord
    {α : ℝ → ℝ}
    {x K : ℝ}
    {D : Set ℝ}
    (hβ_S_nn : 0 ≤ p.β_S)
    (hK_nn : 0 ≤ K)
    (h_transition_adjusted_chord :
      ∀ s₁ ∈ D, ∀ s₂ ∈ D, s₁ < s₂ →
        p.β_S * K *
            dist (Sanctions.clipS' (p.F x s₁))
                 (Sanctions.clipS' (p.F x s₂))
          < p.U_S x (α x) s₂ - p.U_S x (α x) s₁) :
    StrictMonoOn (fun s => p.U_S x (α x) s) D := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have h_allowance_nn :
      0 ≤ p.β_S * K *
        dist (Sanctions.clipS' (p.F x s₁))
             (Sanctions.clipS' (p.F x s₂)) := by
    positivity
  linarith [h_transition_adjusted_chord s₁ hs₁ s₂ hs₂ hlt]

/-- **General-`F` Sender sub-pivot chord from a sanction-side upper chord.**

Affine-free sibling of `sender_transition_adjusted_chord_of_affine_lowerSlope`
below.  The affine pin `hF` is deleted; in its place the transition enters
only through a chord *ceiling* on the sub-pivot sanction range at the state
`x` under consideration: raising the sanction by `Δ` moves next period's
political state by at most `d·Δ`, in absolute value.

Reading the hypotheses in English:

* `hF_chord` — on the sub-pivot range `[0, max x s̄]`, a unit of extra
  sanction displaces the next state by at most `d` (the transition's
  sanction-responsiveness ceiling at this state);
* `hmargin` — `β_S · K · d < m`: the Sender's per-period sanction-marginal
  welfare `m` strictly exceeds the worst discounted continuation loss the
  `K`-Lipschitz value can suffer from a displacement of rate `d`;
* `h_stage` — the Sender stage payoff has minimum upward sanction slope `m`
  on the sub-pivot range (`LowerSlopeOn`).

The hypothesis shape is ported from
`ShockedParams.senderDynObjective_shock_strictMonoOn_of_strong_rally_generalF`
(`Theory/Shocked/ShockedSingleCrossing.lean`) rather than from the
unit-square `Sanctions.TransitionChords.SanctionUpperChord`, and the choice
is load-bearing.  This theorem binds `{x sbar m K d : ℝ}` with **no** domain
hypothesis, exactly as the affine theorem it siblings does, and two of its
downstream consumers — `senderCombinedMonotoneOn_of_stage_lowerSlope_and_carrier_lipschitz`
and `ShockedParams.senderDynObjective_shock_strictMonoOn_of_strong_rally` —
bind `xT`, `xS` with no `∈ Sanctions.I` hypothesis and so cannot supply
`x ∈ [0,1]`.  A unit-square-scoped chord would be more general in `F` but
strictly less general in domain, and unusable there.

The margin is denominated in `d`, not in `p.δ`.  Under a general `F`, `p.δ`
is not the transition's adjustment rate and the substitution is not merely
uninterpretable but false: `Examples.qbParams_not_sanctionUpperChord_affine`
refutes the `p.δ` rate at the non-affine witness, whose actual ceiling is
`53/100 > 1/2`.  Compare the Target-side twin
`Target_combined_chord_of_decomposition_lowerChord`
(`Theory/Certificates/GeneralFDischargers.lean`), which denominates its
margin in the lower-chord rate `dlo` for the same reason.

No nonnegativity hypothesis on `d` is needed: `hF_chord` at any ordered
pair with `s₁ < s₂` already forces `0 ≤ d`. -/
theorem sender_transition_adjusted_chord_of_upperChordOn_lowerSlope
    {α : ℝ → ℝ}
    {x sbar m K d : ℝ}
    (hK_nonneg : 0 ≤ K)
    (hF_chord :
      ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
        ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar), s₁ ≤ s₂ →
          |p.F x s₂ - p.F x s₁| ≤ d * (s₂ - s₁))
    (hmargin : p.β_S * K * d < m)
    (h_stage :
      LowerSlopeOn
        (fun s => p.U_S x (α x) s)
        (Set.Icc (0 : ℝ) (max x sbar))
        m) :
    ∀ s₁ ∈ Set.Icc (0 : ℝ) (max x sbar),
      ∀ s₂ ∈ Set.Icc (0 : ℝ) (max x sbar), s₁ < s₂ →
        p.β_S * K *
            dist (Sanctions.clipS' (p.F x s₁))
                 (Sanctions.clipS' (p.F x s₂))
          < p.U_S x (α x) s₂ - p.U_S x (α x) s₁ := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hsdiff_pos : 0 < s₂ - s₁ := sub_pos.mpr hlt
  have hFdist :
      dist (Sanctions.clipS' (p.F x s₁))
           (Sanctions.clipS' (p.F x s₂))
        ≤ d * (s₂ - s₁) :=
    (Sanctions.clipS'_lipschitz_dist _ _).trans
      (by rw [abs_sub_comm]; exact hF_chord s₁ hs₁ s₂ hs₂ hlt.le)
  have hβK_nonneg : 0 ≤ p.β_S * K :=
    mul_nonneg p.β_S_mem.1 hK_nonneg
  have hdist_cost :
      p.β_S * K *
          dist (Sanctions.clipS' (p.F x s₁))
               (Sanctions.clipS' (p.F x s₂))
        ≤ p.β_S * K * (d * (s₂ - s₁)) :=
    mul_le_mul_of_nonneg_left hFdist hβK_nonneg
  have hmargin_pair :
      p.β_S * K * (d * (s₂ - s₁)) < m * (s₂ - s₁) := by
    nlinarith
  exact lt_of_lt_of_le (lt_of_le_of_lt hdist_cost hmargin_pair)
    (h_stage s₁ hs₁ s₂ hs₂ hlt.le)


/-- **Round-13 Priority 3: C¹ discharger for `LowerSlopeOn`.**
From a convex domain `D`, a pointwise derivative `f' s` of `f` at
every `s ∈ D` (via `HasDerivAt`), and a uniform lower bound
`m ≤ f' s` on `D`, conclude `LowerSlopeOn f D m`.

Economically: a stage payoff with derivative `∂U/∂s ≥ m` on the
domain rises in sanctions at rate at least `m`, which is exactly
what the discrete-chord `LowerSlopeOn` predicate says.

One-line application of mathlib's
`Convex.mul_sub_le_image_sub_of_le_deriv` specialized to `C := m`. -/
theorem LowerSlopeOn.of_hasDerivAt_lowerBound
    {f : ℝ → ℝ} {D : Set ℝ} {m : ℝ} {f' : ℝ → ℝ}
    (hD : Convex ℝ D)
    (hf_diff : ∀ s ∈ D, HasDerivAt f (f' s) s)
    (hf_lower : ∀ s ∈ D, m ≤ f' s) :
    LowerSlopeOn f D m := by
  intro s₁ hs₁ s₂ hs₂ hs_le
  have hf_contOn : ContinuousOn f D :=
    fun s hs => (hf_diff s hs).continuousAt.continuousWithinAt
  have hf_diffOn : DifferentiableOn ℝ f (interior D) := by
    intro s hs
    exact (hf_diff s (interior_subset hs)).differentiableAt.differentiableWithinAt
  have hf'_ge_deriv : ∀ s ∈ interior D, m ≤ deriv f s := by
    intro s hs
    have hd : deriv f s = f' s := (hf_diff s (interior_subset hs)).deriv
    rw [hd]; exact hf_lower s (interior_subset hs)
  exact hD.mul_sub_le_image_sub_of_le_deriv
    hf_contOn hf_diffOn hf'_ge_deriv s₁ hs₁ s₂ hs₂ hs_le

end Params
end AbstractGame

end

end Sanctions
