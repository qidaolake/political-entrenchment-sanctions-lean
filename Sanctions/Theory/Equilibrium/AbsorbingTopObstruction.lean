/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Theory.Basin.JointPreferenceBasin

/-!
# The absorbing-top obstruction (general form)

**Rule-5 generalization (2026-07-29) of the witness result recorded as R6.**

At the top state `x = 1` the transition is absorbing under the maximal
sanction, because `F_diag` is a `Params` field: `F 1 1 = 1` holds for *every*
economy in this model class, with no hypothesis. That single fact drives a
general obstruction, stated here over an arbitrary `p : Params` with no
reference to any witness economy, any specific transition, or any specific
payoff.

## The two halves

`corner_isMaxOn_of_slope` — the **pin**. Suppose the Sender's continuation
value rises to the top state at rate at least `m`; shading the sanction below
the corner by `1 - s` pushes the successor state down from the top by at least
`κ (1 - s)`; and the Sender's *static* gain from that shading is at most
`c (1 - s)`. If the static gain is dominated by the discounted continuation
loss, `c ≤ β_S · m · κ`, then the corner sanction `1` is a global dynamic
maximizer at the top state.

`target_deviation_of_pinned` — the **deviation**. If the Sender's greatest
dynamic response is pinned at `1` at two Target actions, then the successor
state is the *same term* at both, so the continuation `β_T · V_T (…)` cancels
identically and the Target's ranking is decided by its stage payoff alone.
This half needs **no** hypothesis on `F`, on `U_S`, or on `V_T`.

`no_equilibrium_of_slope_and_top_gain` — the **obstruction**. Combining them:
no feedback Stackelberg equilibrium exists whose Sender value has a positive
slope to the top and whose Target strictly gains, at the corner sanction, by
raising its action above `α 1`.

## What it says economically

A Sender that values the entrenched state sanctions at the corner once the
state is absorbing. But sanctioning at the corner means the successor state no
longer responds to the Target's action — the state is already at its ceiling.
That frees the Target to move its action without any continuation consequence,
so its choice is decided purely by the stage payoff. If the stage payoff
rewards moving, the policy was not optimal.

The Sender's own forward-looking motive is therefore **self-defeating at the
absorbing state**: the harder it pushes to hold the top state, the less the
state responds to the Target, and the freer the Target becomes.

## Scope

The constants are the assumption surface and they are all *parametric*: `m` is
a slope of the Sender value, `κ` a transition responsiveness at the top, `c` a
static shading bound, and the binding condition is the single strict inequality
`c ≤ β_S · m · κ` among quantities that already exist. No new named primitive
is introduced, and nothing here is a field of `Params`.

The obstruction is stated at the top state `x = 1`. Nothing is claimed about
interior states.

`Sanctions/Examples/NonAffineSenderStakeRefutation` specializes this at the
non-affine mechanism-active economy with `m = c` (the Sender's stake), `κ =
49/100` (the quadratic-bump transition's top responsiveness), and shading
bound `t/2`, recovering the witness refutation as a corollary.
-/

namespace Sanctions
namespace AbstractGame
namespace AbsorbingTop

open Set AbstractGame AbstractGame.Params

noncomputable section

variable (p : AbstractGame.Params)

/-! ## 1. The deviation half — fully general, no hypothesis on `F`, `U_S`, `V_T`. -/

/-- **Absorbing-top deviation.**  If the Sender's greatest dynamic response is
pinned at the corner `1` at two Target actions, the continuation term is
literally the same term at both, so the Target's ranking is decided by the
stage payoff alone. -/
theorem target_deviation_of_pinned
    (V_T V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (a₀ a₁ : ℝ) (ha₁ : a₁ ∈ Sanctions.I)
    (h0 : p.σ_dyn_top V_S 1 a₀ = 1)
    (h1 : p.σ_dyn_top V_S 1 a₁ = 1)
    (hgain : p.U_T 1 a₀ 1 < p.U_T 1 a₁ 1) :
    ¬ IsMaxOn (fun a => p.joint_T_top_integrand V_T V_S 1 a) Sanctions.I a₀ := by
  intro hcon
  rw [isMaxOn_iff] at hcon
  have h := hcon a₁ ha₁
  simp only [AbstractGame.Params.joint_T_top_integrand] at h
  rw [h0, h1] at h
  linarith

/-! ## 2. The pin half — general slope / transition / shading constants. -/

/-- **Absorbing-top corner pin.**  Hypotheses, in words:

* `hslope` — the Sender value rises to the top state at rate at least `m`;
* `htrans` — shading the sanction by `1 - s` moves the successor state down
  from the top by at least `κ (1 - s)`;
* `hshade` — the Sender's *static* gain from shading is at most `c (1 - s)`;
* `hc` — the static shading gain is dominated by the discounted continuation
  loss, `c ≤ β_S · m · κ`.

Then the corner sanction `1` is a global dynamic maximizer at the top state. -/
theorem corner_isMaxOn_of_slope
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (a m κ c : ℝ) (hm : 0 ≤ m)
    (one : ↥(Sanctions.S : Set ℝ)) (hone : one.val = 1)
    (hslope : ∀ y : ↥(Sanctions.S : Set ℝ), m * (1 - y.val) ≤ V_S one - V_S y)
    (htrans : ∀ s ∈ Sanctions.I, κ * (1 - s) ≤ 1 - p.F 1 s)
    (hshade : ∀ s ∈ Sanctions.I, p.U_S 1 a s - p.U_S 1 a 1 ≤ c * (1 - s))
    (hc : c ≤ p.β_S * m * κ) :
    IsMaxOn (fun s' => p.U_S 1 a s'
      + p.β_S * V_S (Sanctions.clipS' (p.F 1 s'))) Sanctions.I 1 := by
  have honeI : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hβS : 0 ≤ p.β_S := p.β_S_mem.1
  have hclipone : Sanctions.clipS' (1 : ℝ) = one :=
    Subtype.ext (by rw [Sanctions.clipS'_val_eq_of_mem honeI, hone])
  rw [isMaxOn_iff]
  intro s hs
  have hu0 : 0 ≤ 1 - s := by linarith [hs.2]
  -- successor state at the corner is the top itself
  have hFdiag : p.F 1 1 = 1 := p.F_diag 1
  have hFmem : p.F 1 s ∈ Set.Icc (0 : ℝ) 1 := p.F_mem 1 s honeI hs
  have hval : (Sanctions.clipS' (p.F 1 s)).val = p.F 1 s :=
    Sanctions.clipS'_val_eq_of_mem hFmem
  have hsl := hslope (Sanctions.clipS' (p.F 1 s))
  rw [hval] at hsl
  have htr := htrans s hs
  have hsh := hshade s hs
  -- m·κ·(1-s) ≤ m·(1 - F 1 s) ≤ V_S one - V_S (successor)
  have hchain : m * (κ * (1 - s)) ≤ V_S one - V_S (Sanctions.clipS' (p.F 1 s)) := by
    have : m * (κ * (1 - s)) ≤ m * (1 - p.F 1 s) := by
      exact mul_le_mul_of_nonneg_left htr hm
    linarith
  have hβchain : c * (1 - s) ≤ p.β_S * (V_S one - V_S (Sanctions.clipS' (p.F 1 s))) := by
    have h1 : c * (1 - s) ≤ (p.β_S * m * κ) * (1 - s) :=
      mul_le_mul_of_nonneg_right hc hu0
    have h2 : (p.β_S * m * κ) * (1 - s) ≤ p.β_S * (m * (κ * (1 - s))) := by ring_nf; linarith
    have h3 : p.β_S * (m * (κ * (1 - s)))
        ≤ p.β_S * (V_S one - V_S (Sanctions.clipS' (p.F 1 s))) :=
      mul_le_mul_of_nonneg_left hchain hβS
    linarith
  rw [hFdiag, hclipone]
  linarith

/-- Package the pin as an identity for the *greatest* dynamic response. -/
theorem sigma_dyn_top_eq_one_of_isMaxOn
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (a : ℝ)
    (hmax : IsMaxOn (fun s' => p.U_S 1 a s'
      + p.β_S * V_S (Sanctions.clipS' (p.F 1 s'))) Sanctions.I 1) :
    p.σ_dyn_top V_S 1 a = 1 := by
  have honeI : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hmem : (1 : ℝ) ∈ p.dynamicArgmaxSet V_S 1 a := ⟨honeI, hmax⟩
  refine le_antisymm ?_ ?_
  · exact csSup_le ⟨1, hmem⟩ (fun b hb => hb.1.2)
  · exact le_csSup (p.dynamicArgmaxSet_bddAbove V_S 1 a) hmem

/-! ## 3. The obstruction: no equilibrium whose policy sits below the gain. -/

/-- **Absorbing-top obstruction, general form.**  If a feedback Stackelberg
equilibrium's Sender value rises to the top state at a positive rate `m`, the
transition responds to sanction shading at rate `κ`, the Sender's static
shading gain is at most `c (1 - s)` with `c ≤ β_S m κ`, and the Target strictly
gains at the top state by raising its action from `α 1` to `α 1 + t` against the
corner sanction — then no such equilibrium exists.

The economic content: a Sender that values the top state sanctions at the
corner there, which frees the Target to move without changing the successor
state; if the Target's stage payoff rewards that move, the policy cannot have
been optimal. -/
theorem no_equilibrium_of_slope_and_top_gain
    (E : p.FeedbackStackelbergEquilibriumTop)
    (m κ c t : ℝ) (hm : 0 ≤ m)
    (one : ↥(Sanctions.S : Set ℝ)) (hone : one.val = 1)
    (hslope : ∀ y : ↥(Sanctions.S : Set ℝ), m * (1 - y.val) ≤ E.V_S one - E.V_S y)
    (htrans : ∀ s ∈ Sanctions.I, κ * (1 - s) ≤ 1 - p.F 1 s)
    (hshade0 : ∀ s ∈ Sanctions.I,
      p.U_S 1 (E.α 1) s - p.U_S 1 (E.α 1) 1 ≤ c * (1 - s))
    (hshade1 : ∀ s ∈ Sanctions.I,
      p.U_S 1 (E.α 1 + t) s - p.U_S 1 (E.α 1 + t) 1 ≤ c * (1 - s))
    (hc : c ≤ p.β_S * m * κ)
    (hdev : E.α 1 + t ∈ Sanctions.I)
    (hgain : p.U_T 1 (E.α 1) 1 < p.U_T 1 (E.α 1 + t) 1) : False := by
  have honeS : (1 : ℝ) ∈ Sanctions.S := ⟨by norm_num, le_refl 1⟩
  have h0 : p.σ_dyn_top E.V_S 1 (E.α 1) = 1 :=
    sigma_dyn_top_eq_one_of_isMaxOn p E.V_S (E.α 1)
      (corner_isMaxOn_of_slope p E.V_S (E.α 1) m κ c hm one hone hslope htrans
        hshade0 hc)
  have h1 : p.σ_dyn_top E.V_S 1 (E.α 1 + t) = 1 :=
    sigma_dyn_top_eq_one_of_isMaxOn p E.V_S (E.α 1 + t)
      (corner_isMaxOn_of_slope p E.V_S (E.α 1 + t) m κ c hm one hone hslope htrans
        hshade1 hc)
  exact target_deviation_of_pinned p E.V_T E.V_S (E.α 1) (E.α 1 + t) hdev h0 h1
    hgain (E.α_opt_top 1 honeS)

/-! ## The ratchet floor forces an absorbing top

This is the sharpest and most general form of the frontier: it needs no slope
condition, no curvature, no payoff structure, and no hypothesis on `V_T` or
`V_S`.  It is pure feasibility plus `F_diag`.
-/

/-- **The strong ratchet floor pins the top sanction at the corner.**  Any rule
that satisfies `max x sbar ≤ r x` on an upper interval ending at `1`, and is
feasible at `1`, must have `r 1 = 1`.  Evaluating the floor at the top state
already forces it. -/
theorem rule_top_eq_one_of_floor
    (r : ℝ → ℝ) {xbar sbar : ℝ} (hxbar : xbar ≤ 1) (hfeas : r 1 ≤ 1)
    (h_floor : ∀ x ∈ Set.Icc xbar 1, max x sbar ≤ r x) :
    r 1 = 1 :=
  le_antisymm hfeas
    (le_trans (le_max_left 1 sbar) (h_floor 1 ⟨hxbar, le_rfl⟩))

/-- **Hence the realized successor at the top state is the top state itself.**
The transition's diagonal condition `F x x = x` is a maintained field of
`Params`, so no additional hypothesis is required. -/
theorem successor_top_eq_one_of_floor
    (r : ℝ → ℝ) {xbar sbar : ℝ} (hxbar : xbar ≤ 1) (hfeas : r 1 ≤ 1)
    (h_floor : ∀ x ∈ Set.Icc xbar 1, max x sbar ≤ r x) :
    p.F 1 (r 1) = 1 := by
  rw [rule_top_eq_one_of_floor r hxbar hfeas h_floor]
  exact p.F_diag 1

/-- **The ratchet dichotomy.**  For any feasible rule and any upper interval
ending at the top state, exactly one of the following holds:

* the top sanction is *interior* (`r 1 < 1`), and then the strong ratchet floor
  fails on that interval --- indeed on every such interval; or
* the top sanction is at the corner (`r 1 = 1`), and then the realized successor
  at the top state is the top state itself, so the Target's continuation term
  there is `β_T V_T 1` whatever the rule does elsewhere.

There is no third case.  This is why maximal ratcheting and a live Target
continuation channel at the top state cannot be had together: the floor that
delivers the first *is* what produces the second. -/
theorem ratchet_dichotomy
    (r : ℝ → ℝ) {xbar sbar : ℝ} (hxbar : xbar ≤ 1) (hfeas : r 1 ≤ 1) :
    (r 1 < 1 ∧ ¬ ∀ x ∈ Set.Icc xbar 1, max x sbar ≤ r x)
      ∨ (r 1 = 1 ∧ p.F 1 (r 1) = 1) := by
  rcases lt_or_eq_of_le hfeas with hlt | heq
  · exact Or.inl ⟨hlt, Sanctions.no_upper_basin_floor_of_top_lt_one r hlt hxbar⟩
  · exact Or.inr ⟨heq, by rw [heq]; exact p.F_diag 1⟩

/-- Specialization to an equilibrium's own realized rule, where feasibility is
automatic from `dynamicTopRealizedRule_mem`. -/
theorem equilibrium_successor_top_eq_one_of_floor
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar sbar : ℝ} (hxbar : xbar ≤ 1)
    (h_floor : ∀ x ∈ Set.Icc xbar 1,
      max x sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x) :
    p.F 1 (p.dynamicTopRealizedRule E.V_S E.α 1) = 1 :=
  successor_top_eq_one_of_floor p _ hxbar
    (p.dynamicTopRealizedRule_mem E.V_S E.α 1).2 h_floor

/-! ## Axiom hygiene (Rule 10) -/

#print axioms target_deviation_of_pinned
#print axioms corner_isMaxOn_of_slope
#print axioms sigma_dyn_top_eq_one_of_isMaxOn
#print axioms no_equilibrium_of_slope_and_top_gain
#print axioms rule_top_eq_one_of_floor
#print axioms successor_top_eq_one_of_floor
#print axioms ratchet_dichotomy
#print axioms equilibrium_successor_top_eq_one_of_floor

end

end AbsorbingTop
end AbstractGame
end Sanctions
