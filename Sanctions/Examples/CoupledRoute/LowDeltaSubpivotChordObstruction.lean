/-
Sanctions/Examples/CoupledRoute/LowDeltaSubpivotChordObstruction.lean

**Why the coupled-existence route cannot reach the persistence theorem at this
economy — a Rule-11 refutation artifact (2026-08-13).**

The low-δ campaign in this directory pursued a *coupled equilibrium existence*
result, on the understanding that once the equilibrium was constructed the
P4-free persistence route (`Theory/Certificates/SenderPersistencePackage.lean`)
would take over. This file records, machine-checked, that the second half of
that plan cannot succeed at the mechanism-witness stage payoffs — whatever
happens to the first half.

The obstruction is in **P5**, `SenderPersistencePackage.sender_subpivot_chord`:
the transition-adjusted sub-pivot chord, which says the Sender's stage gain from
raising the sanction across the sub-pivot range strictly exceeds the worst
continuation loss its carrier's Lipschitz bound `K_S` permits. P5 supplies the
*level* half of persistence — it is what puts the Sender's greatest response at
or above the pivot.

Three facts, in order.

1. `mwU_S_pivot_chord` computes the chord exactly. Its slope is
   `(3/20)x − 1/10 − a/2 + (3/5)t`.

2. `mw_pivot_chord_slope_eq_curvature_mul_vertex_gap` identifies that slope's
   `t → 0` limit as `(6/5) · (vertex − x)`, where `6/5 = −∂²U_S/∂s²` is the
   Sender's stage curvature and `(9/8)x − 1/12 − (5/12)a` is the argument of
   `mwσ`'s clip — the Sender's unconstrained static vertex. So **P5 says exactly
   that the Sender's own unconstrained optimum lies strictly above the inherited
   state.** That is the ratchet itself, stated as a stage-payoff inequality; it
   involves no continuation value and no `δ` beyond the `β_S·K_S·δ` bar.

3. Hence P5 caps compliance: `mw_subpivot_chord_forces_slope_ceiling`, and at
   the top state `mw_subpivot_chord_forces_compliance_ceiling_at_one` gives
   `a ≤ 1/10`. But this economy's own static Stackelberg policy — already proved
   optimal here in `lowDeltaStaticTargetPolicy_isMaxOn` — is `63/116 ≈ 0.5431`
   at `x = 1`, five times the ceiling. `mw_subpivot_chord_fails_at_static_policy`
   turns that into a refutation: at that compliance level **no** `K_S ≥ 0`
   satisfies the chord, so P5 is unavailable at any Sender carrier whatever.

## Scope — what this does and does not settle

It is **route-scoped in the same sense as the rest of this directory** (see
`README.md`). It refutes P5 at the *static* Target policy, which is the `δ → 0`
limit of the equilibrium policy, and therefore refutes the P5 half of the
persistence route at these stage payoffs. It does **not** claim that no coupled
equilibrium exists here, and it does not touch P1–P3.

Nor does it condemn the mechanism. The identity in (2) shows precisely what
would have to change: `∂²U_S/∂s∂x − (−∂²U_S/∂s²) = 27/20 − 6/5 = 3/20` is the
economy's rally-minus-curvature margin, and `3/20` is simply too small against
the intercept `1/10` and the equilibrium compliance. A witness with a larger
margin satisfies P5 with the sanction strictly interior at every state below the
top; that this is possible is what the corner-vs-interior corollary below
records.

## A corollary worth stating separately

`mw_subpivot_chord_at_one_forces_corner`: at `x = 1` with pivot `1`, P5 forces
the Sender's vertex to or above `1`, i.e. `mwσ 1 a = 1`. So P5
**pins the sanction to the corner at the top state** — but the identity in (2)
constrains no other state, so `σ(x) < 1` remains available for every `x < 1`.
An equilibrium path started below the top is therefore interior and strictly
rising at every finite date, with the corner only as its limit. The referee's
objection that the project's primitive theorem is "a corner equilibrium in which
sanctions equal one at every date" is **not** forced by P5.

## Rule compliance

**Rule 3.** No new assumption. Every statement below is either an algebraic
identity in the existing primitives or a consequence of a hypothesis that is
already a field of `SenderPersistencePackage`.
**Rule 11.** This file is the Lean artifact backing the "the low-δ route cannot
reach persistence" verdict; the verdict is not asserted in prose alone.
**Rule 22.** `lowDeltaParams.F` is affine, and the chord's distance factor is
computed at that instance; the algebraic content (1)–(2) is transition-free, and
section 5 holds for every transition.
**Rule 5.** Section 5 re-derives the refutation from the parametric
`Params.subpivot_chord_at_top_forces_corner`, with no coefficient algebra; the
coefficient sections are kept because they exhibit the *margin*, which is what
identifies the fix.

**Round BJ1.3 (2026-10-07).** P5 is now the pivot-star chord on the basin. The
coefficient sections already argue from star-shaped chords (from `x − t` up to
the pivot `x`), and the top state lies in every basin, so they refute the new P5
as they stand; section 5 adds the star-form sibling
`lowDelta_subpivot_star_chord_fails_at_top` beside the pairwise refutation.
-/

import Sanctions.Examples.CoupledRoute.LowDeltaStaticStackelberg
import Sanctions.Theory.Certificates.SubpivotChordNecessity

namespace Sanctions
namespace Examples

open Set

/-! ## 1. The sub-pivot chord, exactly -/

/-- **Exact value of the mechanism-witness Sender chord at the pivot.**

Between `s₁ = x - t` and `s₂ = x`, the stage gain is `t` times an affine
expression in `t`. Everything downstream is a consequence of this identity. -/
theorem mwU_S_pivot_chord (x a t : ℝ) :
    mwU_S x a x - mwU_S x a (x - t)
      = t * ((3 / 20) * x - 1 / 10 - a / 2 + (3 / 5) * t) := by
  unfold mwU_S
  ring

/-! ## 2. The chord slope IS the vertex gap -/

/-- **The chord's limiting slope is the Sender's stage curvature times the gap
between its unconstrained vertex and the inherited state.**

`6/5 = -∂²U_S/∂s²` is the curvature; `(9/8)x - 1/12 - (5/12)a` is the argument of
`mwσ`'s clip, i.e. the unconstrained static vertex. So the P5 chord condition
says exactly: *the Sender's own optimum lies above the state.* -/
theorem mw_pivot_chord_slope_eq_curvature_mul_vertex_gap (x a : ℝ) :
    (3 / 20) * x - 1 / 10 - a / 2
      = (6 / 5) * (((9 / 8) * x - 1 / 12 - (5 / 12) * a) - x) := by
  ring

/-! ## 3. P5 caps compliance -/

/-- **The sub-pivot chord forces a ceiling on its own slope constant.**

If every chord from `x - t` up to `x` beats `c · t`, then `c` is at most the
limiting slope. This is the `t → 0` limit of `mwU_S_pivot_chord`, taken without
any analysis beyond `le_of_forall_pos_le_add`. -/
theorem mw_subpivot_chord_forces_slope_ceiling
    {x a c : ℝ} (hx : 0 < x)
    (hchord : ∀ t : ℝ, 0 < t → t ≤ x → c * t < mwU_S x a x - mwU_S x a (x - t)) :
    c ≤ (3 / 20) * x - 1 / 10 - a / 2 := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have ht0 : 0 < min x (5 * ε / 3) := lt_min hx (by linarith)
  have htx : min x (5 * ε / 3) ≤ x := min_le_left _ _
  have hte : min x (5 * ε / 3) ≤ 5 * ε / 3 := min_le_right _ _
  have h := hchord _ ht0 htx
  rw [mwU_S_pivot_chord] at h
  have hlt :
      c < (3 / 20) * x - 1 / 10 - a / 2 + (3 / 5) * min x (5 * ε / 3) := by
    refine lt_of_mul_lt_mul_right ?_ (le_of_lt ht0)
    calc c * min x (5 * ε / 3)
        < min x (5 * ε / 3) *
            ((3 / 20) * x - 1 / 10 - a / 2 + (3 / 5) * min x (5 * ε / 3)) := h
      _ = ((3 / 20) * x - 1 / 10 - a / 2 + (3 / 5) * min x (5 * ε / 3)) *
            min x (5 * ε / 3) := by ring
  linarith

/-- **At the top state the ceiling is `1/10`.**

P5 at `x = 1` with pivot `1`, at any nonnegative chord constant `c`
(`c = β_S · K_S · δ` in the package), forces Target compliance below `1/10`. -/
theorem mw_subpivot_chord_forces_compliance_ceiling_at_one
    {a c : ℝ} (hc : 0 ≤ c)
    (hchord : ∀ t : ℝ, 0 < t → t ≤ 1 → c * t < mwU_S 1 a 1 - mwU_S 1 a (1 - t)) :
    a ≤ 1 / 10 := by
  have h := mw_subpivot_chord_forces_slope_ceiling (x := 1) one_pos hchord
  linarith

/-- **P5 at the top state pins the sanction to the corner there — and only
there.**

The Sender's unconstrained vertex at `x = 1` exceeds `1`, so `mwσ 1 a = 1`. The
identity `mw_pivot_chord_slope_eq_curvature_mul_vertex_gap` constrains no other
state, so this says nothing about `σ(x)` for `x < 1`. -/
theorem mw_subpivot_chord_at_one_forces_corner
    {a c : ℝ} (hc : 0 ≤ c)
    (hchord : ∀ t : ℝ, 0 < t → t ≤ 1 → c * t < mwU_S 1 a 1 - mwU_S 1 a (1 - t)) :
    mwσ 1 a = 1 := by
  have ha : a ≤ 1 / 10 := mw_subpivot_chord_forces_compliance_ceiling_at_one hc hchord
  have hv : (1 : ℝ) ≤ (9 / 8) * 1 - 1 / 12 - (5 / 12) * a := by linarith
  unfold mwσ
  have : (1 : ℝ) ≤ min 1 ((9 / 8) * 1 - 1 / 12 - (5 / 12) * a) := le_min le_rfl hv
  have h1 : min (1 : ℝ) ((9 / 8) * 1 - 1 / 12 - (5 / 12) * a) = 1 :=
    le_antisymm (min_le_left _ _) this
  rw [h1]
  exact max_eq_right (by norm_num)

/-! ## 4. The refutation at this economy's own optimal static policy -/

/-- The economy's static Stackelberg Target policy at the top state is
`63/116 ≈ 0.5431`. -/
theorem lowDeltaStaticTargetPolicy_at_one :
    lowDeltaStaticTargetPolicy 1 = 63 / 116 := by
  rw [lowDeltaStaticTargetPolicy_eq]
  norm_num

/-- **P5 fails at this economy, at its own optimal static Target policy.**

At `x = 1` the static Stackelberg compliance is `63/116`, which exceeds the
`1/10` ceiling by a factor of more than five. So there is **no** nonnegative
chord constant — hence no Sender carrier Lipschitz bound `K_S ≥ 0`, at any `δ` —
for which the sub-pivot chord holds. The `t → 0` slope is `1/20 - 63/232 =
-257/1160 < 0`: the Sender's stage payoff is *decreasing* in the sanction at the
pivot, so the Sender does not want to hold the sanction up at all.

Rule 9 note: this refutes P5 at the **static** policy, which is proved optimal
here (`lowDeltaStaticTargetPolicy_isMaxOn`) and is the `δ → 0` limit of the
equilibrium policy. That the *dynamic* equilibrium compliance is likewise far
above `1/10` at every `δ` is numerical evidence, recorded in the round entry —
not proved here, and not claimed. -/
theorem mw_subpivot_chord_fails_at_static_policy :
    ¬ ∃ c : ℝ, 0 ≤ c ∧
        ∀ t : ℝ, 0 < t → t ≤ 1 →
          c * t < mwU_S 1 (lowDeltaStaticTargetPolicy 1) 1 -
                    mwU_S 1 (lowDeltaStaticTargetPolicy 1) (1 - t) := by
  rintro ⟨c, hc, hchord⟩
  rw [lowDeltaStaticTargetPolicy_at_one] at hchord
  have := mw_subpivot_chord_forces_compliance_ceiling_at_one (a := 63 / 116) hc hchord
  linarith

/-- The failure margin, exactly: the limiting chord slope at the static policy is
`-257/1160`, strictly negative. -/
theorem mw_pivot_chord_slope_at_static_policy :
    (3 / 20 : ℝ) * 1 - 1 / 10 - (63 / 116) / 2 = -257 / 1160 := by
  norm_num

/-! ## 5. The same refutation, from the parametric necessary condition

The section above argues from the mechanism-witness coefficients. The same
conclusion follows with no coefficient algebra at all, from
`Params.subpivot_chord_at_top_forces_corner`
(`Theory/Certificates/SubpivotChordNecessity.lean`): P5 at the top state forces
the Sender's *stage* argmax to the corner, because the chord makes `U_S` still
rising there. Here that argmax is `1135/1392`, so the chord cannot hold. Rule 5:
the witness statement is a corollary, not a separate argument. -/

/-- The Sender's static response to the static Stackelberg compliance at the top
state is `1135/1392 ≈ 0.8154` — strictly interior, hence strictly below the
corner P5 would force. -/
theorem mwσ_at_one_static_policy : mwσ 1 (63 / 116) = 1135 / 1392 := by
  unfold mwσ
  norm_num

/-- **The refutation, route-independent.**

P5 at the top state of `lowDeltaParams` would force `σ 1 a = 1`
(`Params.subpivot_chord_at_top_forces_corner`). At this economy's own optimal
static compliance `63/116` the stage argmax is `1135/1392 < 1`. So no
nonnegative Sender-carrier Lipschitz bound `K_S` satisfies the chord — for any
transition and any `δ`, since neither enters the argument. -/
theorem lowDelta_subpivot_chord_fails_at_top :
    ¬ ∃ K_S : ℝ, 0 ≤ K_S ∧
        ∀ s₁ ∈ Set.Icc (0 : ℝ) 1, ∀ s₂ ∈ Set.Icc (0 : ℝ) 1, s₁ < s₂ →
          lowDeltaParams.β_S * K_S *
              dist (Sanctions.clipS' (lowDeltaParams.F 1 s₁))
                (Sanctions.clipS' (lowDeltaParams.F 1 s₂))
            < lowDeltaParams.U_S 1 (63 / 116) s₂ -
                lowDeltaParams.U_S 1 (63 / 116) s₁ := by
  rintro ⟨K_S, hK, hchord⟩
  have hcorner :=
    Sanctions.AbstractGame.Params.subpivot_chord_at_top_forces_corner
      lowDeltaParams hK hchord
  rw [show lowDeltaParams.σ = mwσ from rfl, mwσ_at_one_static_policy] at hcorner
  norm_num at hcorner

/-- **The refutation in P5's pivot-star form (round BJ1.3, 2026-10-07).**
Since round BJ1.3 the package's P5 is the pivot-star chord on the basin: at the
top state `x = 1` (which lies in every basin) the pivot is `1`, and P5 asks only
that moving from each sanction below `1` up to `1` beat the continuation
allowance. That weaker condition still forces the Sender's stage argmax to the
corner (`Params.subpivot_star_chord_forces_static_response_ge_pivot`), and at
this economy's optimal static compliance `63/116` the argmax is
`1135/1392 < 1`. So the refutation survives the weakening: no nonnegative
Sender-carrier Lipschitz bound `K_S` satisfies even the star chord, for any
transition and any `δ`. General in `F`: neither enters the argument. -/
theorem lowDelta_subpivot_star_chord_fails_at_top :
    ¬ ∃ K_S : ℝ, 0 ≤ K_S ∧
        ∀ s₁ ∈ Set.Ico (0 : ℝ) 1,
          lowDeltaParams.β_S * K_S *
              dist (Sanctions.clipS' (lowDeltaParams.F 1 s₁))
                (Sanctions.clipS' (lowDeltaParams.F 1 1))
            < lowDeltaParams.U_S 1 (63 / 116) 1 -
                lowDeltaParams.U_S 1 (63 / 116) s₁ := by
  rintro ⟨K_S, hK, hstar⟩
  have hge :=
    Sanctions.AbstractGame.Params.subpivot_star_chord_forces_static_response_ge_pivot
      lowDeltaParams zero_le_one le_rfl hK hstar
  rw [show lowDeltaParams.σ = mwσ from rfl, mwσ_at_one_static_policy] at hge
  norm_num at hge

/-- **The mechanism-witness Sender payoff IS the quadratic family**, at
curvature `c = 6/5`, rally `r = 27/20`, intercept `u0 = 1/10`, placation
`w = 1/2`, state stake `q = 2/5`. Its rally-minus-curvature margin is therefore
`27/20 - 6/5 = 3/20` — the number that fails the design screen
`Params.quadSenderVertex_ge_state_iff`. -/
theorem mwU_S_eq_quadSenderPayoff (x a s : ℝ) :
    mwU_S x a s
      = Sanctions.AbstractGame.Params.quadSenderPayoff
          (6 / 5) (27 / 20) (1 / 10) (1 / 2) (2 / 5) x a s := by
  unfold mwU_S Sanctions.AbstractGame.Params.quadSenderPayoff
  ring

/-- The witness's clipped static response is the clipped family vertex. -/
theorem mwσ_eq_clip_quadSenderVertex (x a : ℝ) :
    mwσ x a
      = max 0 (min 1 (Sanctions.AbstractGame.Params.quadSenderVertex
          (6 / 5) (27 / 20) (1 / 10) (1 / 2) x a)) := by
  unfold mwσ Sanctions.AbstractGame.Params.quadSenderVertex
  have h : (27 / 20 * x - 1 / 10 - 1 / 2 * a) / (6 / 5)
      = 9 / 8 * x - 1 / 12 - 5 / 12 * a := by ring
  rw [h]

end Examples
end Sanctions
