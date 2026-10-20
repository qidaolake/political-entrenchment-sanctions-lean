/-
Sanctions/Examples/AffineInstance/LockInShockedGeneralFBridge.lean

**The affine `V_S`-free sanction floor and its structural price are corollaries
of the general-transition theorems.**

Round BB, 2026-09-28; doc 110 item M1 (the Rule-5 half).

## What this file proves, in English

`Examples/AffineInstance/LockInShocked.lean` proves two Sender-side theorems
under the affine transition `F(x,s) = (1−δ)x + δs`:

* `V_S_free_sanction_floor` — a sanction floor `c ≤ R(x)` for the greatest
  forward-looking Sender best response against the constructed Sender value,
  from a stage state chord `m`, a stage sanction-loss rate `cS`, and the margin
  `cS·(1 − β_S(1−δ)) ≤ β_S·m·δ`;
* `no_top_gain_equilibrium_of_V_S_free_floor_condition` — the same condition,
  with one off-policy loss bound, rules out any equilibrium in which the Target
  strictly gains by deviating at the top state.

`Theory/LockIn/SenderSanctionFloorGeneralF.lean` proves both for an arbitrary
transition with a lower state chord `g_lo` and a lower sanction chord `d_lo`.
This file shows that the affine theorems are instances of those.  The price
and `via_chords` bridges are one line; `via_generalF` discharges the joint
chords from `hF` (about thirty lines, no re-proof of the argument):

* `affine_lower_state_chord` — the affine law has lower state chord `1 − δ`,
  at equality.  (Its lower sanction chord `δ` is the existing
  `affine_transitionChordPack`, `Examples/AffineInstance/Certificates.lean`.)
* `V_S_free_sanction_floor_via_generalF` — the affine floor, **with exactly the
  original's statement**, from the sign-free joint-chord form
  `V_S_free_sanction_floor_of_joint_chords`.  Covers every sign of `m`.
* `V_S_free_sanction_floor_via_chords` — the affine floor at `m ≥ 0` as a
  one-line instance of the named-chord form `V_S_free_sanction_floor_generalF`
  at `g_lo = 1 − δ`, `d_lo = δ`: the general margin
  `cS·(1 − β_S·g_lo) ≤ β_S·m·d_lo` *is* the affine margin there, verbatim.
* `no_top_gain_equilibrium_of_V_S_free_floor_condition_via_generalF` — the
  affine structural price, **with exactly the original's statement**, as a
  one-line instance of the general-`F` price theorem.

Two `example ... := rfl` checks confirm that the two `_via_generalF` theorems
have *definitionally the same statement* as the originals in
`LockInShocked.lean`, so the originals are recovered verbatim, not a variant.

## Scope (Rule 9)

Universal statements over every `Params` whose transition is affine; no witness.
The originals are not edited or retired: they stay where they are, and these
bridges sit beside them (Rule 5: the affine form is a corollary of the
parametric one).

## Rule 22

**Affine-restricted by construction**: every theorem here carries
`hF : p.F = affineF p.δ`, because its job is to recover the affine instance.
The general content lives in `Theory/LockIn/SenderSanctionFloorGeneralF.lean`.

## Rule 3

No new assumption.  Each bridge carries the affine original's hypotheses
exactly; `V_S_free_sanction_floor_via_chords` adds `0 ≤ m`, the sign the
named-chord form needs, and is a demonstration of the margin's coincidence,
not a replacement for `V_S_free_sanction_floor_via_generalF`, which needs no
sign.
-/

import Sanctions.Theory.LockIn.SenderSanctionFloorGeneralF
import Sanctions.Examples.AffineInstance.LockInShocked
import Sanctions.Examples.AffineInstance.Certificates

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **The affine law's lower state chord is `1 − δ`, at equality.**  Raising
the inherited state by `Δ` raises `(1−δ)x + δs` by exactly `(1−δ)·Δ`, at every
sanction.  Affine-restricted (Rule 22): this is the affine instance of the
lower state chord consumed by `V_S_free_sanction_floor_generalF`. -/
theorem affine_lower_state_chord
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ) :
    ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
      (1 - p.δ) * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s := by
  intro s _ y₁ _ y₂ _ _
  rw [hF]
  unfold Sanctions.AbstractGame.affineF
  exact le_of_eq (by ring)

/-- **The affine `V_S`-free sanction floor, recovered from the general-`F`
joint-chord theorem.**

Statement identical to `V_S_free_sanction_floor`
(`Examples/AffineInstance/LockInShocked.lean:397`) — checked by `rfl` below.
The proof instantiates `V_S_free_sanction_floor_of_joint_chords` at the
Benveniste–Scheinkman slope `g = m / (1 − β_S(1−δ))`: under the affine law the
state increment of `F` is exactly `(1−δ)·Δ` and the sanction increment exactly
`δ·Δ`, so both joint chords hold, the first by the cone identity
`m + β_S·g·(1−δ) = g` and the second by the affine margin.  No sign on `m` is
needed.  Affine-restricted (Rule 22). -/
theorem V_S_free_sanction_floor_via_generalF
    {α : ℝ → ℝ} (hα : Continuous α)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {m cS x c : ℝ}
    (hx : x ∈ Sanctions.I) (hc : c ∈ Sanctions.I)
    (h_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
    (h_sanction_loss :
      LowerLossSlopeOn (fun s => p.U_S x (α x) s) (Set.Icc (0 : ℝ) c) cS)
    (h_margin : cS * (1 - p.β_S * (1 - p.δ)) ≤ p.β_S * m * p.δ) :
    c ≤ p.dynamicTopRealizedRule (p.V_S α hα) α x := by
  have hpos := p.oneMinus_betaS_oneMinusDelta_pos
  set g : ℝ := Sanctions.StokeyLucas.bellmanLowerSlopeConstant p.β_S (1 - p.δ) m
    with hgdef
  have hid : m + p.β_S * g * (1 - p.δ) = g := p.lowerSlopeConstant_cone_identity m
  have hcS : cS ≤ p.β_S * g * p.δ := by
    rw [hgdef, Sanctions.StokeyLucas.bellmanLowerSlopeConstant_def,
      show p.β_S * (m / (1 - p.β_S * (1 - p.δ))) * p.δ
          = (p.β_S * m * p.δ) / (1 - p.β_S * (1 - p.δ)) from by ring,
      le_div_iff₀ hpos]
    exact h_margin
  refine p.V_S_free_sanction_floor_of_joint_chords (g := g) hα hx hc ?_
    h_sanction_loss ?_
  · -- the joint state chord at `g`, with equality in the transition term
    intro s hs y₁ hy₁ y₂ hy₂ hle
    have hU := h_state_slope s hs y₁ hy₁ y₂ hy₂ hle
    have hFd : p.F y₂ s - p.F y₁ s = (1 - p.δ) * (y₂ - y₁) := by
      rw [hF]; unfold Sanctions.AbstractGame.affineF; ring
    rw [hFd]
    have hid' : g * (y₂ - y₁)
        = m * (y₂ - y₁) + p.β_S * g * ((1 - p.δ) * (y₂ - y₁)) := by
      linear_combination (-(y₂ - y₁)) * hid
    linarith
  · -- the joint sanction chord at `g`, from the affine margin
    intro s₁ _ s₂ _ hle
    have hFd : p.F x s₂ - p.F x s₁ = p.δ * (s₂ - s₁) := by
      rw [hF]; unfold Sanctions.AbstractGame.affineF; ring
    rw [hFd]
    have h := mul_le_mul_of_nonneg_right hcS (sub_nonneg.mpr hle)
    linarith

/-- **The affine floor at `m ≥ 0` is the named-chord general-`F` floor at
`g_lo = 1 − δ`, `d_lo = δ`.**  One line: the affine law's two lower chords
(`affine_lower_state_chord`, `affine_transitionChordPack`) and the affine
margin, which is the general margin `cS·(1 − β_S·g_lo) ≤ β_S·m·d_lo` verbatim
at those rates.  Affine-restricted (Rule 22).  Carries `0 ≤ m`, which the
named-chord form needs; `V_S_free_sanction_floor_via_generalF` covers every
sign. -/
theorem V_S_free_sanction_floor_via_chords
    {α : ℝ → ℝ} (hα : Continuous α)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {m cS x c : ℝ} (hm : 0 ≤ m)
    (hx : x ∈ Sanctions.I) (hc : c ∈ Sanctions.I)
    (h_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (α y₂) s - p.U_S y₁ (α y₁) s)
    (h_sanction_loss :
      LowerLossSlopeOn (fun s => p.U_S x (α x) s) (Set.Icc (0 : ℝ) c) cS)
    (h_margin : cS * (1 - p.β_S * (1 - p.δ)) ≤ p.β_S * m * p.δ) :
    c ≤ p.dynamicTopRealizedRule (p.V_S α hα) α x :=
  p.V_S_free_sanction_floor_generalF hα hx hc hm h_state_slope
    (p.affine_lower_state_chord hF) (p.affine_transitionChordPack hF).1
    h_sanction_loss h_margin

/-- **The affine structural price, recovered from the general-`F` one.**

Statement identical to `no_top_gain_equilibrium_of_V_S_free_floor_condition`
(`Examples/AffineInstance/LockInShocked.lean:465`) — checked by `rfl` below.
One line: `no_top_gain_equilibrium_of_V_S_free_floor_condition_generalF` at the
affine law's lower chords `g_lo = 1 − δ` and `d_lo = δ`, where the general
margin is the affine margin verbatim.  Affine-restricted (Rule 22). -/
theorem no_top_gain_equilibrium_of_V_S_free_floor_condition_via_generalF
    (E : p.FeedbackStackelbergEquilibriumTop)
    (hF : p.F = Sanctions.AbstractGame.affineF p.δ)
    {m cS t : ℝ} (hm : 0 ≤ m)
    (h_state_slope :
      ∀ s ∈ Sanctions.I, ∀ y₁ ∈ Sanctions.S, ∀ y₂ ∈ Sanctions.S, y₁ ≤ y₂ →
        m * (y₂ - y₁) ≤ p.U_S y₂ (E.α y₂) s - p.U_S y₁ (E.α y₁) s)
    (h_loss0 : LowerLossSlopeOn (fun s => p.U_S 1 (E.α 1) s) (Set.Icc (0 : ℝ) 1) cS)
    (h_loss1 : LowerLossSlopeOn (fun s => p.U_S 1 (E.α 1 + t) s) (Set.Icc (0 : ℝ) 1) cS)
    (h_margin : cS * (1 - p.β_S * (1 - p.δ)) ≤ p.β_S * m * p.δ)
    (hdev : E.α 1 + t ∈ Sanctions.I)
    (hgain : p.U_T 1 (E.α 1) 1 < p.U_T 1 (E.α 1 + t) 1) : False :=
  p.no_top_gain_equilibrium_of_V_S_free_floor_condition_generalF E hm h_state_slope
    (p.affine_lower_state_chord hF) (p.affine_transitionChordPack hF).1
    h_loss0 h_loss1 h_margin hdev hgain

/-! ## The bridges have the originals' statements, definitionally -/

example : type_of% @Params.V_S_free_sanction_floor
    = type_of% @Params.V_S_free_sanction_floor_via_generalF := rfl

example : type_of% @Params.no_top_gain_equilibrium_of_V_S_free_floor_condition
    = type_of% @Params.no_top_gain_equilibrium_of_V_S_free_floor_condition_via_generalF :=
  rfl

end Params
end AbstractGame

end -- noncomputable section

end Sanctions

/-! ## Axiom hygiene (Rule 10) -/

-- The axiom report below names declarations in full; several names pass the
-- 100-character line limit, which is accepted for these report lines only.
set_option linter.style.longLine false

#print axioms Sanctions.AbstractGame.Params.affine_lower_state_chord
#print axioms Sanctions.AbstractGame.Params.V_S_free_sanction_floor_via_generalF
#print axioms Sanctions.AbstractGame.Params.V_S_free_sanction_floor_via_chords
#print axioms Sanctions.AbstractGame.Params.no_top_gain_equilibrium_of_V_S_free_floor_condition_via_generalF
