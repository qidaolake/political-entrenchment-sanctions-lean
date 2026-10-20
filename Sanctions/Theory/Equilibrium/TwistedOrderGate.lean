/-
Sanctions/Theory/Equilibrium/TwistedOrderGate.lean

**The mixed-monotone (twisted-order) route, gated.**

## The question this settles

The joint Bellman map `T = (T_T, T_S)` is not isotone under the *pointwise*
product order on value pairs — `LeaderArgmaxOrderRefutation.lean` shows the
leader's argmax moves the wrong way. But those refutations vary the Target
continuation `W_T` while holding the Sender continuation `W_S` **fixed**, so
they say nothing about a product order with the Sender coordinate **reversed**:

    (V_T, V_S) ≤tw (W_T, W_S)   iff   V_T ≤ W_T pointwise  and  W_S ≤ V_S pointwise.

Under `≤tw`, isotonicity of `T` needs four coordinate signs:

| tag | requirement | status here |
|---|---|---|
| G1 | `T_T` increasing in `V_T` | **holds** — `T_T_joint_mono_own_value` |
| G2 | `T_T` *decreasing* in `V_S` | **refuted** — `T_T_joint_lt_of_sender_value_raise` |
| G3 | `T_S` decreasing in `V_T` | not reached (G2 already closes the route) |
| G4 | `T_S` increasing in `V_S` | not reached |

Because G2 fails, `T` is not `≤tw`-isotone, and the Tarski/Knaster route on the
twisted order is closed for the unrestricted class. Rule 11 wanted the
refutation attempted before any construction; this is that attempt, and it
succeeded, so no complete-lattice carrier need be built.

## Why G2 fails, in words

`V_S` enters the Target's Bellman integrand *only* through the Sender's
best response `σ_dyn V_S x a` — the sanction the Sender picks when its own
continuation value is `V_S`. Raising the Sender's continuation makes the Sender
sanction **harder**. Two things then happen to the Target, and they point in
opposite directions:

* the Target's stage payoff falls, because it is being sanctioned more (rate
  `LT` below — the Target's stage loss per unit of extra sanction);
* the Target's *continuation* value rises, because a harsher sanction pushes
  next period's state up (chord rate `dS`) and the Target's value function
  climbs with the state (slope `gT`) — this is entrenchment, the model's whole
  subject.

When the second effect wins, the Target's Bellman value goes **up** in response
to a pointwise rise in `V_S`, which is the opposite of what G2 needs.

## The sharp part: it fails exactly where the model lives

The condition under which the second effect wins is

    LT < β_T · gT · dS

and that is not an exotic corner. It is the **strict form of the project's own
Target loss-offset margin**, `hT_loss_margin : cT ≤ p.β_T * gT * dlo`, consumed
by `Target_combined_chord_of_decomposition_lowerChord` in `GeneralFDischargers`
(and a field of `StandardComplianceLocalCoreCertificate` until round BJ1.4,
2026-10-07) — the hypothesis stating that the Target's current sanction loss rate is outweighed by
its discounted continuation-state gain. That margin is what makes lock-in work:
it is why the Target tolerates sanctions rather than complying.

So the twisted order does not fail on a pathology introduced to break it. It
fails *because* the economy is one in which the Target is entrenchment-seeking,
which is the only case the paper is about. Strengthening the hypotheses to
rescue the order would mean assuming the loss-offset margin away, and with it
the mechanism.

## Scope — what is and is not refuted (Rule 9A)

Refuted: that `T` is isotone under `≤tw` on the unrestricted value rectangle,
hence that Tarski/Knaster applies to it there.

**Not** refuted, and no reader may infer:

* **that no equilibrium exists.** This is a statement about one proof *route*.
  Existence is delivered elsewhere, by contraction — see
  `exists_equilibrium_basinTop_generalF_schur`.
* **that no carrier-local twisted order works.** The refutation is a
  *configuration*: two ordered Sender values at which the Sender's optimal
  response strictly shifts, a Target maximiser, the chord inequalities and a
  strict net-gain margin. It defeats antitonicity on any domain that contains
  that configuration, and says nothing about a carrier that does not — a
  carrier on which the margin is *reversed* (`β_T · gT · dS ≤ LT`), or on which
  the Sender's response does not move between the two values (a constant shift
  of `V_S` adds the action-independent term `β_S · c` and moves nothing), is
  untouched. It does *not* prove that every order-preserving carrier must
  exclude the loss-offset margin.
* **anything at `β_S = 0`.** There the Sender is myopic, `σ_dyn` does not depend
  on `V_S` at all (`senderDynObjective_eq_stage_of_βS_zero`,
  `Theory/Mechanism/RegimeSelectorBridge.lean`), so `T_T` is *constant* in `V_S`
  — trivially both isotone and antitone. Every counterexample below needs the
  Sender's response to actually move, which needs `β_S > 0`.

## Rule 3

No new assumption. `TwistedLE` is a definition, G1 is proved from `0 ≤ β_T`
alone, and every hypothesis of the refutation is a *theorem parameter scoping a
counterexample*, not a hypothesis of any downstream result — the same idiom as
`hplac` / `hvar` / `hgain` in `LeaderArgmaxOrderRefutation.lean`. `BddAbove` on
the integrand image is the house use-site parameter (cf.
`Theory/Bellman/GeneralFOperatorRow.lean:282`), discharged where continuity is
available.

## Rule 19

`Theory/`, not `Foundations/`: every statement is about `Params`, the Sender's
dynamic best response, and the Target's Bellman operator. The order relation
itself is three lines and carries no external theory worth factoring out.
-/

import Sanctions.Theory.Equilibrium.JointMPE
import Sanctions.Foundations.TransitionChords

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame

/-! ## 1. The twisted product order

Only the relation, as Rule 20's disprove-first gate asks: no global `Order`
instance is installed on raw function pairs, so nothing downstream can pick this
up by accident. -/

/-- **The twisted (mixed-monotone) product order on value pairs.** The Target
coordinate is ordered pointwise upward; the Sender coordinate is ordered
pointwise *downward*. This is the order under which a map that is increasing in
its own value and decreasing in its opponent's would be isotone. -/
def TwistedLE
    (z w : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) : Prop :=
  (∀ y, z.1 y ≤ w.1 y) ∧ (∀ y, w.2 y ≤ z.2 y)

theorem TwistedLE.refl (z : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) :
    TwistedLE z z :=
  ⟨fun _ => le_refl _, fun _ => le_refl _⟩

theorem TwistedLE.trans
    {z w v : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ)}
    (h₁ : TwistedLE z w) (h₂ : TwistedLE w v) : TwistedLE z v :=
  ⟨fun y => (h₁.1 y).trans (h₂.1 y), fun y => (h₂.2 y).trans (h₁.2 y)⟩

namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 2. G1 — the own-value sign holds

The Target's Bellman operator *is* monotone in the Target's own continuation
value. This half of the twisted order is free: the Sender's response
`σ_dyn V_S x a` does not depend on `V_T` at all, so raising `V_T` pointwise
raises the integrand at every action with the state left untouched, and the
supremum follows. -/

/-- **G1 — `T_T` is increasing in the Target's own continuation value.**

If `V_T ≤ W_T` pointwise then `T_T_joint V_T V_S x ≤ T_T_joint W_T V_S x`: the
Target's Bellman value rises when its own continuation rises. Needs only
`0 ≤ β_T` (a nonnegative Target discount factor).

`hbdd` — that the upper integrand's image over the action set is bounded above
— is the standard use-site parameter, discharged from continuity wherever the
Sender's argmax is unique. -/
theorem T_T_joint_mono_own_value
    {V_T W_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    (hβ : 0 ≤ p.β_T) (hle : ∀ y, V_T y ≤ W_T y) (x : ℝ)
    (hbdd : BddAbove ((fun a => p.joint_T_integrand W_T V_S x a) '' Sanctions.I)) :
    p.T_T_joint V_T V_S x ≤ p.T_T_joint W_T V_S x := by
  refine csSup_le ⟨p.joint_T_integrand V_T V_S x 0, ⟨0, by norm_num [Sanctions.I], rfl⟩⟩ ?_
  rintro b ⟨a, ha, rfl⟩
  have hstep :
      p.joint_T_integrand V_T V_S x a ≤ p.joint_T_integrand W_T V_S x a := by
    simp only [joint_T_integrand]
    have h := hle (Sanctions.clipS' (p.F x (p.σ_dyn V_S x a)))
    nlinarith [h, hβ]
  exact hstep.trans (le_csSup hbdd ⟨a, ha, rfl⟩)

/-! ## 3. G2 — the cross sign is refuted

The integrand-level statement first, then the operator-level one. -/

/-- **G2, at the integrand — raising the Sender's continuation raises the
Target's.**

Read the hypotheses economically, at a fixed state `x` and Target action `a`:

* `hstep` — the Sender's dynamic best response strictly *increases* when its
  continuation value is raised from `V_S` to `W_S`. (This is the live channel;
  it is empty at `β_S = 0`.)
* `hchord` — the transition has lower chord rate `dS` in the sanction: pushing
  the sanction up by `Δ` raises next period's state by at least `dS · Δ`. This
  is `SanctionLowerChord p.F dS` read at the two responses.
* `hslope` — the Target's value function climbs with the state at rate at least
  `gT` over that move (the entrenchment-seeking regime; cf.
  `LowerSlopeOnValueOn`).
* `hloss` — the Target's stage payoff falls by at most `LT` per unit of extra
  sanction.
* `hmargin` — `LT < β_T · gT · dS`: the discounted continuation gain strictly
  outweighs the stage loss. This is the **strict form of the loss-offset margin**
  `hT_loss_margin : cT ≤ p.β_T * gT * dlo` (a certificate field until round
  BJ1.4).

Conclusion: the Target's Bellman integrand is strictly **higher** under the
raised Sender value — the opposite of the sign the twisted order needs. -/
theorem joint_T_integrand_lt_of_sender_value_raise
    {V_T V_S W_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x a gT dS LT : ℝ}
    (hβ : 0 < p.β_T) (hgT : 0 ≤ gT)
    (hstep : p.σ_dyn V_S x a < p.σ_dyn W_S x a)
    (hchord : dS * (p.σ_dyn W_S x a - p.σ_dyn V_S x a)
                ≤ p.F x (p.σ_dyn W_S x a) - p.F x (p.σ_dyn V_S x a))
    (hslope : gT * (p.F x (p.σ_dyn W_S x a) - p.F x (p.σ_dyn V_S x a))
                ≤ V_T (Sanctions.clipS' (p.F x (p.σ_dyn W_S x a)))
                  - V_T (Sanctions.clipS' (p.F x (p.σ_dyn V_S x a))))
    (hloss : p.U_T x a (p.σ_dyn V_S x a) - p.U_T x a (p.σ_dyn W_S x a)
                ≤ LT * (p.σ_dyn W_S x a - p.σ_dyn V_S x a))
    (hmargin : LT < p.β_T * gT * dS) :
    p.joint_T_integrand V_T V_S x a < p.joint_T_integrand V_T W_S x a := by
  simp only [joint_T_integrand]
  have hΔ : 0 < p.σ_dyn W_S x a - p.σ_dyn V_S x a := by linarith
  -- the state moves up by at least `dS · Δ`, so the value climbs by at least `gT · dS · Δ`
  have h1 : gT * (dS * (p.σ_dyn W_S x a - p.σ_dyn V_S x a))
              ≤ gT * (p.F x (p.σ_dyn W_S x a) - p.F x (p.σ_dyn V_S x a)) :=
    mul_le_mul_of_nonneg_left hchord hgT
  -- discount it
  have h2 : p.β_T * (gT * (p.F x (p.σ_dyn W_S x a) - p.F x (p.σ_dyn V_S x a)))
              ≤ p.β_T * (V_T (Sanctions.clipS' (p.F x (p.σ_dyn W_S x a)))
                          - V_T (Sanctions.clipS' (p.F x (p.σ_dyn V_S x a)))) :=
    mul_le_mul_of_nonneg_left hslope hβ.le
  have h3 : p.β_T * (gT * (dS * (p.σ_dyn W_S x a - p.σ_dyn V_S x a)))
              ≤ p.β_T * (gT * (p.F x (p.σ_dyn W_S x a) - p.F x (p.σ_dyn V_S x a))) :=
    mul_le_mul_of_nonneg_left h1 hβ.le
  -- the margin is strict, so the net move is strictly positive
  have h4 : 0 < (p.β_T * gT * dS - LT) * (p.σ_dyn W_S x a - p.σ_dyn V_S x a) :=
    mul_pos (by linarith) hΔ
  nlinarith [h2, h3, h4, hloss]

/-- **G2, at the operator — `T_T` is NOT antitone in the Sender's value.**

Same hypotheses as the integrand version, plus: `a` attains the Target's Bellman
supremum under the lower Sender value (`hmax`, `ha`), and the upper integrand is
bounded above (`hbdd`). Conclusion: `T_T_joint V_T V_S x < T_T_joint V_T W_S x`
even though `V_S` sits pointwise below `W_S`. -/
theorem T_T_joint_lt_of_sender_value_raise
    {V_T V_S W_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x a gT dS LT : ℝ}
    (hβ : 0 < p.β_T) (hgT : 0 ≤ gT)
    (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => p.joint_T_integrand V_T V_S x b) Sanctions.I a)
    (hbdd : BddAbove ((fun b => p.joint_T_integrand V_T W_S x b) '' Sanctions.I))
    (hstep : p.σ_dyn V_S x a < p.σ_dyn W_S x a)
    (hchord : dS * (p.σ_dyn W_S x a - p.σ_dyn V_S x a)
                ≤ p.F x (p.σ_dyn W_S x a) - p.F x (p.σ_dyn V_S x a))
    (hslope : gT * (p.F x (p.σ_dyn W_S x a) - p.F x (p.σ_dyn V_S x a))
                ≤ V_T (Sanctions.clipS' (p.F x (p.σ_dyn W_S x a)))
                  - V_T (Sanctions.clipS' (p.F x (p.σ_dyn V_S x a))))
    (hloss : p.U_T x a (p.σ_dyn V_S x a) - p.U_T x a (p.σ_dyn W_S x a)
                ≤ LT * (p.σ_dyn W_S x a - p.σ_dyn V_S x a))
    (hmargin : LT < p.β_T * gT * dS) :
    p.T_T_joint V_T V_S x < p.T_T_joint V_T W_S x := by
  have hG : IsGreatest ((fun b => p.joint_T_integrand V_T V_S x b) '' Sanctions.I)
      (p.joint_T_integrand V_T V_S x a) := by
    refine ⟨⟨a, ha, rfl⟩, ?_⟩
    rintro c ⟨b, hb, rfl⟩
    exact hmax hb
  have hlt := p.joint_T_integrand_lt_of_sender_value_raise
    hβ hgT hstep hchord hslope hloss hmargin
  simp only [T_T_joint]
  rw [hG.csSup_eq]
  exact hlt.trans_le (le_csSup hbdd ⟨a, ha, rfl⟩)

/-! ## 4. The verdict

The universal that the twisted order would need, negated. -/

/-- **The mixed-monotone route is closed on the unrestricted rectangle.**

There is no economy-wide antitonicity of the Target's Bellman operator in the
Sender's continuation value: given a single configuration satisfying the
loss-offset margin strictly, the universal `∀ W_T V W, V ≤ W pointwise →
T_T W_T W ≤ T_T W_T V` is false. Since that universal is precisely the G2
coordinate sign of `≤tw`-isotonicity, `T` is not `≤tw`-isotone, and Tarski does
not apply to it on this domain.

Note what carries the refutation: `hmargin`, the strict loss-offset margin. The
route is not closed by a pathology — it is closed by the model's own lock-in
condition. -/
theorem not_antitone_T_T_joint_in_sender_value
    {V_T V_S W_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {x a gT dS LT : ℝ}
    (hβ : 0 < p.β_T) (hgT : 0 ≤ gT)
    (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => p.joint_T_integrand V_T V_S x b) Sanctions.I a)
    (hbdd : BddAbove ((fun b => p.joint_T_integrand V_T W_S x b) '' Sanctions.I))
    (hVW : ∀ y, V_S y ≤ W_S y)
    (hstep : p.σ_dyn V_S x a < p.σ_dyn W_S x a)
    (hchord : dS * (p.σ_dyn W_S x a - p.σ_dyn V_S x a)
                ≤ p.F x (p.σ_dyn W_S x a) - p.F x (p.σ_dyn V_S x a))
    (hslope : gT * (p.F x (p.σ_dyn W_S x a) - p.F x (p.σ_dyn V_S x a))
                ≤ V_T (Sanctions.clipS' (p.F x (p.σ_dyn W_S x a)))
                  - V_T (Sanctions.clipS' (p.F x (p.σ_dyn V_S x a))))
    (hloss : p.U_T x a (p.σ_dyn V_S x a) - p.U_T x a (p.σ_dyn W_S x a)
                ≤ LT * (p.σ_dyn W_S x a - p.σ_dyn V_S x a))
    (hmargin : LT < p.β_T * gT * dS) :
    ¬ (∀ (W_T V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ),
        (∀ y, V y ≤ W y) → ∀ z : ℝ, p.T_T_joint W_T W z ≤ p.T_T_joint W_T V z) := by
  intro h
  exact absurd (h V_T V_S W_S hVW x)
    (not_le.mpr (p.T_T_joint_lt_of_sender_value_raise
      hβ hgT ha hmax hbdd hstep hchord hslope hloss hmargin))

end Params
end AbstractGame

/-! ## 5. Rule 10 — axiom inventory

Both the positive sign and the refutation must stand on the standard three. -/

#print axioms Sanctions.AbstractGame.Params.T_T_joint_mono_own_value
#print axioms Sanctions.AbstractGame.Params.joint_T_integrand_lt_of_sender_value_raise
#print axioms Sanctions.AbstractGame.Params.T_T_joint_lt_of_sender_value_raise
#print axioms Sanctions.AbstractGame.Params.not_antitone_T_T_joint_in_sender_value

end -- noncomputable section

end Sanctions
