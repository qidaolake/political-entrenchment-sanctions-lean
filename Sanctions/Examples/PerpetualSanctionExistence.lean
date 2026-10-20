/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Examples.P3SpreadPinned
import Sanctions.Examples.B2GeneralFPersistenceWitness

/-!
# Perpetual sanctions exist: the existence form

Everywhere else in this development the strong dynamic conclusions are stated
*at a named economy* — "at `B₂` the sanction path is non-decreasing", "at `P₃`
it strictly increases". That phrasing invites the obvious objection: **why those
numbers?** The magnitudes of `b2Params` and `mechanismWitnessParams` are chosen,
not derived; only their *signs* are economics.

This file restates the same content in existential form, where the objection
does not arise:

  **there exist primitives** at which sanctions never end and never fall.

The tuned constants then live inside the *proof* rather than inside the *claim*.
This is the one use of a witness that Rule 5 endorses without reservation — an
existence certificate discharging non-vacuity of a parameter class, where one
cannot say "there exists `p`" without exhibiting one.

Nothing here is new mathematics. Every theorem is an existential introduction
over results already proved, and each is a short assembly. The value is entirely
in the logical form.

## The two statements, and why they differ

`exists_perfect_information_perpetual_sanctions` — the **perfect-information**
form. The transition of `b2Params` is the affine law with no smoothing operator
of any kind, which `b2_transition_is_deterministic` records by `rfl` rather than
by assertion. So the infinite-horizon feedback Stackelberg game there has
perfect information, and from *every* initial state in the high basin the
realised sanction never falls below `1/2 > 0` and the path is non-decreasing,
at every date, forever.

`exists_perpetually_escalating_sanctions` — the **strict-escalation** form. Here
the sanction path is `StrictMono`: strictly higher at every date, forever, and
never below `5/12 > 0`. But this economy is `mwShocked`, whose `smear` averages
the continuation value over noise (`smear V y = 𝔼_η[V(clipS'(y+η))]`), so it is
**not** a perfect-information game.

**In our two witnesses** the split runs as follows: the atomless shock purifies
the follower's response and permits an interior Target policy, and it is the
interior policy that makes the ratchet strict; in the deterministic witness the
Target sits at the stage-aligned corner and the ratchet is only weak.

That is a statement about *these two economies*, not a necessity theorem. **We
have not shown that perfect information precludes strict escalation** — no such
result is proved anywhere in this development, and the comparison above is
evidence for a mechanism, not a proof of one. Strict escalation under perfect
information is **open**.

## What "never ending" and "escalating" mean, exactly

Both are statements about the *realised equilibrium path*, with both governments
optimizing at every date: the Sender's sanction is the greatest maximizer of its
forward-looking objective, and the Target's action carries the equilibrium's
Bellman-optimality field. No behaviour is imposed.

"Never ending" is a strictly positive floor holding at every date — not merely
"does not converge to zero". "Escalating" is monotonicity of the path, and in
the shocked case strict monotonicity. Note that strict escalation is
nevertheless **bounded**: sanctions are feasible, so the path increases strictly
while converging, and no claim of unbounded escalation is made or could be.
-/

namespace Sanctions
namespace Examples

open Set

noncomputable section

/-! Existence form: rather than "this calibration escalates", state
"there EXIST primitives at which escalation occurs". The witness moves
inside the proof. -/

/-- **Perpetual escalating sanctions exist.**

There is an economy in the model class, an equilibrium of it, an initial
political state, and a strictly positive floor `sbar`, such that along the
realised equilibrium path, at every date `n`:

* the sanction never falls below `sbar > 0` --- sanctions never end; and
* the sanction is strictly greater than at date `n-1` --- they escalate; and
* the political state remains in the high basin.

Both players are optimizing at every date: the Sender's sanction is the
greatest maximizer of its forward-looking objective, and the Target's action
carries the equilibrium's Bellman-optimality field. Nothing is a fixed rule. -/
theorem exists_perpetually_escalating_sanctions :
    ∃ (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
      (x₀ sbar : ℝ),
      0 < sbar
      ∧ (∀ n, sbar ≤ mechanismWitnessParams.dynamicTopLockInSanctionsF
                (mwSenderValueOne E.V_S) E.α x₀ n)
      ∧ StrictMono (mechanismWitnessParams.dynamicTopLockInSanctionsF
                (mwSenderValueOne E.V_S) E.α x₀)
      ∧ (∀ n, mechanismWitnessParams.dynamicTopLockInPathF
                (mwSenderValueOne E.V_S) E.α x₀ n ∈ Set.Icc (2 / 5 : ℝ) 1) := by
  obtain ⟨-, hsanct, hpath⟩ :=
    p3_monotone_sanctions_from_rational_start (x₀ := 2 / 5)
      (by norm_num) (by norm_num)
  refine ⟨mwEqEquilibrium, 2 / 5, 5 / 12, by norm_num, ?_, hsanct, hpath⟩
  intro n
  exact P3WeakFloor.mwWeakFloor_two_fifths mwEqEquilibrium _ (hpath n)

/-- The same statement with the floor and the start exhibited, for readers who
want the concrete data: start at the basin pivot `2/5`, floor `5/12`. -/
theorem perpetual_escalation_at_two_fifths :
    (0 : ℝ) < 5 / 12
    ∧ (∀ n, (5 : ℝ) / 12 ≤ mechanismWitnessParams.dynamicTopLockInSanctionsF
              (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α (2 / 5) n)
    ∧ StrictMono (mechanismWitnessParams.dynamicTopLockInSanctionsF
              (mwSenderValueOne mwEqEquilibrium.V_S) mwEqEquilibrium.α (2 / 5)) := by
  obtain ⟨-, hsanct, hpath⟩ :=
    p3_monotone_sanctions_from_rational_start (x₀ := 2 / 5)
      (by norm_num) (by norm_num)
  exact ⟨by norm_num,
    fun n => P3WeakFloor.mwWeakFloor_two_fifths mwEqEquilibrium _ (hpath n),
    hsanct⟩


/-! ## The perfect-information form

The economy above carries an atomless transition shock (its `smear` averages the
continuation value over noise), so it is *not* a perfect-information game.  The
deterministic witness `b2Params` is: its transition is the affine law with no
smoothing, so the infinite-horizon game has perfect information.  There the
escalation is non-decreasing rather than strict. -/

/-- **Perpetual non-ending sanctions exist in a perfect-information
infinite-horizon game.**

There are primitives with a *deterministic* transition --- no noise, no
smoothing, hence perfect information --- an equilibrium of the resulting
infinite-horizon feedback Stackelberg game, and a strictly positive floor, such
that from every initial state in the high basin and at every date:

* the realised sanction never falls below `1/2 > 0`, so sanctions never end;
* the realised sanction path is non-decreasing, so sanctions never de-escalate;
* the political state remains in the high basin.

Both governments optimize at every date. -/
theorem exists_perfect_information_perpetual_sanctions :
    ∃ (E : b2Params.FeedbackStackelbergEquilibriumTop) (sbar : ℝ),
      0 < sbar
      ∧ ∀ x₀ ∈ Set.Icc (1 / 2 : ℝ) 1,
          (∀ n, b2Params.dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (1 / 2 : ℝ) 1)
          ∧ (∀ n, sbar ≤ b2Params.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
          ∧ Monotone (b2Params.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  obtain ⟨E, -, -, -, -, hout⟩ := b2_integrated_mechanism_active_generalF_witness
  exact ⟨E, 1 / 2, by norm_num, fun x₀ hx₀ => hout.2.2.2.2.2.2.1 x₀ hx₀⟩


/-- The transition of the perfect-information witness really is deterministic:
it is the affine law, with no smoothing operator anywhere. -/
theorem b2_transition_is_deterministic :
    b2Params.F = AbstractGame.affineF (1 / 2) := rfl

/-- **There exist primitives at which sanctions never end, in a
perfect-information infinite-horizon game.**

This is the fully existential form: the economy is discharged inside the
existential, and the transition is described only *qualitatively* --- it is
some deterministic affine adjustment law, with the rate itself existentially
bound --- so **no magnitude from the witness appears in the statement**.  There
exist primitives `p` whose transition is deterministic, an equilibrium of the
resulting
infinite-horizon feedback Stackelberg game, and a strictly positive floor
`sbar`, such that from **every** initial state of the high basin and at **every**
date the realised sanction stays at or above `sbar` and never falls.

Both governments optimise at every date: the Sender's sanction is the greatest
maximiser of its forward-looking objective and the Target's action carries the
equilibrium's Bellman-optimality field.  Nothing is imposed on either. -/
theorem exists_params_with_perpetual_sanctions :
    ∃ (p : AbstractGame.Params) (E : p.FeedbackStackelbergEquilibriumTop)
      (xbar sbar : ℝ),
      (∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ p.F = AbstractGame.affineF δ)
      ∧ 0 < sbar
      ∧ xbar < 1
      ∧ ∀ x₀ ∈ Set.Icc xbar 1,
          (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc xbar 1)
          ∧ (∀ n, sbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n)
          ∧ Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀) := by
  obtain ⟨E, sbar, hsbar, hall⟩ := exists_perfect_information_perpetual_sanctions
  exact ⟨b2Params, E, 1 / 2, sbar,
    ⟨1 / 2, by norm_num, by norm_num, b2_transition_is_deterministic⟩, hsbar,
    by norm_num, hall⟩


#print axioms exists_params_with_perpetual_sanctions
#print axioms exists_perfect_information_perpetual_sanctions
#print axioms b2_transition_is_deterministic

#print axioms exists_perpetually_escalating_sanctions
#print axioms perpetual_escalation_at_two_fifths

end

end Examples
end Sanctions
