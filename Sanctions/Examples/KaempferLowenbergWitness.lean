/-
Sanctions/Examples/KaempferLowenbergWitness.lean

**Concrete Kaempfer-Lowenberg two-group witnesses — the microfounded basis
witnesses for the two political basins.**

Two concrete `KaempferLowenberg.Polity` instances exhibiting that BOTH basins
arise endogenously from the two-group political market, with the basin assignment
*derived* from the rally / income-incidence / empowerment channel signs rather
than asserted as a stage-payoff cross-partial (contrast the Eaton-Engers witness,
where the K-L rally enters as the hand-chosen coefficient `+(3/2)·s·x` in `U_S`).

Both use the reference baseline `b(x) = −x` (strictly decreasing, so the clearing
entrenchment is `x*(s) = n(s)` the net sanction channel):

* `lockInWitness` — strong rally (`rally s = s`), no offsetting empowerment:
  net channel `n(s) = s` is increasing, so `x*(s) = s` rises with the sanction.
  This is the **high political basin** and exhibits the project's `F_mono_s`
  sign as a *derived* property.
* `washOutWitness` — opposition empowerment dominates (`empower s = s`):
  net channel `n(s) = −s` is decreasing, so `x*(s) = −s` falls with the sanction.
  This is the **low political basin / destabilization regime** that an assumed
  `F_mono_s ≥ 0` cannot reach.

The two are genuinely distinct (clearing entrenchment rises `0 ↦ 1` in the
lock-in witness, falls `0 ↦ −1` in the wash-out witness), establishing
non-vacuity of both `Polity.LockIn` and `Polity.WashOut`.
-/

import Sanctions.Theory.Microfoundations.KaempferLowenbergPolity

namespace Sanctions
namespace Examples

open KaempferLowenberg

/-- **Lock-in basis witness.** Strong rally, no offsetting empowerment ⟹ the
clearing entrenchment rises with the sanction (the derived `F_mono_s`). -/
noncomputable def lockInWitness : Polity where
  b := fun x => -x
  hb := fun _ _ h => neg_lt_neg h
  rally := fun s => s
  incid := fun _ => 0
  empower := fun _ => 0
  xstar := fun s => s
  hroot := fun s => by ring

/-- **Wash-out basis witness.** Opposition empowerment dominates ⟹ the clearing
entrenchment falls with the sanction (the destabilization basin). -/
noncomputable def washOutWitness : Polity where
  b := fun x => -x
  hb := fun _ _ h => neg_lt_neg h
  rally := fun _ => 0
  incid := fun _ => 0
  empower := fun s => s
  xstar := fun s => -s
  hroot := fun s => by ring

/-- The lock-in witness is in the lock-in regime. -/
theorem lockInWitness_lockIn : lockInWitness.LockIn := by
  intro a b h
  simp only [Polity.netChannel, lockInWitness]
  linarith

/-- Derived `F_mono_s` at the lock-in witness: clearing entrenchment is monotone. -/
theorem lockInWitness_xstar_mono : Monotone lockInWitness.xstar :=
  lockInWitness.xstar_mono_of_lockIn lockInWitness_lockIn

/-- The wash-out witness is in the wash-out regime. -/
theorem washOutWitness_washOut : washOutWitness.WashOut := by
  intro a b h
  simp only [Polity.netChannel, washOutWitness]
  linarith

/-- Derived destabilization at the wash-out witness: clearing entrenchment is
antitone (sanctions erode hardliner power). -/
theorem washOutWitness_xstar_anti : Antitone washOutWitness.xstar :=
  washOutWitness.xstar_anti_of_washOut washOutWitness_washOut

/-- The two basins are genuinely distinct: the lock-in clearing entrenchment
rises `0 ↦ 1`, the wash-out clearing entrenchment falls `0 ↦ −1`. -/
theorem witnesses_distinct :
    lockInWitness.xstar 0 = 0 ∧ lockInWitness.xstar 1 = 1 ∧
    washOutWitness.xstar 0 = 0 ∧ washOutWitness.xstar 1 = -1 :=
  ⟨rfl, rfl, by simp [washOutWitness], by simp [washOutWitness]⟩

end Examples
end Sanctions
