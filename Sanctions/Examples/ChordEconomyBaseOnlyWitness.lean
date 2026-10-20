/-
Sanctions/Examples/ChordEconomyBaseOnlyWitness.lean

**The base chord class is strictly larger than its relief extension** (renovation item
BH5.6(b), 2026-10-07; audit item H-7; Rule 9B generality witness).

Round BC (2026-09-29) moved four rates out of `ChordEconomy` into the relief extension
`ChordEconomyRelief`: the Target's upper compliance cost (T3), its lower sanction pain
`p_lo > 0` (T5), its upper state envelope (T7) and the Sender's upper cross rate (S9). The
defiance side, monotone-class uniqueness, branch invariance and the wedge floor are stated over
the base class. Every member exhibited in the tree also satisfied the relief extension, so the
`ChordEconomy` docstring recorded the base class's extra generality as unwitnessed. This file
supplies the witness, for every chord economy.

The construction keeps every field of a chord economy `E` except the Target's stage payoff,
which becomes the symbolic family's `symU_T ℓ c c v`,

    U_T(x, a, s) = −ℓ·a + s·(c·x − c) + v·x.

Its per-unit sanction pain is `c·(1 − x)`: positive below the top state and fully offset by the
rally at the top state `x = 1`.

1. `ChordEconomy.withRallyOffsetTarget E ℓ c v`: a chord economy for every `ℓ > 0`, `c ≥ 0`,
   `v > 0`. Only three base fields read the Target's payoff — T2 (compliance cost at least
   `ℓ_lo`), T4 (pain at most `c`) and T6 (state slope at least `v_lo + n_lo·s`) — and they hold
   with `ℓ_lo = ℓ`, pain ceiling `c`, and envelope `v + c·s`. Every Sender, transition, discount
   and carrier field is copied from `E`.
2. `not_relief_of_rallyOffset_U_T`: no relief economy has this Target payoff. Its field T5
   (`hUT_painLo`: pain at least `p_lo > 0` per unit) fails at the top state, where the pain is
   zero.
3. `withRallyOffsetTarget_not_relief`: hence no relief economy extends the new member.
   `exists_not_relief_same_sender` keeps the transition, the Sender's payoff and both discounts
   of any chord economy, and `chordEconomy_not_relief_witness` is a closed instance built on the
   affine family member `placableAffine`, which also satisfies interiority.

**Why the Target's payoff, not the record.** Interiority and the stage relief margin can be
falsified at any member by inflating the upper-bound data fields (`uhi`, `dhi`, `ℓhi`), which
changes no economy and witnesses nothing. The separation has to be in the game itself. The
relief extension's upper rates (S9, T3, T7) hold with large enough constants for any smooth
payoff, so its one genuine lower bound, the sanction pain T5, is the route.

**Rule 9 (9A).** An existence certificate for the separation of the two classes, and nothing
more: it says nothing about which members are typical. **Rule 9B.** `ChordEconomy` has no
opaque `Prop` field: each proposition-valued field is a relation over the structure's own data,
and the member elaborates, which is its joint satisfiability. **Rule 22.** General in `F`: the
construction works over every chord economy, whatever its transition; the closed instance uses
`placableAffine`'s affine law at rate `1/2`. **Rule 3.** No assumption is introduced.
**Rule 9C.** The identities behind T2, T4, T6 and the zero pain at the top state were checked in
exact arithmetic before the Lean was written.
-/
import Sanctions.Examples.PlacableSenderWitnesses

namespace Sanctions
namespace Examples

open Set AbstractGame

noncomputable section

/-! ## The rally-offset Target payoff -/

/-- **T2 for the rally-offset Target**: compliance costs exactly `ℓ` per unit. -/
theorem rallyOffset_costLo (ℓ c v : ℝ) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a₁ ∈ Icc (0 : ℝ) 1, ∀ a₂ ∈ Icc (0 : ℝ) 1,
      a₁ ≤ a₂ → symU_T ℓ c c v x a₂ s - symU_T ℓ c c v x a₁ s ≤ -(ℓ * (a₂ - a₁)) := by
  intro x _ s _ a₁ _ a₂ _ _
  apply le_of_eq; unfold symU_T; ring

/-- **T4 for the rally-offset Target**: the pain per unit of sanction, `c·(1 − x)`, is at most
`c` on the feasible square (`c ≥ 0`). -/
theorem rallyOffset_painHi {c : ℝ} (ℓ v : ℝ) (hc : 0 ≤ c) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ s₁ ∈ Icc (0 : ℝ) 1, ∀ s₂ ∈ Icc (0 : ℝ) 1,
      s₁ ≤ s₂ → symU_T ℓ c c v x a s₁ - symU_T ℓ c c v x a s₂ ≤ c * (s₂ - s₁) := by
  intro x hx a _ s₁ _ s₂ _ hs
  have hid : symU_T ℓ c c v x a s₁ - symU_T ℓ c c v x a s₂
      = c * (s₂ - s₁) - (s₂ - s₁) * (c * x) := by
    unfold symU_T; ring
  rw [hid]
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (mul_nonneg hc hx.1)]

/-- **T6 for the rally-offset Target**: the state is valued at exactly `v + c·s` per unit at
sanction `s`. -/
theorem rallyOffset_stateLo (ℓ c v : ℝ) :
    ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1, ∀ x₂ ∈ Icc (0 : ℝ) 1,
      x₁ ≤ x₂ → (v + c * s) * (x₂ - x₁) ≤ symU_T ℓ c c v x₂ a s - symU_T ℓ c c v x₁ a s := by
  intro a _ s _ x₁ _ x₂ _ _
  apply le_of_eq; unfold symU_T; ring

/-- **No sanction pain at the top state**: there the rally exactly offsets the pain, so a full
sanction costs the Target nothing relative to none. -/
theorem rallyOffset_no_pain_at_top (ℓ c v a : ℝ) :
    symU_T ℓ c c v 1 a 0 - symU_T ℓ c c v 1 a 1 = 0 := by
  unfold symU_T; ring

/-- **No relief economy has the rally-offset Target payoff**, whatever `ℓ`, `c`, `v`. The relief
field T5 asks the Target to lose at least `p_lo > 0` per unit of sanction at every state; at the
top state this Target loses nothing. -/
theorem not_relief_of_rallyOffset_U_T (ℓ c v : ℝ) :
    ¬ ∃ R : ChordEconomyRelief, R.U_T = symU_T ℓ c c v := by
  rintro ⟨R, hR⟩
  have h := R.hUT_painLo 1 ⟨zero_le_one, le_rfl⟩ 0 ⟨le_rfl, zero_le_one⟩ 0
    ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ zero_le_one
  rw [hR, rallyOffset_no_pain_at_top, sub_zero, mul_one] at h
  exact absurd h (not_le.mpr R.hplo)

/-! ## A base member outside the relief extension, from every chord economy -/

namespace ChordEconomy

/-- **The same chord economy with the rally-offset Target** (renovation item BH5.6(b),
2026-10-07). Every field of `E` is kept except the Target's stage payoff, which becomes
`symU_T ℓ c c v`, and the three base Target rates that read it: `ℓ_lo = ℓ`, the pain ceiling
`c`, and the state envelope `v + c·s` (`v_lo = v`, `n_lo = c`). No Sender, transition, discount
or carrier field reads the Target's payoff. General in `F`: the transition is `E`'s. -/
def withRallyOffsetTarget (E : ChordEconomy) (ℓ c v : ℝ) (hℓ : 0 < ℓ) (hc : 0 ≤ c)
    (hv : 0 < v) : ChordEconomy :=
  { E with
    U_T := symU_T ℓ c c v
    U_T_continuous := symU_T_continuous ℓ c c v
    ℓlo := ℓ
    c := c
    vlo := v
    nlo := c
    hUT_costLo := rallyOffset_costLo ℓ c v
    hUT_painHi := rallyOffset_painHi ℓ v hc
    hUT_stateLo := rallyOffset_stateLo ℓ c v
    hℓlo := hℓ
    hvlo := hv
    hnlo := hc }

variable (E : ChordEconomy) (ℓ c v : ℝ) (hℓ : 0 < ℓ) (hc : 0 ≤ c) (hv : 0 < v)

@[simp] theorem withRallyOffsetTarget_U_T :
    (E.withRallyOffsetTarget ℓ c v hℓ hc hv).U_T = symU_T ℓ c c v := rfl
@[simp] theorem withRallyOffsetTarget_U_S :
    (E.withRallyOffsetTarget ℓ c v hℓ hc hv).U_S = E.U_S := rfl
@[simp] theorem withRallyOffsetTarget_F :
    (E.withRallyOffsetTarget ℓ c v hℓ hc hv).F = E.F := rfl
@[simp] theorem withRallyOffsetTarget_β_S :
    (E.withRallyOffsetTarget ℓ c v hℓ hc hv).β_S = E.β_S := rfl
@[simp] theorem withRallyOffsetTarget_β_T :
    (E.withRallyOffsetTarget ℓ c v hℓ hc hv).β_T = E.β_T := rfl

/-- Interiority reads only the Sender's rates and the transition's chords, so the new member is
interior exactly when `E` is. General in `F`. -/
theorem withRallyOffsetTarget_interior_iff :
    (E.withRallyOffsetTarget ℓ c v hℓ hc hv).Interior ↔ E.Interior := Iff.rfl

/-- **No relief economy extends the new member.** General in `F`. -/
theorem withRallyOffsetTarget_not_relief :
    ¬ ∃ R : ChordEconomyRelief, R.toChordEconomy = E.withRallyOffsetTarget ℓ c v hℓ hc hv := by
  rintro ⟨R, hR⟩
  exact not_relief_of_rallyOffset_U_T ℓ c v ⟨R, congrArg (fun G : ChordEconomy => G.U_T) hR⟩

/-- **Every chord economy's Sender, transition and discounts are shared by a chord economy
outside the relief extension.** For every chord economy `E` there is a chord economy with the
same transition, the same Sender stage payoff and the same two discount factors that no relief
economy extends (the rally-offset Target with `E`'s compliance cost and state rate and unit pain
ceiling). General in `F`, with no hypothesis on `E`. -/
theorem exists_not_relief_same_sender :
    ∃ E' : ChordEconomy, E'.F = E.F ∧ E'.U_S = E.U_S ∧ E'.β_S = E.β_S ∧ E'.β_T = E.β_T ∧
      ¬ ∃ R : ChordEconomyRelief, R.toChordEconomy = E' :=
  ⟨E.withRallyOffsetTarget E.ℓlo 1 E.vlo E.hℓlo zero_le_one E.hvlo, rfl, rfl, rfl, rfl,
    E.withRallyOffsetTarget_not_relief E.ℓlo 1 E.vlo E.hℓlo zero_le_one E.hvlo⟩

end ChordEconomy

/-! ## A closed instance -/

/-- **Rule 9 form.** There is a chord economy, interior, that no relief economy extends: the
affine family member `placableAffine` (`ℓ = 1`, `c = 4`, `v = 30`, rally `n = 0`) with its
Target's rally raised to `n = 4`, so that the pain `4·(1 − x)` vanishes at the top state. Rule 22:
affine-restricted (the member's `affineF (1/2)`); `exists_not_relief_same_sender` is the form
over every chord economy. -/
theorem chordEconomy_not_relief_witness :
    ∃ E : ChordEconomy, E.Interior ∧ ¬ ∃ R : ChordEconomyRelief, R.toChordEconomy = E :=
  ⟨placableAffine.toChord.toChordEconomy.withRallyOffsetTarget 1 4 30 one_pos (by norm_num)
      (by norm_num),
    placableAffine_chordInterior,
    ChordEconomy.withRallyOffsetTarget_not_relief _ _ _ _ _ _ _⟩

/-- **Rule 11 form.** Not every chord economy extends to a relief economy: the base class is
strictly larger than the relief extension. -/
theorem chordEconomy_not_all_relief :
    ¬ ∀ E : ChordEconomy, ∃ R : ChordEconomyRelief, R.toChordEconomy = E := by
  intro h
  obtain ⟨E, -, hE⟩ := chordEconomy_not_relief_witness
  exact hE (h E)

end

#print axioms Sanctions.Examples.not_relief_of_rallyOffset_U_T
#print axioms Sanctions.Examples.ChordEconomy.exists_not_relief_same_sender
#print axioms Sanctions.Examples.chordEconomy_not_relief_witness
#print axioms Sanctions.Examples.chordEconomy_not_all_relief

end Examples
end Sanctions
