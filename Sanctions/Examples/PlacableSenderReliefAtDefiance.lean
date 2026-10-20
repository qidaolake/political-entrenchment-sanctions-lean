/-
Sanctions/Examples/PlacableSenderReliefAtDefiance.lean

**Relief participation at the Target's own optimum, without zero-sanction
neutrality** (round BB, 2026-09-28; doc 110, item R13a).

`PlacableSenderReliefParticipation.lean` shows that an uncompensated spell of
`T` imposed zero-sanction periods, followed by the same constructed equilibrium,
is acceptable to neither incumbent, for *any* compliance sequence `a` the Target
might play during the spell. Its headline form, `no_date_zero_transfer_supports_relief`
(pinned row 48), has six premises. One of them, `ZeroSanctionNoGain` (at zero
sanction no compliance level raises the Sender's stage payoff above defiance),
is consumed at exactly one place: the Sender's one-period step, to handle an
arbitrary compliance action. The same file also proves that defiance (`a ≡ 0`)
is the Target's best compliance sequence during the spell
(`targetReliefValue_le_defiance`), from the cost bound alone.

This file evaluates the spell at that optimum instead of at an arbitrary
sequence. At `a ≡ 0` the Sender's step needs no neutrality condition: the
Sender's payoff at defiance and zero sanction is compared with itself. So:

* **(1)** `no_date_zero_transfer_supports_relief_at_defiance`: with only the
  loss-offset margin, the monotone realised response, a feasible start and a
  nonempty spell (four premises), defiance is the Target's best compliance
  sequence during the spell, **and** no number `τ` makes the spell, played at
  that best sequence, weakly acceptable to both incumbents. The Target's
  optimum is also unique on the spell (`defiance_unique_best_relief_sequence`).
* **(2)** `no_date_zero_transfer_supports_relief_of_defiance`: row 48's exact
  statement, re-derived from (1) under `ZeroSanctionNoGain`. The Sender's spell
  value at any compliance sequence is at most its value at `a ≡ 0` (neutrality,
  pointwise), the Target's is at most its value at `a ≡ 0` (its own optimum), so
  a transfer that worked at `a` would work at `a ≡ 0`. Row 48 is thus a
  corollary of (1); a `type_of%` check at the foot of the file confirms the two
  statements are identical. Row 48 itself is untouched.
* **(3)** `relief_participation_of_margin_at_defiance`: the four-premise form of
  the paper-facing `relief_participation_of_margin` (premises: the loss-offset
  margin, the rally margin, a feasible start, a nonempty spell), at the
  constructed equilibrium `equilibriumTop_of_margin`, with the Target's
  best-sequence conjunct; and `relief_participation_of_margin_of_defiance`
  re-deriving the original six-premise statement from it under neutrality.

**Scope (load-bearing; Rule 9).** Every statement is universal over the chord
economy class and concerns the *constructed* equilibrium (`VSstar`, `VTstar`),
not every equilibrium. The spell's zero sanctions are imposed (Rule 1's
exogenous-phase exception); the Target's compliance during it is derived as its
optimum, not assumed. What (1) no longer covers is the any-sequence reading:
whether the Sender could gain from a compliance-for-relief spell when it values
compliance at zero sanction is not settled here, in either direction. That
reading is exactly what (2) recovers under `ZeroSanctionNoGain`.

Renovation item BH3.4 (2026-10-06): (3) extends to every full-defiance equilibrium,
under the loss-offset margin and a nondecreasing response in place of the rally margin
(`relief_participation_of_policy_zero_at_defiance`, in
`PlacableSenderDefianceEquilibriaWelfare.lean`), and
`relief_participation_of_margin_at_defiance` is re-derived from it there.

Rule 22: general in `F` (chord conditions only, inherited from the relief file).
Rule 3: no new hypothesis; every *assumption* is a premise of row 48 or of
`relief_participation_of_margin` (the uniqueness theorem's `hopt` is the
antecedent of its conclusion; the step lemma's `hy` comes from
`sender_relief_step`), and two (`ZeroSanctionNoGain` and the
compliance-sequence quantifier) are removed from the four-premise forms.
-/
import Sanctions.Examples.PlacableSenderReliefParticipation

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Finset

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## The Sender's step at defiance, without neutrality -/

/-- **One imposed zero-sanction period against a defiant Target costs the Sender
at least the stage-gain floor** `G_S`, with no neutrality condition: the
Sender's value dominates its objective at the stage optimum (Bellman
inequality), the stage optimum's continuation is at least a zero sanction's
(monotone transition, nondecreasing value), and the stage gain of the optimum
over a zero sanction is at least `G_S` (floor S12). The one-sided neutrality
`ZeroSanctionNoGain` that `sender_relief_step` needs for an arbitrary compliance
action is not needed at defiance. General in `F`. -/
theorem sender_relief_step_defiance {y : ℝ} (hy : y ∈ Sanctions.I) :
    E.toParams.U_S y 0 0 + E.β_S * E.VSstar (Sanctions.clipS' (E.F y 0)) + E.stageGainFloor
      ≤ E.VSstar (Sanctions.clipS' y) := by
  have hσ : E.σ y 0 ∈ Sanctions.I := E.σ_mem y 0
  -- Bellman inequality at the stage optimum
  have h1 := E.senderObj_le_VSstar (Sanctions.clipS' y) hσ
  rw [Sanctions.clipS'_val_eq_of_mem hy] at h1
  -- the stage optimum's continuation is at least the zero sanction's
  have hF : E.F y 0 ≤ E.F y (E.σ y 0) := E.F_mono_s y hσ.1
  have hslope := E.clip_lowerSlope E.VSstar_mem.1 _ (E.F_mem _ _ hy zero_mem_I) _
    (E.F_mem _ _ hy hσ) hF
  have hcont : E.VSstar (Sanctions.clipS' (E.F y 0))
      ≤ E.VSstar (Sanctions.clipS' (E.F y (E.σ y 0))) := by
    have := mul_nonneg E.gS_pos.le (sub_nonneg.2 hF)
    linarith
  have hcont' := mul_le_mul_of_nonneg_left hcont E.hβS0.le
  -- the stage gain (floor S12)
  have hgain := E.stage_gain_ge hy
  unfold senderObj at h1
  change E.U_S y 0 0 + E.β_S * E.VSstar (Sanctions.clipS' (E.F y 0)) + E.stageGainFloor
    ≤ E.VSstar (Sanctions.clipS' y)
  linarith

/-- **The Sender loses from a spell played against defiance**, by at least the
stage-gain floor per period, discounted at its own rate. No neutrality
condition. General in `F`. -/
theorem senderReliefValue_defiance_add_loss_le {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (T : ℕ) :
    E.senderReliefValue (fun _ => 0) x₀ T + E.stageGainFloor * ∑ t ∈ range T, E.β_S ^ t
      ≤ E.VSstar (Sanctions.clipS' x₀) := by
  have h := Sanctions.Foundations.FiniteDiscountedTelescope.sum_add_terminal_add_gap_le
    (β := E.β_S) (δ := E.stageGainFloor) E.hβS0.le
    (V := fun t => E.VSstar (Sanctions.clipS' (E.reliefState x₀ t)))
    (u := fun t => E.toParams.U_S (E.reliefState x₀ t) 0 0) T
    (fun t _ => by
      have := E.sender_relief_step_defiance (E.reliefState_mem hx₀ t)
      simpa [reliefState_succ] using this)
  simpa [senderReliefValue] using h

/-- The Sender's loss from a nonempty spell against defiance is strict: at least
the stage-gain floor `G_S > 0`. General in `F`. -/
theorem senderReliefValue_defiance_lt {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {T : ℕ} (hT : 0 < T) :
    E.senderReliefValue (fun _ => 0) x₀ T + E.stageGainFloor
      ≤ E.VSstar (Sanctions.clipS' x₀) := by
  have h := E.senderReliefValue_defiance_add_loss_le hx₀ T
  have hgeom := Sanctions.Foundations.FiniteDiscountedTelescope.one_le_geom_sum E.hβS0.le hT
  have hδ := E.stageGainFloor_pos
  nlinarith [h, hgeom, hδ]

/-! ## Defiance is the Target's best, and unique, spell sequence -/

/-- **Defiance beats any compliance sequence during the spell by at least the
discounted compliance cost** `ℓ_lo·Σ β_T^t a_t`: with the sanction imposed at
zero, compliance changes neither the state path nor the continuation, and each
unit of it costs at least `ℓ_lo` (the cost bound `hUT_costLo`). The quantitative
form of `targetReliefValue_le_defiance`. General in `F`. -/
theorem targetReliefValue_add_cost_le_defiance
    (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (T : ℕ) :
    (E.targetReliefValue hTM) hmono a x₀ T + E.ℓlo * ∑ t ∈ range T, E.β_T ^ t * a t
      ≤ (E.targetReliefValue hTM) hmono (fun _ => 0) x₀ T := by
  unfold targetReliefValue
  have hterm : ∀ t ∈ range T,
      E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) (a t) 0 + E.ℓlo * (E.β_T ^ t * a t)
        ≤ E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) 0 0 := by
    intro t _
    have h := E.hUT_costLo _ (E.reliefState_mem hx₀ t) 0 zero_mem_I 0 zero_mem_I (a t) (ha t)
      (ha t).1
    have hc : E.toParams.U_T (E.reliefState x₀ t) (a t) 0 + E.ℓlo * a t
        ≤ E.toParams.U_T (E.reliefState x₀ t) 0 0 := by
      change E.U_T (E.reliefState x₀ t) (a t) 0 + E.ℓlo * a t ≤ E.U_T (E.reliefState x₀ t) 0 0
      linarith
    have hp := pow_nonneg E.hβT0.le t
    have := mul_le_mul_of_nonneg_left hc hp
    nlinarith [this]
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at hsum
  linarith

/-- **Defiance is the Target's unique best compliance sequence during a spell**:
any sequence in `[0,1]` that does at least as well as `a ≡ 0` is zero in every
period of the spell. General in `F`. -/
theorem defiance_unique_best_relief_sequence
    (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {T : ℕ}
    (hopt : (E.targetReliefValue hTM) hmono (fun _ => 0) x₀ T
      ≤ (E.targetReliefValue hTM) hmono a x₀ T) :
    ∀ t < T, a t = 0 := by
  have h := (E.targetReliefValue_add_cost_le_defiance hTM) hmono ha hx₀ T
  have hnn : ∀ t ∈ range T, 0 ≤ E.β_T ^ t * a t :=
    fun t _ => mul_nonneg (pow_nonneg E.hβT0.le t) (ha t).1
  have hsum0 : ∑ t ∈ range T, E.β_T ^ t * a t = 0 := by
    have hle : E.ℓlo * ∑ t ∈ range T, E.β_T ^ t * a t ≤ 0 := by linarith
    have hge := sum_nonneg hnn
    have hpos := E.hℓlo
    nlinarith
  intro t ht
  have hterm := (sum_eq_zero_iff_of_nonneg hnn).1 hsum0 t (mem_range.2 ht)
  rcases mul_eq_zero.1 hterm with h0 | h0
  · exact absurd h0 (pow_ne_zero t E.hβT0.ne')
  · exact h0

/-! ## (1) Row 48 at the Target's optimum: four premises -/

/-- **The two incumbents' gains from a nonempty spell played at the Target's
optimum sum to at most `−G_S`**, with no neutrality condition. General in `F`. -/
theorem relief_joint_loss_at_defiance (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {T : ℕ} (hT : 0 < T) :
    E.senderReliefValue (fun _ => 0) x₀ T + (E.targetReliefValue hTM) hmono (fun _ => 0) x₀ T
        + E.stageGainFloor
      ≤ E.VSstar (Sanctions.clipS' x₀) + E.VTstar hTM hmono (Sanctions.clipS' x₀) := by
  have hS := E.senderReliefValue_defiance_lt hx₀ hT
  have hTt := (E.targetReliefValue_le hTM) hmono hx₀ (fun _ => zero_mem_I) T
  linarith

/-- **Row 48 at the Target's own optimum, on four premises** (doc 110, R13a).
Given only the loss-offset margin `LossOffset` (the Target's sanction pain is
covered by the discounted continuation gain of the higher state the sanction
produces), the monotone realised response `hmono`, a feasible start `x₀ ∈ [0,1]`
and a nonempty spell `T > 0`:

1. defiance `a ≡ 0` is the Target's best compliance sequence during the spell —
   no sequence in `[0,1]` gives it a higher spell value; and
2. at that sequence, no number `τ` makes the spell weakly acceptable to both
   incumbents when `τ` is taken from the Sender's value and added to the
   Target's.

Unlike row 48, neither `ZeroSanctionNoGain` nor an arbitrary compliance sequence
is a premise: the Target's compliance is derived as its optimum rather than
quantified over. This theorem proves that `a ≡ 0` is *a* best sequence;
that it is the unique best on the spell is the separate theorem
`defiance_unique_best_relief_sequence`. (Read as a date-zero side payment the
second conjunct presupposes quasilinear transfers, which the game does not
have; the statement is about the constructed values.) General in `F`. -/
theorem no_date_zero_transfer_supports_relief_at_defiance (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {T : ℕ} (hT : 0 < T) :
    (∀ a : ℕ → ℝ, (∀ t, a t ∈ Sanctions.I) →
        (E.targetReliefValue hTM) hmono a x₀ T
          ≤ (E.targetReliefValue hTM) hmono (fun _ => 0) x₀ T) ∧
    ¬ ∃ τ : ℝ, E.VSstar (Sanctions.clipS' x₀) ≤ E.senderReliefValue (fun _ => 0) x₀ T - τ ∧
        E.VTstar hTM hmono (Sanctions.clipS' x₀)
          ≤ (E.targetReliefValue hTM) hmono (fun _ => 0) x₀ T + τ := by
  refine ⟨fun a ha => (E.targetReliefValue_le_defiance hTM) hmono ha hx₀ T, ?_⟩
  rintro ⟨τ, h1, h2⟩
  have h := (E.relief_joint_loss_at_defiance hTM) hmono hx₀ hT
  have hδ := E.stageGainFloor_pos
  linarith

/-! ## (2) Row 48 as a corollary under neutrality -/

/-- **Under `ZeroSanctionNoGain` the Sender's spell value at any compliance
sequence is at most its value at defiance**: the state path and the terminal
value do not depend on compliance, and at zero sanction no compliance level
raises the Sender's stage payoff above defiance. General in `F`. -/
theorem senderReliefValue_le_defiance (hZ : E.ZeroSanctionNoGain)
    {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (T : ℕ) :
    E.senderReliefValue a x₀ T ≤ E.senderReliefValue (fun _ => 0) x₀ T := by
  unfold senderReliefValue
  have hterm : ∀ t ∈ range T,
      E.β_S ^ t * E.toParams.U_S (E.reliefState x₀ t) (a t) 0
        ≤ E.β_S ^ t * E.toParams.U_S (E.reliefState x₀ t) 0 0 :=
    fun t _ => mul_le_mul_of_nonneg_left (hZ _ (E.reliefState_mem hx₀ t) (a t) (ha t))
      (pow_nonneg E.hβS0.le t)
  linarith [sum_le_sum hterm]

/-- **Row 48, re-derived from its four-premise form.** The statement is exactly
`no_date_zero_transfer_supports_relief` (pinned row 48): six premises, any
compliance sequence. The proof goes through
`no_date_zero_transfer_supports_relief_at_defiance`: a transfer `τ` that made the
spell at `a` weakly acceptable to both would do so at `a ≡ 0`, since the
Sender's value at `a` is at most at defiance (`senderReliefValue_le_defiance`,
the only use of `ZeroSanctionNoGain`) and the Target's is at most at defiance
(its own optimum). General in `F`. -/
theorem no_date_zero_transfer_supports_relief_of_defiance (hZ : E.ZeroSanctionNoGain)
    (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {T : ℕ}
    (hT : 0 < T) :
    ¬ ∃ τ : ℝ, E.VSstar (Sanctions.clipS' x₀) ≤ E.senderReliefValue a x₀ T - τ ∧
        E.VTstar hTM hmono (Sanctions.clipS' x₀) ≤ (E.targetReliefValue hTM) hmono a x₀ T + τ := by
  rintro ⟨τ, h1, h2⟩
  have hS := E.senderReliefValue_le_defiance hZ ha hx₀ T
  have hTt := (E.targetReliefValue_le_defiance hTM) hmono ha hx₀ T
  exact ((E.no_date_zero_transfer_supports_relief_at_defiance hTM) hmono hx₀ hT).2
    ⟨τ, by linarith, by linarith⟩

/-! ## (3) The paper-facing form at the constructed equilibrium: four premises -/

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-! ### The rally-margin forms, on the two-sided extension (renovation item BJ3.1)

The rally margin reads the two-sided curvature data, so since 2026-10-07 the two
margin-form statements below are stated on `ChordEconomyTwoSided`; until then they were
on `ChordEconomy`, otherwise unchanged. Each is general in `F`. -/

/-- **Relief participation at the constructed equilibrium, on four premises**
(doc 110, R13a). Given the loss-offset margin `LossOffset`, the rally margin
`hmargin` (the Sender's discounted continuation cross-effect is dominated by its
stage cross-effect floor `r_lo`, which makes the realised response monotone), a
feasible start and a nonempty spell, at `equilibriumTop_of_margin`:

1. the Sender strictly loses from the spell played against defiance, by at
   least the stage-gain floor `G_S`;
2. the Target weakly loses from it; and
3. defiance is the Target's best compliance sequence during the spell.

The four-premise form of `relief_participation_of_margin`, which additionally
takes `ZeroSanctionNoGain` and an arbitrary compliance sequence. General in
`F`. The form at every full-defiance equilibrium, with a nondecreasing response in
place of the rally margin, is `relief_participation_of_policy_zero_at_defiance`
(renovation item BH3.4). -/
theorem relief_participation_of_margin_at_defiance (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {T : ℕ} (hT : 0 < T) :
    (∑ t ∈ range T, E.β_S ^ t * E.toParams.U_S (E.reliefState x₀ t) 0 0
        + E.β_S ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_S
            (Sanctions.clipS' (E.reliefState x₀ T))
        + E.stageGainFloor
      ≤ ((E.equilibriumTop_of_margin hTM) hmargin).V_S (Sanctions.clipS' x₀)) ∧
    (∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) 0 0
        + E.β_T ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_T
            (Sanctions.clipS' (E.reliefState x₀ T))
      ≤ ((E.equilibriumTop_of_margin hTM) hmargin).V_T (Sanctions.clipS' x₀)) ∧
    (∀ a : ℕ → ℝ, (∀ t, a t ∈ Sanctions.I) →
      ∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) (a t) 0
          + E.β_T ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_T
              (Sanctions.clipS' (E.reliefState x₀ T))
        ≤ ∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) 0 0
          + E.β_T ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_T
              (Sanctions.clipS' (E.reliefState x₀ T))) :=
  ⟨E.senderReliefValue_defiance_lt hx₀ hT,
    (E.targetReliefValue_le hTM) (E.responsePath_monotoneOn_of_margin hmargin) hx₀
      (fun _ => zero_mem_I) T,
    fun _ ha => (E.targetReliefValue_le_defiance hTM)
      (E.responsePath_monotoneOn_of_margin hmargin) ha hx₀ T⟩

/-- **`relief_participation_of_margin`, re-derived from its four-premise form.**
The statement is exactly the paper-facing `relief_participation_of_margin` (any
compliance sequence, under `ZeroSanctionNoGain`); the Sender half follows from
the defiance form by `senderReliefValue_le_defiance`, the Target half from the
defiance form by the Target's own optimum. General in `F`. -/
theorem relief_participation_of_margin_of_defiance (hZ : E.ZeroSanctionNoGain)
    (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {T : ℕ}
    (hT : 0 < T) :
    (∑ t ∈ range T, E.β_S ^ t * E.toParams.U_S (E.reliefState x₀ t) (a t) 0
        + E.β_S ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_S
            (Sanctions.clipS' (E.reliefState x₀ T))
        + E.stageGainFloor
      ≤ ((E.equilibriumTop_of_margin hTM) hmargin).V_S (Sanctions.clipS' x₀)) ∧
    (∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) (a t) 0
        + E.β_T ^ T * ((E.equilibriumTop_of_margin hTM) hmargin).V_T
            (Sanctions.clipS' (E.reliefState x₀ T))
      ≤ ((E.equilibriumTop_of_margin hTM) hmargin).V_T (Sanctions.clipS' x₀)) := by
  obtain ⟨hS0, hT0, hbest⟩ := (E.relief_participation_of_margin_at_defiance hTM) hmargin hx₀ hT
  have hS := E.senderReliefValue_le_defiance hZ ha hx₀ T
  unfold senderReliefValue at hS
  exact ⟨by
      change _ ≤ E.VSstar (Sanctions.clipS' x₀)
      change _ ≤ E.VSstar (Sanctions.clipS' x₀) at hS0
      linarith,
    (hbest a ha).trans hT0⟩

end ChordEconomyTwoSided

/-! ## The corollaries have exactly the original statements

Proof irrelevance makes two proofs of one proposition equal, so the checks
below compare the *types*: each re-derived theorem's type is definitionally
equal to the original's (and is written with the same binders, in the same
order). A drift in either statement breaks the check. -/

example : type_of% @ChordEconomy.no_date_zero_transfer_supports_relief_of_defiance
    = type_of% @ChordEconomy.no_date_zero_transfer_supports_relief := rfl

example : type_of% @ChordEconomyTwoSided.relief_participation_of_margin_of_defiance
    = type_of% @ChordEconomyTwoSided.relief_participation_of_margin := rfl

end

#print axioms ChordEconomy.sender_relief_step_defiance
#print axioms ChordEconomy.senderReliefValue_defiance_add_loss_le
#print axioms ChordEconomy.senderReliefValue_defiance_lt
#print axioms ChordEconomy.targetReliefValue_add_cost_le_defiance
#print axioms ChordEconomy.defiance_unique_best_relief_sequence
#print axioms ChordEconomy.relief_joint_loss_at_defiance
#print axioms ChordEconomy.no_date_zero_transfer_supports_relief_at_defiance
#print axioms ChordEconomy.senderReliefValue_le_defiance
#print axioms ChordEconomy.no_date_zero_transfer_supports_relief_of_defiance
#print axioms ChordEconomyTwoSided.relief_participation_of_margin_at_defiance
#print axioms ChordEconomyTwoSided.relief_participation_of_margin_of_defiance

end Examples
end Sanctions
