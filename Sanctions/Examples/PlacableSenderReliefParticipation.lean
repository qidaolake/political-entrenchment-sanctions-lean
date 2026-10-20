/-
Sanctions/Examples/PlacableSenderReliefParticipation.lean

**Neither incumbent gains from an uncompensated spell of relief followed by the
same equilibrium** (round AE, 2026-09-20; doc 94, item A3+; the derivation is
the outside reader's, `suggestions/2026-09-20-literature-recommendations-
verification/01_MATHEMATICAL_RESULTS.md` §4, re-derived and checked here; on the
abstract payoffs since round AV, 2026-09-25, doc 104).

The manuscript's relief results treat relief as *imposed*: a zero-sanction
schedule that neither government chose (Rule 1's exogenous-phase exception).
This file asks what such a spell is worth to each incumbent, at the constructed
forward-looking equilibrium of a chord economy, when the same equilibrium
resumes afterwards. For `T` periods of zero sanctions from a feasible start
`x₀`, any compliance sequence `a`, and the equilibrium's own values as terminal
values:

* **Sender** (`senderReliefValue_add_loss_le`): the spell is worth strictly less
  than the equilibrium, by at least the stage-gain floor
  `G_S = s₀(u_lo − Q̄ s₀/2)`, `s₀ = min(1, u_lo/Q̄)`, per period, discounted (on the
  quadratic–linear family `G_S = u₀²/(2q)`, `toChord_stageGainFloor`). One step:
  the Sender's value dominates its objective at the stage optimum (Bellman
  inequality, `senderObj_le_VSstar`); the carrier value is nondecreasing and the
  transition is monotone in the sanction, so the stage optimum's continuation is
  at least that of a zero sanction; the stage gain of the optimum over a zero
  sanction is at least `G_S` (floor S12, `stage_gain_ge`); and no compliance level
  beats defiance at zero sanction (`ZeroSanctionNoGain`, the one-sided
  zero-sanction neutrality of sign-off M2).
* **Target** (`targetReliefValue_add_cost_le`): the spell is worth weakly less,
  by at least the discounted compliance cost `ℓ_lo·Σ β_T^t·a_t`. One step: the
  Target's Bellman equality at defiance and the realised response `R(y)`, the
  value's lower slope `g_T`, the lower sanction chord `d_lo`, the pain bound `c`
  (T4) and the cost bound `ℓ_lo` (T2), and the loss-offset margin
  `LossOffset : c ≤ β_T·d_lo·g_T` — the Target incumbent's sanction pain is
  covered by the discounted continuation gain of the higher state the sanction
  produces. So defiance is also the best compliance sequence *during* the spell
  (`targetReliefValue_le_defiance`).
* **Jointly** (`relief_joint_loss`, `no_date_zero_transfer_supports_relief`): the
  two incumbents' gains sum to at most `−G_S`, so no number `τ` makes the
  spell weakly acceptable to both when `τ` is subtracted from one value and
  added to the other. Read as a lump-sum side payment at date zero this
  presupposes quasilinear transfers, which the game does not have; the theorem
  itself is a statement about the constructed values.

**Scope (load-bearing).** This excludes one arrangement: uncompensated zero
sanctions for finitely many periods, then the *same* constructed equilibrium.
It says nothing about a different continuation equilibrium, a third party's
subsidy, transfers at later dates under unequal discounting, or population
welfare. The Target half rests on the loss-offset margin and **fails outside
it**: at `lossOffsetParams` — an economy outside the family whose constructed
equilibrium still has defiance as the unique optimum — one imposed
zero-sanction period is worth exactly `1/18` *more* to the Target than the
equilibrium, at every state (`lossOffset_relief_period_benefits_target`;
Rule 11: the refutation of the unqualified claim, exhibited).

Renovation item BH3.4 (2026-10-06): the rally margin in `relief_participation_of_margin`
only names the constructed equilibrium and makes the response nondecreasing. The
statement holds at every full-defiance equilibrium under the loss-offset margin and a
nondecreasing response (`relief_participation_of_policy_zero`, in
`PlacableSenderDefianceEquilibriaWelfare.lean`), and it is re-derived from that form
there.

Rule 22: general in `F` (chord conditions only), except the refutation, which is
at an affine economy and marked so. Rule 9: nothing parametric here is a
witness; the refutation licenses exactly "the margin cannot be dropped".
-/
import Sanctions.Examples.PlacableSenderWelfareCompletion
import Sanctions.Examples.LossOffsetConverseCounterexample
import Sanctions.Foundations.FiniteDiscountedTelescope

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Finset

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## The stage-gain floor -/

/-- The sanction at which the floor condition's gain bound is largest,
`s₀ = min(1, u_lo/Q̄)`. -/
def gainSanction : ℝ := min 1 (E.ulo / E.Qbar)

theorem gainSanction_pos : 0 < E.gainSanction :=
  lt_min one_pos (div_pos E.hulo E.Qbar_pos)

theorem gainSanction_mem : E.gainSanction ∈ Sanctions.I :=
  ⟨E.gainSanction_pos.le, min_le_left _ _⟩

theorem Qbar_mul_gainSanction_le : E.Qbar * E.gainSanction ≤ E.ulo := by
  have h := min_le_right 1 (E.ulo / E.Qbar)
  have hQ := E.Qbar_pos
  calc E.Qbar * E.gainSanction ≤ E.Qbar * (E.ulo / E.Qbar) := mul_le_mul_of_nonneg_left h hQ.le
    _ = E.ulo := by field_simp

/-- **The stage-gain floor** `G_S = s₀·(u_lo − Q̄·s₀/2)`, `s₀ = min(1, u_lo/Q̄)`: the
floor condition (S12) guarantees that sanctioning a defiant Target at `s₀` beats
not sanctioning by at least `G_S` at every state. It is `u_lo²/(2Q̄)` when
`u_lo ≤ Q̄`; on the quadratic–linear family, `u₀²/(2q)`. -/
def stageGainFloor : ℝ := E.gainSanction * (E.ulo - E.Qbar * E.gainSanction / 2)

theorem stageGainFloor_pos : 0 < E.stageGainFloor := by
  unfold stageGainFloor
  have h := E.Qbar_mul_gainSanction_le
  exact mul_pos E.gainSanction_pos (by linarith [E.hulo])

/-- The stage gain of the optimal sanction over zero is at least the floor, at
every state. -/
theorem stage_gain_ge {y : ℝ} (hy : y ∈ Sanctions.I) :
    E.stageGainFloor ≤ E.U_S y 0 (E.σ y 0) - E.U_S y 0 0 := by
  have h1 := E.hUS_floor y hy 0 zero_mem_I E.gainSanction E.gainSanction_mem
    E.gainSanction_pos.le
  have h2 := (E.σ_isMaxOn_U_S y 0) E.gainSanction_mem
  simp only [Set.mem_setOf_eq] at h2
  unfold stageGainFloor
  simp only [sub_zero, add_zero] at h1
  linarith

/-! ## The spell -/

/-- The state after `t` periods of imposed zero sanctions from `x₀`: the
all-zero schedule of `Theory/LockIn/FiniteEpisodePersistence`. -/
def reliefState (x₀ : ℝ) (t : ℕ) : ℝ := E.toParams.episodePath (fun _ => 0) x₀ t

@[simp] theorem reliefState_zero (x₀ : ℝ) : E.reliefState x₀ 0 = x₀ := rfl

theorem reliefState_succ (x₀ : ℝ) (t : ℕ) :
    E.reliefState x₀ (t + 1) = E.F (E.reliefState x₀ t) 0 := rfl

theorem reliefState_mem {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    E.reliefState x₀ t ∈ Sanctions.I :=
  E.toParams.episodePath_mem (fun _ => ⟨le_rfl, zero_le_one⟩) hx₀ t

/-- The Sender's value of `T` periods of imposed zero sanctions with compliance
sequence `a`, followed by the constructed forward-looking equilibrium. -/
def senderReliefValue (a : ℕ → ℝ) (x₀ : ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, E.β_S ^ t * E.toParams.U_S (E.reliefState x₀ t) (a t) 0
    + E.β_S ^ T * E.VSstar (Sanctions.clipS' (E.reliefState x₀ T))

/-- The Target's value of the same spell. -/
def targetReliefValue (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (a : ℕ → ℝ) (x₀ : ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) (a t) 0
    + E.β_T ^ T * E.VTstar hTM hmono (Sanctions.clipS' (E.reliefState x₀ T))

/-! ## One period -/

/-- **One imposed zero-sanction period costs the Sender at least the stage-gain
floor**, for every compliance action in `[0,1]`, when no compliance level beats
defiance at zero sanction (`ZeroSanctionNoGain`). -/
theorem sender_relief_step (hZ : E.ZeroSanctionNoGain) {y : ℝ} (hy : y ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I) :
    E.toParams.U_S y a 0 + E.β_S * E.VSstar (Sanctions.clipS' (E.F y 0)) + E.stageGainFloor
      ≤ E.VSstar (Sanctions.clipS' y) := by
  have hσ : E.σ y 0 ∈ Sanctions.I := E.σ_mem y 0
  -- Bellman inequality at the stage optimum (`senderObj_le_VSstar`, WelfareCompletion)
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
  -- the stage gain and the one-sided neutrality
  have hgain := E.stage_gain_ge hy
  have hN := hZ y hy a ha
  unfold senderObj at h1
  change E.U_S y a 0 + E.β_S * E.VSstar (Sanctions.clipS' (E.F y 0)) + E.stageGainFloor
    ≤ E.VSstar (Sanctions.clipS' y)
  linarith

/-- **One imposed zero-sanction period costs the Target at least its compliance
cost `ℓ_lo·a`**, under the loss-offset margin: its Bellman equality at defiance
and the realised response `R`, the pain of `R` (at most `c·R`, T4), the
continuation gain of the higher state `R` produces (at least `β_T g_T d_lo R`),
and the compliance cost (at least `ℓ_lo·a`, T2). -/
theorem target_relief_step (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {y : ℝ} (hy : y ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    E.toParams.U_T y a 0 + E.β_T * E.VTstar hTM hmono (Sanctions.clipS' (E.F y 0)) + E.ℓlo * a
      ≤ E.VTstar hTM hmono (Sanctions.clipS' y) := by
  have hR : E.responsePath E.VSstar y ∈ Sanctions.I := E.responsePath_mem _ _
  have hclip : Sanctions.clipS' y = ⟨y, hy⟩ := Subtype.ext (Sanctions.clipS'_val_eq_of_mem hy)
  -- the Target's Bellman equality at defiance and the realised response
  have hfix := congrArg (fun V : Val => V ⟨y, hy⟩) (E.VTstar_fix hTM hmono)
  simp only at hfix
  rw [targetOp_apply] at hfix
  -- lower slope of the value and the lower sanction chord
  have hF : E.F y 0 ≤ E.F y (E.responsePath E.VSstar y) := E.F_mono_s y hR.1
  have hslope := E.clipT_lowerSlope (E.VTstar_mem hTM hmono) _ (E.F_mem _ _ hy zero_mem_I) _
    (E.F_mem _ _ hy hR) hF
  have hchord : E.dlo * (E.responsePath E.VSstar y - 0)
      ≤ E.F y (E.responsePath E.VSstar y) - E.F y 0 := E.hSlo hy zero_mem_I hR hR.1
  have hTM' : E.c ≤ E.β_T * E.dlo * E.gT := hTM
  have hgT := E.gT_pos
  have hβT := E.hβT0
  have hA : E.β_T * E.gT * (E.dlo * (E.responsePath E.VSstar y - 0))
      ≤ E.β_T * (E.VTstar hTM hmono (Sanctions.clipS' (E.F y (E.responsePath E.VSstar y)))
          - E.VTstar hTM hmono (Sanctions.clipS' (E.F y 0))) := by
    have h1 := mul_le_mul_of_nonneg_left hchord hgT.le
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hslope) hβT.le
    nlinarith [h2]
  have hB : 0 ≤ E.responsePath E.VSstar y * (E.β_T * E.dlo * E.gT - E.c) :=
    mul_nonneg hR.1 (by linarith)
  -- the stage: pain of `R` at most `c·R` (T4), compliance cost at least `ℓ_lo·a` (T2)
  have hpain := E.hUT_painHi y hy 0 zero_mem_I 0 zero_mem_I _ hR hR.1
  have hcost := E.hUT_costLo y hy 0 zero_mem_I 0 zero_mem_I a ha ha.1
  rw [hclip, ← hfix]
  change E.U_T y a 0 + E.β_T * E.VTstar hTM hmono (Sanctions.clipS' (E.F y 0)) + E.ℓlo * a
    ≤ E.U_T y 0 (E.responsePath E.VSstar y)
      + E.β_T * E.VTstar hTM hmono (Sanctions.clipS' (E.F y (E.responsePath E.VSstar y)))
  nlinarith [hA, hB, hpain, hcost]

/-! ## The spell -/

/-- **The Sender strictly loses from the spell**, by at least the stage-gain
floor per period, discounted at its own rate; for every compliance sequence in
`[0,1]`. -/
theorem senderReliefValue_add_loss_le (hZ : E.ZeroSanctionNoGain) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) (T : ℕ) :
    E.senderReliefValue a x₀ T + E.stageGainFloor * ∑ t ∈ range T, E.β_S ^ t
      ≤ E.VSstar (Sanctions.clipS' x₀) := by
  have h := Sanctions.Foundations.FiniteDiscountedTelescope.sum_add_terminal_add_gap_le
    (β := E.β_S) (δ := E.stageGainFloor) E.hβS0.le
    (V := fun t => E.VSstar (Sanctions.clipS' (E.reliefState x₀ t)))
    (u := fun t => E.toParams.U_S (E.reliefState x₀ t) (a t) 0) T
    (fun t _ => by
      have := E.sender_relief_step hZ (E.reliefState_mem hx₀ t) (ha t)
      simpa [reliefState_succ] using this)
  simpa [senderReliefValue] using h

/-- **The Target weakly loses from the spell**, by at least its discounted
compliance cost; for every compliance sequence in `[0,1]`. -/
theorem targetReliefValue_add_cost_le (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) (T : ℕ) :
    (E.targetReliefValue hTM) hmono a x₀ T + E.ℓlo * ∑ t ∈ range T, E.β_T ^ t * a t
      ≤ E.VTstar hTM hmono (Sanctions.clipS' x₀) := by
  have h := Sanctions.Foundations.FiniteDiscountedTelescope.sum_add_terminal_add_residual_le
    (β := E.β_T) E.hβT0.le
    (V := fun t => E.VTstar hTM hmono (Sanctions.clipS' (E.reliefState x₀ t)))
    (u := fun t => E.toParams.U_T (E.reliefState x₀ t) (a t) 0)
    (D := fun t => E.ℓlo * a t) T
    (fun t _ => by
      have := (E.target_relief_step hTM) hmono (E.reliefState_mem hx₀ t) (ha t)
      simpa [reliefState_succ] using this)
  have hsum : ∑ t ∈ range T, E.β_T ^ t * (E.ℓlo * a t)
      = E.ℓlo * ∑ t ∈ range T, E.β_T ^ t * a t := by
    rw [mul_sum]
    exact sum_congr rfl fun t _ => by ring
  rw [hsum] at h
  simpa [targetReliefValue] using h

/-- The Sender's loss is strict for a nonempty spell. -/
theorem senderReliefValue_lt (hZ : E.ZeroSanctionNoGain) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {T : ℕ} (hT : 0 < T) :
    E.senderReliefValue a x₀ T + E.stageGainFloor ≤ E.VSstar (Sanctions.clipS' x₀) := by
  have h := E.senderReliefValue_add_loss_le hZ hx₀ ha T
  have hgeom := Sanctions.Foundations.FiniteDiscountedTelescope.one_le_geom_sum E.hβS0.le hT
  have hδ := E.stageGainFloor_pos
  nlinarith [h, hgeom, hδ]

/-- The Target's weak loss. -/
theorem targetReliefValue_le (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) (T : ℕ) :
    (E.targetReliefValue hTM) hmono a x₀ T ≤ E.VTstar hTM hmono (Sanctions.clipS' x₀) := by
  have h := (E.targetReliefValue_add_cost_le hTM) hmono hx₀ ha T
  have hsum : 0 ≤ ∑ t ∈ range T, E.β_T ^ t * a t :=
    sum_nonneg fun t _ => mul_nonneg (pow_nonneg E.hβT0.le t) (ha t).1
  have := mul_nonneg E.hℓlo.le hsum
  linarith

/-- **Defiance is the Target's best compliance sequence during the spell**: with
the sanction fixed at zero, compliance changes neither the state path nor the
continuation and costs at least `ℓ_lo·a` (T2). -/
theorem targetReliefValue_le_defiance
    (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (T : ℕ) :
    (E.targetReliefValue hTM) hmono a x₀ T
      ≤ (E.targetReliefValue hTM) hmono (fun _ => 0) x₀ T := by
  unfold targetReliefValue
  have hterm : ∀ t ∈ range T,
      E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) (a t) 0
        ≤ E.β_T ^ t * E.toParams.U_T (E.reliefState x₀ t) 0 0 := by
    intro t _
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg E.hβT0.le t)
    have h := E.hUT_costLo _ (E.reliefState_mem hx₀ t) 0 zero_mem_I 0 zero_mem_I (a t) (ha t)
      (ha t).1
    have := mul_nonneg E.hℓlo.le (ha t).1
    change E.U_T (E.reliefState x₀ t) (a t) 0 ≤ E.U_T (E.reliefState x₀ t) 0 0
    linarith
  linarith [sum_le_sum hterm]

/-- **The two incumbents' gains from a nonempty spell sum to at most `−G_S`.** -/
theorem relief_joint_loss (hZ : E.ZeroSanctionNoGain) (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {T : ℕ}
    (hT : 0 < T) :
    E.senderReliefValue a x₀ T + (E.targetReliefValue hTM) hmono a x₀ T + E.stageGainFloor
      ≤ E.VSstar (Sanctions.clipS' x₀) + E.VTstar hTM hmono (Sanctions.clipS' x₀) := by
  have hS := E.senderReliefValue_lt hZ hx₀ ha hT
  have hTt := (E.targetReliefValue_le hTM) hmono hx₀ ha T
  linarith

/-- **No lump-sum number makes a nonempty spell weakly acceptable to both
incumbents.** If `τ` is taken from the Sender's value of the spell and added to
the Target's, at least one of them is strictly worse off than in the
equilibrium. (Read as a date-zero side payment this presupposes quasilinear
transfers; the statement is about the constructed values.) -/
theorem no_date_zero_transfer_supports_relief (hZ : E.ZeroSanctionNoGain) (hTM : E.LossOffset)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) {T : ℕ}
    (hT : 0 < T) :
    ¬ ∃ τ : ℝ, E.VSstar (Sanctions.clipS' x₀) ≤ E.senderReliefValue a x₀ T - τ ∧
        E.VTstar hTM hmono (Sanctions.clipS' x₀) ≤ (E.targetReliefValue hTM) hmono a x₀ T + τ := by
  rintro ⟨τ, h1, h2⟩
  have h := (E.relief_joint_loss hZ hTM) hmono hx₀ ha hT
  have hδ := E.stageGainFloor_pos
  linarith

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- **The statement at the constructed equilibrium under the rally margin**: the
terminal values are that equilibrium's own `V_S` and `V_T`. The form at every
full-defiance equilibrium, with a nondecreasing response in place of the rally margin,
is `relief_participation_of_policy_zero` (renovation item BH3.4). General in `F`; on the
two-sided extension since renovation item BJ3.1 (2026-10-07), as the rally margin reads the
two-sided curvature data. -/
theorem relief_participation_of_margin (hZ : E.ZeroSanctionNoGain) (hTM : E.LossOffset)
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
      ≤ ((E.equilibriumTop_of_margin hTM) hmargin).V_T (Sanctions.clipS' x₀)) :=
  ⟨E.senderReliefValue_lt hZ hx₀ ha hT,
    (E.targetReliefValue_le hTM) (E.responsePath_monotoneOn_of_margin hmargin) hx₀ ha T⟩

end ChordEconomyTwoSided

/-! ## The quadratic–linear family: the floor in closed form -/

/-- **On the family the stage-gain floor is `u₀²/(2q)`** (`u_lo = u₀ ≤ q = Q̄`).
Renovation item BJ2.3 (2026-10-07): the floor condition `u₀ ≤ q` is the hypothesis `hu`
(it followed from the family's interiority field, which is gone; `u₀_le_q` derives it from
interiority). General in `F`. -/
theorem PlacableEconomyF.toChord_stageGainFloor (E : PlacableEconomyF) (hu : E.u₀ ≤ E.q) :
    E.toChord.stageGainFloor = E.u₀ ^ 2 / (2 * E.q) := by
  have hq := E.hq
  have hs : E.toChord.gainSanction = E.u₀ / E.q := by
    change min 1 (E.u₀ / E.q) = E.u₀ / E.q
    exact min_eq_right ((div_le_one hq).2 hu)
  unfold ChordEconomy.stageGainFloor
  rw [hs]
  change E.u₀ / E.q * (E.u₀ - E.q * (E.u₀ / E.q) / 2) = E.u₀ ^ 2 / (2 * E.q)
  field_simp
  ring

/-! ## The margin cannot be dropped (Rule 11)

`lossOffsetParams` lies outside the family — its loss-offset margin fails
(`lossOffset_fails`) — yet its constructed equilibrium has defiance as the unique
Target optimum. There one imposed zero-sanction period is worth `1/18` more to
the Target than the equilibrium, at every feasible state: compliance is costly,
but relief that is simply imposed requires none. Affine, and marked so
(Rule 22). -/

/-- **Outside the loss-offset margin an imposed relief period benefits the
Target**, by exactly `1/18` at every feasible state. -/
theorem lossOffset_relief_period_benefits_target {x : ℝ} (hx : x ∈ Sanctions.I) :
    lossOffsetEquilibrium.V_T (Sanctions.clipS' x) + 1 / 18
      = lossOffsetParams.U_T x 0 0
        + lossOffsetParams.β_T
          * lossOffsetEquilibrium.V_T (Sanctions.clipS' (lossOffsetParams.F x 0)) := by
  have hFmem : lossOffsetParams.F x 0 ∈ Sanctions.I := lo_F_mem hx ⟨le_rfl, zero_le_one⟩
  change loVT (Sanctions.clipS' x) + 1 / 18
      = lossOffsetParams.U_T x 0 0 + lossOffsetParams.β_T * loVT (Sanctions.clipS' _)
  simp only [loVT, ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem hx,
    Sanctions.clipS'_val_eq_of_mem hFmem]
  simp only [lo_U_T, lo_F, lo_β_T, symU_T, affineF]
  ring

end

#print axioms ChordEconomy.stage_gain_ge
#print axioms ChordEconomy.sender_relief_step
#print axioms ChordEconomy.target_relief_step
#print axioms ChordEconomy.senderReliefValue_add_loss_le
#print axioms ChordEconomy.targetReliefValue_add_cost_le
#print axioms ChordEconomy.targetReliefValue_le_defiance
#print axioms ChordEconomy.relief_joint_loss
#print axioms ChordEconomy.no_date_zero_transfer_supports_relief
#print axioms ChordEconomyTwoSided.relief_participation_of_margin
#print axioms PlacableEconomyF.toChord_stageGainFloor
#print axioms lossOffset_relief_period_benefits_target

end Examples
end Sanctions
