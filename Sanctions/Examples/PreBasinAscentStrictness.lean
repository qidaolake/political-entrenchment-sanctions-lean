/-
Sanctions/Examples/PreBasinAscentStrictness.lean

**Pre-basin ascent is properly weaker than strict adjustment** (round BB,
2026-09-28; doc 110 item R7, the strictness side of the localisation).

`Theory/LockIn/LocalisedShockEntry.lean` and its two consumers replace the
transition hypotheses of the shock theorems — strict adjustment F5
(`StrictAdjustment`) or global full-sanction ascent `hF_top` on `[0, 1)` — by
pre-basin ascent: full sanction strictly raises every state in `[0, x̄]`. The
implication old ⇒ new is proved there. This file shows that it cannot be
reversed: an economy exists whose transition satisfies pre-basin ascent below
`x̄ = 1/2` but fails `hF_top` and hence F5.

**The witness.** The plateau transition

  `plateauF c x s = max (min s x) (min s (max x c))`

moves the state all the way to the sanction when the sanction is below the
state or below `c`, and stops at `max x c` otherwise; at full sanction
`plateauF c x 1 = max x c`. It is continuous, weakly increasing in both
arguments, and fixes the diagonal, so it is a legitimate general transition.
Full sanction strictly raises every state below `c` and leaves every state in
`[c, 1]` where it is. `plateauParams c` is the certificate economy
`eeCertParams` with its affine transition replaced by `plateauF c`; no other
field of `Params` mentions `F`, so the other fields carry over unchanged.

At `c = 3/4`:

* pre-basin ascent holds on `[0, 1/2]` (`plateauParams_preBasinAscent`);
* `hF_top` fails at `x = 3/4` (`plateauParams_not_hF_top`), so F5 fails
  (`plateauParams_not_strictAdjustment`);
* the full-sanction path from `0` does **not** converge to `1` — it never
  exceeds `3/4` (`plateauParams_shockPathF_not_tendsto_one`). This is the
  Lean artifact behind the remark that `shockPathF_tendsto_one` does not
  localise: its conclusion is false under pre-basin ascent alone;
* yet finite entry into `[1/2, 1]` holds from every feasible start
  (`plateauParams_uniform_entry`), by the localised lemma — a conclusion the
  old lemmas cannot deliver here, since their hypothesis fails.

Scope (Rule 9A): an existence certificate for the *hypothesis-level*
separation, nothing more. It says the transition conditions of the localised
theorems are properly weaker than those of the pinned ones. It does **not**
exhibit a compliance certificate, a persistence package or a Sender-side
basin at a transition failing F5, so it does not show that the localised
certificate theorems apply to an economy the pinned ones miss; that
generality remains unwitnessed at the level of the full theorems.

Rule 22: the witness transition is non-affine at every weight
(`plateauF_ne_affineF`: no `affineF d` agrees with `plateauF (3/4)` at both
`(0, 1)` and `(3/4, 1)`). It also fails F5, which every affine law with
`δ ∈ (0, 1)` satisfies. Rule 3: no new assumption; the file
proves facts about one concrete economy. Rule 9B: the economy is a concrete
`def`; its only `Prop`-typed data are the `Params` proof fields.
-/

import Sanctions.Examples.EECertWitness
import Sanctions.Theory.LockIn.LocalisedShockEntry

namespace Sanctions
namespace Examples

open Set Filter Topology AbstractGame

noncomputable section

/-- **The plateau transition.** `plateauF c x s = max (min s x) (min s (max x c))`:
the next state equals the sanction when the sanction lies below the state,
and equals `min s (max x c)` otherwise, so a sanction above the state lifts it
at most to `max x c`. -/
def plateauF (c : ℝ) (x s : ℝ) : ℝ := max (min s x) (min s (max x c))

/-- Full sanction moves a feasible state to `max x c`. -/
theorem plateauF_one {c x : ℝ} (hx : x ≤ 1) (hc : c ≤ 1) :
    plateauF c x 1 = max x c := by
  unfold plateauF
  rw [min_eq_right hx, min_eq_right (max_le hx hc)]
  exact max_eq_right (le_max_left x c)

/-- **The certificate economy with a plateau transition.** Every field of
`eeCertParams` except the transition and its five structural fields,
which are proved for `plateauF c`. -/
def plateauParams (c : ℝ) : AbstractGame.Params :=
  { eeCertParams with
    F := plateauF c
    F_continuous := by
      unfold plateauF
      exact (continuous_snd.min continuous_fst).max
        (continuous_snd.min (continuous_fst.max continuous_const))
    F_mono_x := by
      intro s
      exact (monotone_const.min monotone_id).max
        (monotone_const.min (monotone_id.max monotone_const))
    F_mono_s := by
      intro x
      exact (monotone_id.min monotone_const).max (monotone_id.min monotone_const)
    F_diag := by
      intro x
      unfold plateauF
      rw [min_self, min_eq_left (le_max_left x c), max_self] }

theorem plateauParams_F (c : ℝ) : (plateauParams c).F = plateauF c := rfl

/-- **The witness transition is not affine, at any weight.** At `c = 3/4` the
plateau law sends both `(0, 1)` and `(3/4, 1)` to `3/4`. An affine law
`(1 − d)x + d·s` sends `(0, 1)` to `d` and `(3/4, 1)` to `3/4 + d/4`, so it
would need `d = 3/4` and `d = 0` at once. Rule 22: this is the proved
non-affineness of the witness. -/
theorem plateauF_ne_affineF (d : ℝ) : plateauF (3/4) ≠ AbstractGame.affineF d := by
  intro h
  have e1 : plateauF (3/4) 0 1 = 3/4 := by
    rw [plateauF_one (x := 0) (c := 3/4) (by norm_num) (by norm_num)]
    exact max_eq_right (by norm_num)
  have e2 : plateauF (3/4) (3/4) 1 = 3/4 := by
    rw [plateauF_one (x := 3/4) (c := 3/4) (by norm_num) (by norm_num)]
    exact max_self _
  rw [h] at e1 e2
  unfold AbstractGame.affineF at e1 e2
  linarith

/-- **Pre-basin ascent holds below the plateau level.** For every threshold
`x̄ < c ≤ 1`, full sanction strictly raises every state in `[0, x̄]`. -/
theorem plateauParams_preBasinAscent {c xbar : ℝ} (hxc : xbar < c) (hc1 : c ≤ 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < (plateauParams c).F x 1 := by
  intro x hx
  rw [plateauParams_F, plateauF_one (by linarith [hx.2]) hc1]
  exact lt_of_lt_of_le (lt_of_le_of_lt hx.2 hxc) (le_max_right x c)

/-- **Global full-sanction ascent fails** when the plateau level is interior:
at `x = c`, full sanction leaves the state at `c`. -/
theorem plateauParams_not_hF_top {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ¬ ∀ x ∈ Set.Ico (0 : ℝ) 1, x < (plateauParams c).F x 1 := by
  intro h
  have hlt := h c ⟨hc0, hc1⟩
  rw [plateauParams_F, plateauF_one hc1.le hc1.le, max_self] at hlt
  exact lt_irrefl c hlt

/-- **Strict adjustment (F5) fails** when the plateau level is interior. -/
theorem plateauParams_not_strictAdjustment {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ¬ (plateauParams c).StrictAdjustment :=
  fun h => plateauParams_not_hF_top hc0 hc1 h.hF_top

/-- The full-sanction path from `0` never exceeds the plateau level. -/
theorem plateauParams_shockPathF_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ n, (plateauParams c).shockPathF 0 n ≤ c := by
  intro n
  induction n with
  | zero => simpa using hc0
  | succ n ih =>
    rw [Params.shockPathF_succ]
    change plateauF c ((plateauParams c).shockPathF 0 n) 1 ≤ c
    rw [plateauF_one (le_trans ih hc1) hc1]
    exact max_le ih le_rfl

/-- **Convergence to saturation does not localise.** Under pre-basin ascent
alone the full-sanction path need not converge to `1`: at an interior plateau
level it stays at or below `c < 1` forever. -/
theorem plateauParams_shockPathF_not_tendsto_one {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ¬ Tendsto ((plateauParams c).shockPathF 0) atTop (𝓝 1) := by
  intro h
  have hev : ∀ᶠ n in atTop, c < (plateauParams c).shockPathF 0 n :=
    h.eventually (eventually_gt_nhds hc1)
  obtain ⟨n, hn⟩ := hev.exists
  exact absurd (plateauParams_shockPathF_le hc0 hc1.le n) (not_le.mpr hn)

/-- **Finite shock entry still holds** at the plateau economy, by the
localised lemma: one duration moves every feasible start into `[1/2, 1]`.
The old lemmas do not apply here, since global ascent fails. -/
theorem plateauParams_uniform_entry :
    ∃ N : ℕ, ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ n ≥ N,
      (plateauParams (3/4)).shockPathF x₀ n ∈ Set.Icc (1/2 : ℝ) 1 :=
  (plateauParams (3/4)).shockPathF_uniform_eventually_in_basin_of_preBasinAscent
    (plateauParams_preBasinAscent (by norm_num) (by norm_num))

/-- **Pre-basin ascent is properly weaker than strict adjustment and than
global ascent (existence certificate, Rule 9A).** There is an economy whose
transition strictly lifts every state in `[0, 1/2]` under full sanction, yet
fails global full-sanction ascent on `[0, 1)`, fails strict adjustment F5,
and has a full-sanction path from `0` that does not converge to `1`. -/
theorem exists_preBasinAscent_not_strictAdjustment :
    ∃ p : AbstractGame.Params,
      (∀ x ∈ Set.Icc (0 : ℝ) (1/2), x < p.F x 1) ∧
      ¬ (∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1) ∧
      ¬ p.StrictAdjustment ∧
      ¬ Tendsto (p.shockPathF 0) atTop (𝓝 1) :=
  ⟨plateauParams (3/4),
    plateauParams_preBasinAscent (by norm_num) (by norm_num),
    plateauParams_not_hF_top (by norm_num) (by norm_num),
    plateauParams_not_strictAdjustment (by norm_num) (by norm_num),
    plateauParams_shockPathF_not_tendsto_one (by norm_num) (by norm_num)⟩

end

#print axioms Sanctions.Examples.plateauF_one
#print axioms Sanctions.Examples.plateauParams_F
#print axioms Sanctions.Examples.plateauF_ne_affineF
#print axioms Sanctions.Examples.plateauParams_preBasinAscent
#print axioms Sanctions.Examples.plateauParams_not_hF_top
#print axioms Sanctions.Examples.plateauParams_not_strictAdjustment
#print axioms Sanctions.Examples.plateauParams_shockPathF_le
#print axioms Sanctions.Examples.plateauParams_shockPathF_not_tendsto_one
#print axioms Sanctions.Examples.plateauParams_uniform_entry
#print axioms Sanctions.Examples.exists_preBasinAscent_not_strictAdjustment

end Examples
end Sanctions
