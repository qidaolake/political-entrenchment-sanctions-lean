/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Theory.LockIn.DynamicTopLockIn

/-!
# Sub-interval lock-in: ratcheting on a basin that does not reach the top state

The tree's lock-in machinery (`dynamicTopLockInPathF_mono`,
`dynamicTopLockInSanctionsF_mono`) requires the ratchet `x ≤ R(x)` on an interval
running all the way up to the top state `1`.  That is exactly what
`Sanctions.no_upper_basin_floor_of_top_lt_one` rules out for any economy whose
top sanction is interior --- so at such economies the existing route to a
monotone sanction path is closed.

This file supplies the sub-interval siblings, over an arbitrary right endpoint
`b ≤ 1`, and identifies the exact price of not reaching the top.

## The price: the right endpoint must be a fixed point

`dynamicTopLockIn_subinterval_forces_fixed_endpoint` --- if `[a,b]` carries the
ratchet *and* is forward invariant, then the realised rule fixes `b` exactly,
`R(b) = b`.  The argument is purely kinematic: invariance applied at `b` gives
`F b (R b) ≤ b = F b b`, so `R b ≤ b`, while the ratchet gives `R b ≥ b`.  It
consumes only `F_diag` (applying the current state as the sanction leaves the
state put) and strict monotonicity of `F b ·`.

So the two conditions one wants together --- sanctions never falling below the
state, and the basin never being left --- meet only at a steady state of the
closed loop.  That is not a defect of any particular economy; it is forced by
the transition structure.

`dynamicTopLockInStepF_mem_subinterval` is the converse: ratchet plus a
monotone rule plus `R(b) ≤ b` gives invariance.  Together they characterise
when a sub-interval works (`dynamicTopLockIn_subinterval_iff`).

## Rule compliance

**Rule 3.** Nothing is added to the assumption surface: these consume only
existing `Params` fields (`F_mem`, `F_mono_x`, `F_mono_s`, `F_diag`).  The local
monotonicity hypothesis mirrors the one `dynamicTopLockInSanctionsF_mono`
already takes.

**Rule 5.** Stated over an arbitrary `Params`, an arbitrary feasible rule, and
an arbitrary right endpoint; witness instantiations are corollaries elsewhere.

**Rule 19.** These mention `Params` and the project's own lock-in path
constructions, so they are model wiring and belong here rather than in
`Foundations/`.
-/

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## PART 1 — SUB-INTERVAL LOCK-IN, PARAMETRIC

The existing lock-in theorems (`Theory/LockIn/DynamicTopLockIn.lean`) all require the
ratchet floor on `Icc xbar 1`, i.e. reaching the TOP state.  At P3 that is impossible
(`Foundations/Basic.lean` `no_upper_basin_floor_of_top_lt_one` +
`mwShockedOne_no_top_floor`).  The theorems below are the sub-interval siblings: the
right endpoint is an arbitrary `b ≤ 1`, and the price of not reaching `1` is that the
rule must FIX `b`.  No new assumption: they consume only the existing `Params` fields
`F_mem`, `F_mono_x`, `F_mono_s`, `F_diag`. -/

/-- **The obstruction.**  If `[a,b]` carries the ratchet and is forward invariant, then
the realized rule fixes the right endpoint exactly.  Purely kinematic: only `F b b = b`
and strict monotonicity of `F b ·` are used. -/
theorem dynamicTopLockIn_subinterval_forces_fixed_endpoint
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hstrict : StrictMono fun s => p.F b s)
    (h_ratchet : ∀ x ∈ Set.Icc a b, x ≤ p.dynamicTopRealizedRule V_S α x)
    (h_inv : ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b) :
    p.dynamicTopRealizedRule V_S α b = b := by
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  refine le_antisymm ?_ (h_ratchet b hb)
  by_contra hcon
  rw [not_le] at hcon
  have h1 : p.F b b < p.F b (p.dynamicTopRealizedRule V_S α b) := hstrict hcon
  rw [p.F_diag b] at h1
  exact absurd (h_inv b hb).2 (not_le.mpr h1)

/-- **Sub-interval forward invariance.**  Ratchet on `[a,b]` + monotone rule on `[a,b]`
+ the rule fixing `b` ⇒ `[a,b]` is invariant. -/
theorem dynamicTopLockInStepF_mem_subinterval
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ}
    (h_ratchet : ∀ x ∈ Set.Icc a b, x ≤ p.dynamicTopRealizedRule V_S α x)
    (h_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (h_fix : p.dynamicTopRealizedRule V_S α b ≤ b)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b := by
  have hab : a ≤ b := le_trans hx.1 hx.2
  have hlow : x ≤ p.dynamicTopLockInStepF V_S α x := by
    have h := p.F_mono_s x (h_ratchet x hx)
    dsimp only at h
    rwa [p.F_diag x] at h
  refine ⟨le_trans hx.1 hlow, ?_⟩
  calc p.F x (p.dynamicTopRealizedRule V_S α x)
      ≤ p.F b (p.dynamicTopRealizedRule V_S α x) := p.F_mono_x _ hx.2
    _ ≤ p.F b (p.dynamicTopRealizedRule V_S α b) :=
        p.F_mono_s b (h_mono hx ⟨hab, le_rfl⟩ hx.2)
    _ ≤ p.F b b := p.F_mono_s b h_fix
    _ = b := p.F_diag b

/-- Every state on the sub-interval path stays on the sub-interval. -/
theorem dynamicTopLockInPathF_mem_subinterval
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ}
    (h_ratchet : ∀ x ∈ Set.Icc a b, x ≤ p.dynamicTopRealizedRule V_S α x)
    (h_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (h_fix : p.dynamicTopRealizedRule V_S α b ≤ b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    ∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Icc a b := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ n ih =>
    simp only [dynamicTopLockInPathF_succ]
    exact p.dynamicTopLockInStepF_mem_subinterval V_S α h_ratchet h_mono h_fix ih

/-- **Monotone state path on the sub-interval.** -/
theorem dynamicTopLockInPathF_mono_subinterval
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ}
    (h_ratchet : ∀ x ∈ Set.Icc a b, x ≤ p.dynamicTopRealizedRule V_S α x)
    (h_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (h_fix : p.dynamicTopRealizedRule V_S α b ≤ b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Monotone (p.dynamicTopLockInPathF V_S α x₀) := by
  apply monotone_nat_of_le_succ
  intro n
  have hmem := p.dynamicTopLockInPathF_mem_subinterval V_S α h_ratchet h_mono h_fix hx₀ n
  simp only [dynamicTopLockInPathF_succ]
  have h := p.F_mono_s (p.dynamicTopLockInPathF V_S α x₀ n) (h_ratchet _ hmem)
  dsimp only at h
  rwa [p.F_diag] at h

/-- **Monotone sanctions on the sub-interval.**  The realized equilibrium sanction
sequence is non-decreasing forever. -/
theorem dynamicTopLockInSanctionsF_mono_subinterval
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ}
    (h_ratchet : ∀ x ∈ Set.Icc a b, x ≤ p.dynamicTopRealizedRule V_S α x)
    (h_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b))
    (h_fix : p.dynamicTopRealizedRule V_S α b ≤ b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Monotone (p.dynamicTopLockInSanctionsF V_S α x₀) := by
  intro m n hmn
  exact h_mono
    (p.dynamicTopLockInPathF_mem_subinterval V_S α h_ratchet h_mono h_fix hx₀ m)
    (p.dynamicTopLockInPathF_mem_subinterval V_S α h_ratchet h_mono h_fix hx₀ n)
    (p.dynamicTopLockInPathF_mono_subinterval V_S α h_ratchet h_mono h_fix hx₀ hmn)

/-- **The characterization.**  Given a monotone rule and a strictly `s`-monotone
transition, a sub-interval carries the ratchet-plus-invariance package **iff** the rule
ratchets on it and fixes its right endpoint. -/
theorem dynamicTopLockIn_subinterval_iff
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hstrict : StrictMono fun s => p.F b s)
    (h_mono : MonotoneOn (p.dynamicTopRealizedRule V_S α) (Set.Icc a b)) :
    ((∀ x ∈ Set.Icc a b, x ≤ p.dynamicTopRealizedRule V_S α x) ∧
        ∀ x ∈ Set.Icc a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Icc a b)
      ↔ ((∀ x ∈ Set.Icc a b, x ≤ p.dynamicTopRealizedRule V_S α x) ∧
        p.dynamicTopRealizedRule V_S α b = b) := by
  constructor
  · rintro ⟨hr, hi⟩
    exact ⟨hr, p.dynamicTopLockIn_subinterval_forces_fixed_endpoint V_S α hab hstrict hr hi⟩
  · rintro ⟨hr, hf⟩
    exact ⟨hr, fun x hx => p.dynamicTopLockInStepF_mem_subinterval V_S α hr h_mono hf.le hx⟩

/-! ## Strict escalation, parametrically

The project exhibits strictly increasing sanction paths at one economy and
non-decreasing ones at another, and it is tempting to describe the difference
as a property of those two constructions.  It is not: strict escalation follows
from a condition on the realised rule alone, stated here over an arbitrary
`Params`, an arbitrary equilibrium-realised rule, and an arbitrary sub-interval.

The condition is exactly what one would guess.  If at every state of `[a, b)`
the equilibrium sanction strictly exceeds the state --- the Sender more than
replaces the current level of entrenchment --- then the political state strictly
rises; and if the realised rule is in addition strictly increasing there, the
sanction strictly rises with it, at every date, forever.
-/

/-! ### The strictness hypothesis is necessary, not a convenience

`dynamicTopLockInStepF_gt_self` below carries `hup`, *local upward adjustment*
at the state: a feasible sanction above the state strictly raises it,
`x < s ⇒ x < F(x,s)`.  The `Params` field `F_mono_s` does *not* supply it — it
gives only `Monotone` — so it deserves a justification, and here is one,
machine-checked rather than argued: the conclusion of the step theorem is
**equivalent** to the local strictness `F x x < F x (R x)`, so nothing is bought
by assuming it.  Where the transition is flat in the sanction, a strict
escalation step is impossible for *every* equilibrium and *every* rule.

The exact necessary condition is stated in terms of the endogenous realised rule
`R`, so it is unusable as a hypothesis.  `hup` is the primitive-side sufficient
condition for it, read only at the states of `[a, b)` and only for sanctions
above the state.  Until BG2.3 (2026-10-06) the theorems asked instead that `F`
be strictly increasing in the sanction at *every* state, a global condition the
witnesses had to verify everywhere; that form, and the two-sided strict
adjustment (F5), both imply `hup` and survive as the `_of_strictMono_s` and
`_of_strictAdjustment` corollaries below. -/

/-- **A strict step is exactly a local strict increase of `F` in the sanction.**
Immediate from `F_diag`, and the reason `hFs` below is the right hypothesis
rather than a strengthening chosen to make the proof go through. -/
theorem step_gt_self_iff_local_strict
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (α : ℝ → ℝ) (x : ℝ) :
    x < p.dynamicTopLockInStepF V_S α x
      ↔ p.F x x < p.F x (p.dynamicTopRealizedRule V_S α x) := by
  constructor
  · intro h; rwa [p.F_diag x]
  · intro h; rw [p.F_diag x] at h; exact h

/-- **Flat transition ⇒ no strict escalation, ever.**  If the transition does not
move with the sanction at `x`, then no equilibrium and no rule can produce a
strict step there.  So the strictness `hup` assumes is not an optional
convenience: without it the conclusion is unavailable, not merely unproved. -/
theorem no_strict_step_of_flat_in_sanction
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (α : ℝ → ℝ) (x : ℝ)
    (hflat : ∀ s s', p.F x s = p.F x s') :
    ¬ x < p.dynamicTopLockInStepF V_S α x := by
  rw [p.step_gt_self_iff_local_strict V_S α x,
    hflat x (p.dynamicTopRealizedRule V_S α x)]
  exact lt_irrefl _

/-- **Strict monotonicity in the sanction gives local upward adjustment.**
If `F x ·` is strictly increasing, a sanction above the state lifts it:
`x = F x x < F x s`. General in `F`; the bridge from the pre-BG2.3 hypothesis
to `hup`. -/
theorem localUpwardAdjustment_of_strictMono_s {x : ℝ}
    (hFs : StrictMono (fun s => p.F x s)) :
    ∀ s ∈ Sanctions.I, x < s → x < p.F x s := by
  intro s _ hxs
  have h := hFs hxs
  dsimp only at h
  rwa [p.F_diag x] at h

/-- **Strict adjustment gives local upward adjustment at every nonnegative
state.** The raising half of (F5) applies once `x` is feasible, and
`0 ≤ x < s ≤ 1` makes it so. General in `F` (BG2.3). -/
theorem localUpwardAdjustment_of_strictAdjustment (hAdj : p.StrictAdjustment)
    {x : ℝ} (hx0 : 0 ≤ x) :
    ∀ s ∈ Sanctions.I, x < s → x < p.F x s := fun _ hs hxs =>
  hAdj.self_lt_F_of_lt_s ⟨hx0, (hxs.trans_le hs.2).le⟩ hs hxs

/-- **One strict step.**  If the realised sanction strictly exceeds the current
state and the transition adjusts upward at that state — a feasible sanction
above the state strictly raises it — the successor state strictly exceeds the
current state.  Economically: a Sender who more than replaces today's
entrenchment raises it tomorrow, provided sanctions above the state bite there.

General in `F`; the realised sanction is feasible, so `hup` applies to it
directly.  Since BG2.3 (2026-10-06) the hypothesis is `hup`, local upward
adjustment at `x`, in place of strict monotonicity of `F x ·`; the old form is
`dynamicTopLockInStepF_gt_self_of_strictMono_s`, and (F5) gives
`dynamicTopLockInStepF_gt_self_of_strictAdjustment`.

On the hypothesis `hup`, see `no_strict_step_of_flat_in_sanction` above: it is
the primitive-side form of a condition the conclusion itself forces. -/
theorem dynamicTopLockInStepF_gt_self
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (α : ℝ → ℝ)
    {x : ℝ} (hup : ∀ s ∈ Sanctions.I, x < s → x < p.F x s)
    (hR : x < p.dynamicTopRealizedRule V_S α x) :
    x < p.dynamicTopLockInStepF V_S α x :=
  hup _ (p.dynamicTopRealizedRule_mem V_S α x) hR

/-- The pre-BG2.3 form of `dynamicTopLockInStepF_gt_self`: strict monotonicity
of `F x ·`. General in `F`. -/
theorem dynamicTopLockInStepF_gt_self_of_strictMono_s
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (α : ℝ → ℝ)
    {x : ℝ} (hFs : StrictMono (fun s => p.F x s))
    (hR : x < p.dynamicTopRealizedRule V_S α x) :
    x < p.dynamicTopLockInStepF V_S α x :=
  p.dynamicTopLockInStepF_gt_self V_S α (p.localUpwardAdjustment_of_strictMono_s hFs) hR

/-- `dynamicTopLockInStepF_gt_self` under strict adjustment (F5) at a
nonnegative state. General in `F` (BG2.3). -/
theorem dynamicTopLockInStepF_gt_self_of_strictAdjustment
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (α : ℝ → ℝ)
    (hAdj : p.StrictAdjustment) {x : ℝ} (hx0 : 0 ≤ x)
    (hR : x < p.dynamicTopRealizedRule V_S α x) :
    x < p.dynamicTopLockInStepF V_S α x :=
  p.dynamicTopLockInStepF_gt_self V_S α
    (p.localUpwardAdjustment_of_strictAdjustment hAdj hx0) hR

/-- **The state path strictly increases.**  Under the step condition on all of
`[a, b)` together with invariance of `[a, b)`, every step is a strict increase,
so the path is `StrictMono`.

General in `F`.  Since BG2.3 (2026-10-06) the transition hypothesis is `hup`,
local upward adjustment on `[a, b)` only — at each state of the interval a
feasible sanction above the state strictly raises it — in place of strict
monotonicity of `F` in the sanction at every state.  The old form is
`dynamicTopLockInPathF_strictMono_of_gt_self_of_strictMono_s`; with `0 ≤ a`,
(F5) gives `dynamicTopLockInPathF_strictMono_of_gt_self_of_strictAdjustment`. -/
theorem dynamicTopLockInPathF_strictMono_of_gt_self
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (α : ℝ → ℝ)
    {a b x₀ : ℝ}
    (hup : ∀ x ∈ Set.Ico a b, ∀ s ∈ Sanctions.I, x < s → x < p.F x s)
    (hgt : ∀ x ∈ Set.Ico a b, x < p.dynamicTopRealizedRule V_S α x)
    (hinv : ∀ x ∈ Set.Ico a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Ico a b)
    (hx₀ : x₀ ∈ Set.Ico a b) :
    StrictMono (p.dynamicTopLockInPathF V_S α x₀) := by
  have hmem : ∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Ico a b := by
    intro n
    induction n with
    | zero => simpa using hx₀
    | succ k ih => rw [dynamicTopLockInPathF_succ]; exact hinv _ ih
  have hstep : ∀ n, p.dynamicTopLockInPathF V_S α x₀ n
      < p.dynamicTopLockInPathF V_S α x₀ (n + 1) := by
    intro n
    rw [dynamicTopLockInPathF_succ]
    exact p.dynamicTopLockInStepF_gt_self V_S α (hup _ (hmem n)) (hgt _ (hmem n))
  exact strictMono_nat_of_lt_succ hstep

/-- The pre-BG2.3 form of `dynamicTopLockInPathF_strictMono_of_gt_self`:
strict monotonicity of `F` in the sanction at every state. General in `F`. -/
theorem dynamicTopLockInPathF_strictMono_of_gt_self_of_strictMono_s
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (α : ℝ → ℝ)
    {a b x₀ : ℝ}
    (hFs : ∀ x, StrictMono (fun s => p.F x s))
    (hgt : ∀ x ∈ Set.Ico a b, x < p.dynamicTopRealizedRule V_S α x)
    (hinv : ∀ x ∈ Set.Ico a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Ico a b)
    (hx₀ : x₀ ∈ Set.Ico a b) :
    StrictMono (p.dynamicTopLockInPathF V_S α x₀) :=
  p.dynamicTopLockInPathF_strictMono_of_gt_self V_S α
    (fun x _ => p.localUpwardAdjustment_of_strictMono_s (hFs x)) hgt hinv hx₀

/-- `dynamicTopLockInPathF_strictMono_of_gt_self` under strict adjustment (F5),
for an interval with nonnegative left end `0 ≤ a`. General in `F` (BG2.3). -/
theorem dynamicTopLockInPathF_strictMono_of_gt_self_of_strictAdjustment
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (α : ℝ → ℝ)
    (hAdj : p.StrictAdjustment) {a b x₀ : ℝ} (ha : 0 ≤ a)
    (hgt : ∀ x ∈ Set.Ico a b, x < p.dynamicTopRealizedRule V_S α x)
    (hinv : ∀ x ∈ Set.Ico a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Ico a b)
    (hx₀ : x₀ ∈ Set.Ico a b) :
    StrictMono (p.dynamicTopLockInPathF V_S α x₀) :=
  p.dynamicTopLockInPathF_strictMono_of_gt_self V_S α
    (fun _ hx => p.localUpwardAdjustment_of_strictAdjustment hAdj (ha.trans hx.1))
    hgt hinv hx₀

/-- **The sanction path strictly increases.**  Adding strict monotonicity of the
realised rule on the interval, the sanction sequence inherits the strict
increase of the state path.

Economically: the Sender both over-replaces the current entrenchment (so the
state climbs) and responds more aggressively to a more entrenched state (so the
sanction climbs with it). Neither alone suffices.

General in `F`.  Since BG2.3 (2026-10-06) the transition hypothesis is `hup`,
local upward adjustment on `[a, b)`, in place of strict monotonicity of `F` in
the sanction at every state; the old form is
`dynamicTopLockInSanctionsF_strictMono_of_gt_self_of_strictMono_s`, and (F5)
with `0 ≤ a` gives the `_of_strictAdjustment` corollary. -/
theorem dynamicTopLockInSanctionsF_strictMono_of_gt_self
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (α : ℝ → ℝ)
    {a b x₀ : ℝ}
    (hup : ∀ x ∈ Set.Ico a b, ∀ s ∈ Sanctions.I, x < s → x < p.F x s)
    (hgt : ∀ x ∈ Set.Ico a b, x < p.dynamicTopRealizedRule V_S α x)
    (hinv : ∀ x ∈ Set.Ico a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Ico a b)
    (hrule : StrictMonoOn (p.dynamicTopRealizedRule V_S α) (Set.Ico a b))
    (hx₀ : x₀ ∈ Set.Ico a b) :
    StrictMono (p.dynamicTopLockInSanctionsF V_S α x₀) := by
  have hmem : ∀ n, p.dynamicTopLockInPathF V_S α x₀ n ∈ Set.Ico a b := by
    intro n
    induction n with
    | zero => simpa using hx₀
    | succ k ih => rw [dynamicTopLockInPathF_succ]; exact hinv _ ih
  have hpath := p.dynamicTopLockInPathF_strictMono_of_gt_self V_S α hup hgt hinv hx₀
  intro m n hmn
  exact hrule (hmem m) (hmem n) (hpath hmn)

/-- The pre-BG2.3 form of `dynamicTopLockInSanctionsF_strictMono_of_gt_self`:
strict monotonicity of `F` in the sanction at every state. General in `F`. -/
theorem dynamicTopLockInSanctionsF_strictMono_of_gt_self_of_strictMono_s
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (α : ℝ → ℝ)
    {a b x₀ : ℝ}
    (hFs : ∀ x, StrictMono (fun s => p.F x s))
    (hgt : ∀ x ∈ Set.Ico a b, x < p.dynamicTopRealizedRule V_S α x)
    (hinv : ∀ x ∈ Set.Ico a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Ico a b)
    (hrule : StrictMonoOn (p.dynamicTopRealizedRule V_S α) (Set.Ico a b))
    (hx₀ : x₀ ∈ Set.Ico a b) :
    StrictMono (p.dynamicTopLockInSanctionsF V_S α x₀) :=
  p.dynamicTopLockInSanctionsF_strictMono_of_gt_self V_S α
    (fun x _ => p.localUpwardAdjustment_of_strictMono_s (hFs x)) hgt hinv hrule hx₀

/-- `dynamicTopLockInSanctionsF_strictMono_of_gt_self` under strict adjustment
(F5), for an interval with nonnegative left end `0 ≤ a`. General in `F`
(BG2.3). -/
theorem dynamicTopLockInSanctionsF_strictMono_of_gt_self_of_strictAdjustment
    (V_S : BoundedContinuousFunction ↥(Sanctions.S : Set ℝ) ℝ) (α : ℝ → ℝ)
    (hAdj : p.StrictAdjustment) {a b x₀ : ℝ} (ha : 0 ≤ a)
    (hgt : ∀ x ∈ Set.Ico a b, x < p.dynamicTopRealizedRule V_S α x)
    (hinv : ∀ x ∈ Set.Ico a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Ico a b)
    (hrule : StrictMonoOn (p.dynamicTopRealizedRule V_S α) (Set.Ico a b))
    (hx₀ : x₀ ∈ Set.Ico a b) :
    StrictMono (p.dynamicTopLockInSanctionsF V_S α x₀) :=
  p.dynamicTopLockInSanctionsF_strictMono_of_gt_self V_S α
    (fun _ hx => p.localUpwardAdjustment_of_strictAdjustment hAdj (ha.trans hx.1))
    hgt hinv hrule hx₀

/-- **The escalation condition is not vacuous, and it is not automatic.**

The two hypotheses are logically independent: a rule can strictly exceed the
state without being monotone, and can be strictly monotone while lying below the
diagonal. The conjunction is what strict escalation needs, and neither conjunct
is implied by the basin conditions. -/
theorem strict_escalation_needs_both :
    (∃ r : ℝ → ℝ, (∀ x ∈ Set.Ico (0:ℝ) 1, x < r x)
        ∧ ¬ StrictMonoOn r (Set.Ico (0:ℝ) 1))
    ∧ (∃ r : ℝ → ℝ, StrictMonoOn r (Set.Ico (0:ℝ) 1)
        ∧ ¬ (∀ x ∈ Set.Ico (0:ℝ) 1, x < r x)) := by
  constructor
  · refine ⟨fun _ => 2, fun x hx => by linarith [hx.2], ?_⟩
    intro hmono
    have := hmono (a := 0) ⟨le_refl 0, by norm_num⟩
      (b := 1/2) ⟨by norm_num, by norm_num⟩ (by norm_num)
    exact absurd this (by norm_num)
  · refine ⟨fun x => x / 2, fun x _ y _ hxy => by linarith, ?_⟩
    intro hall
    have := hall (1/2) ⟨by norm_num, by norm_num⟩
    norm_num at this

/-! ## Axiom hygiene (Rule 10) -/

#print axioms dynamicTopLockInStepF_gt_self
#print axioms dynamicTopLockInPathF_strictMono_of_gt_self
#print axioms dynamicTopLockInSanctionsF_strictMono_of_gt_self
#print axioms strict_escalation_needs_both

end Params
end AbstractGame

end

end Sanctions
