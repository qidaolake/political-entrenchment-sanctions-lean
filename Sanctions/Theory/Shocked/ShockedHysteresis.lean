/-
Sanctions/Theory/Shocked/ShockedHysteresis.lean

**Step 7 (Goal-3): hysteresis survives the atomless shock as BASIN
FORWARD-INVARIANCE — the high basin is absorbing for the box-shocked closed loop
exactly when the shock half-width is small enough.**

On the high basin the equilibrium Sender response is the high-sanction corner
`σ ≡ 1` (the Rule-1 exogenous-corner / saturated-basin case), so the deterministic
closed loop is `x ↦ F(x, 1)` and the shocked next state is
`x' = clipS(F(x, 1) + η)`, `η ∈ [−h, h]`.

**General in `F` since round BH-6 (item BH6.7, 2026-10-07).** The file used to
specialise `F` to the affine law, binding a bare `{δ : ℝ}` and writing the loop
as `x ↦ (1−δ)x + δ` (axis-2 affine-restricted, Rule 22). It now proves the
result at two levels of generality, and the affine pair is an instance:

* **Over a bare closed loop** `G : ℝ → ℝ` (`basin_forward_invariant_of_closedLoop`,
  `basin_escape_of_closedLoop`): no `Params`, no transition fields. The only
  property of the loop that forward invariance reads is `G xT ≤ G x` for basin
  states `x ≥ xT`, and the budget enters only at the floor, as `h ≤ G xT − xT`.
  The escape result reads nothing about `G` at all beyond its value at `xT`.
* **Over any economy** `p : Params` (`Params.basin_forward_invariant_under_box_shock_generalF`,
  `Params.basin_escape_of_box_shock_wide_generalF`, and the sharp
  `Params.basin_forward_invariant_iff_le_fullShockDrift`): the loop is
  `G := (p.F · 1)`, its monotonicity is the `Params` field `F_mono_x`, and the
  budget is the full-sanction drift at the floor,
  `d_F(xT) := p.fullShockDrift xT = F(xT, 1) − xT` (`Theory/LockIn/LockIn.lean`).
  The basin `[xT, 1]` is forward-invariant under every shock in `[−h, h]`
  **iff** `h ≤ d_F(xT)`, for every transition.
* **The affine pair** `basin_forward_invariant_under_box_shock` and
  `basin_escape_of_box_shock_wide` (bare `δ`, loop `(1−δ)x + δ`, budget
  `δ·(1 − xT)`) now live in `Examples/AffineInstance/LockInShocked.lean` as
  instances of the bare-loop theorems. They keep their names (the
  formalization map cites them) and their validity at `δ = 1`: the affine loop
  meets `G xT ≤ G x` exactly when `δ ≤ 1`, so nothing about `Params`
  (in particular `δ_mem : δ ∈ Ioo 0 1`) is ever imported.

⚠ **Correction (BH6.7).** Earlier versions of this header said that generalising
was "not free, because quantifying over `p : Params` imports `δ_mem` and so
loses the present statements' validity at `δ = 1`" (`AFFINE-GENERALIZATION-PLAN.md`
item D/B). That obstacle is avoided by the bare-loop intermediate above: the
general statements quantify over a loop, not over `Params`, and the affine pair
— including its `δ = 1` case — is an instance of them.

Rule 1's exogenous-shock carve-out does **not** license specialising the loop.
That exception covers the transient externally-imposed high-sanction phase;
these results are about the *resumed natural dynamics* under the derived corner
response `σ ≡ 1`, which is an optimisation outcome and therefore inside Rule 22's
scope. The general statements are what Rule 22 asks for.

**The result.** If the shock half-width satisfies the budget `h ≤ d_F(xT)`, then
for every basin state `x ∈ [xT, 1]` and every realised shock `η ∈ [−h, h]`, the
next state stays in the basin: `x' ∈ [xT, 1]`. Hence the basin `[xT, 1]` is
**forward-invariant** under the box-shocked dynamics — once high, the (noisy)
state stays high with probability one. This is the rigorous, measure-theory-free
core of the "lock-in survives atomless purification" claim: the *support* of the
next-state law never escapes the basin.

The budget is the exact threshold the disprove-first probe pinned for the affine
law (`docs/archive/workflow-scratch/probe_h_dichotomy.lean`): absorption holds iff
`h ≤ δ(1 − xT)`, confirmed to the digit (`xT = 0.65, δ = 1/5 ⇒ h* = 0.07`); at the
affine law `d_F(xT) = δ·(1 − xT)`. Above it the chain mixes across the watershed
and lock-in washes out (the separate step-6 regime). Per the Rule-3 symbol-economy
clause the threshold is the single weak inequality `h ≤ d_F(xT)` among existing
objects, not a new named "width margin" scalar.

**Rule 1 / sole-exception.** `σ ≡ 1` on the basin is the *derived* high-sanction
corner (the realised equilibrium argmax saturates there); the exogenous high-shock
phase that drives the state into the basin in the first place is the CLAUDE.md
Rule-1 sole exception (a transient externally-imposed path), after which these
natural noisy dynamics resume.
-/

import Sanctions.Domain.UnitIntervalProjection
import Sanctions.Theory.LockIn.LockIn

namespace Sanctions
namespace AbstractGame

/-- **`clipS` fixes points of the unit interval.** For `xT ∈ [0, 1]`,
`clipS xT = xT`. -/
theorem clipS_eq_self_of_mem {xT : ℝ} (h0 : 0 ≤ xT) (h1 : xT ≤ 1) :
    Sanctions.clipS xT = xT := by
  unfold Sanctions.clipS
  rw [min_eq_right h1, max_eq_right h0]

/-- **Basin forward-invariance under the atomless box shock, over any closed
loop.** Let `G` be the deterministic basin closed loop (`G x = F(x, 1)` in the
model). If `G` does not map a basin state `x ≥ xT` below where it maps the floor
(`G xT ≤ G x`), the down-shock is no larger than `h` (`−h ≤ η`), and `h` is
within the loop's drift at the floor (`h ≤ G xT − xT`), then the post-shock state
`clipS(G x + η)` lies in `[xT, 1]`. Economically: the floor's own upward drift is
the whole shock budget; every higher basin state drifts to at least where the
floor does.

Rule 22: general — no transition, no `Params`. Compared with the former affine
statement it drops the functional form `G x = (1−δ)x + δ`, the floor's
nonnegativity `0 ≤ xT` (never used: `clipS` already caps at `0`), and the upper
half `η ≤ h` of the box (the clip caps the state at `1`) (BH6.7, 2026-10-07). -/
theorem basin_forward_invariant_of_closedLoop
    {G : ℝ → ℝ} {xT x η h : ℝ}
    (hxT1 : xT ≤ 1)
    (hmono : G xT ≤ G x)
    (hη : -h ≤ η)
    (hbudget : h ≤ G xT - xT) :
    xT ≤ Sanctions.clipS (G x + η)
      ∧ Sanctions.clipS (G x + η) ≤ 1 := by
  refine ⟨?_, (Sanctions.clipS_mem _).2⟩
  unfold Sanctions.clipS
  exact le_max_of_le_right (le_min hxT1 (by linarith))

/-- **Basin forward-invariance under the box shock, for every transition.**
For any economy `p`, with the saturated-basin closed loop `x ↦ F(x, 1)`: if the
shock budget is within the full-sanction drift at the floor,
`h ≤ d_F(xT) = p.fullShockDrift xT = F(xT, 1) − xT`, then every basin state
`x ∈ [xT, 1]` maps under every realised shock `η ≥ −h` back into the basin.

Rule 22: general in `F` — the loop's monotonicity is the `Params` field
`F_mono_x`. Instance of `basin_forward_invariant_of_closedLoop` at
`G := (p.F · 1)` (BH6.7, 2026-10-07). -/
theorem Params.basin_forward_invariant_under_box_shock_generalF
    (p : Params) {xT x η h : ℝ}
    (hxT1 : xT ≤ 1)
    (hx : xT ≤ x)
    (hη : -h ≤ η)
    (hbudget : h ≤ p.fullShockDrift xT) :
    xT ≤ Sanctions.clipS (p.F x 1 + η)
      ∧ Sanctions.clipS (p.F x 1 + η) ≤ 1 :=
  basin_forward_invariant_of_closedLoop (G := fun y => p.F y 1) hxT1
    (p.F_mono_x 1 hx) hη hbudget

/-! ## Step 6 (honest scope): the wash-out regime — above the threshold the basin
LEAKS.

The full step-6 object (a *unique invariant distribution* of the box-smeared
closed-loop Markov chain, with global weak convergence `T^n μ ⇒ λ*`) is the
Hopenhayn–Prescott 1992 Theorem 2 / Stokey–Lucas Theorem 12.12 conclusion under the
**Monotone Mixing Condition**. When this file was written it was **not** formalized:
mathlib provides the weak-convergence base (`Portmanteau`, `LevyProkhorovMetric`,
`Tight`, `ConvergenceInDistribution`) but **lacks** the stochastic order on measures
(Kamae–Krengel–O'Brien / Strassen), Knaster–Tarski on a compact set of measures, and
the MMC convergence engine that HP's argument is built on. It was therefore
**cited**, not re-proved.

**Correction (round BB, 2026-09-28).** The paragraph above is out of date. The
unique invariant law is proved, by a different route: a contraction in the dual
Kantorovich–Rubinstein distance, with existence by Krylov–Bogolyubov and no
stochastic order. For the box-shocked full-sanction chain
`x' = clipS'((1−δ)x + δ + η)` — the affine law —
`Foundations/BoxTransfer.lean` proves uniqueness (`boxTransfer_unique_invariant`)
and geometric convergence (`boxTransfer_dualKR_geometric`), and
`Foundations/KrylovBogolyubov.lean` adds existence
(`boxTransfer_existsUnique_invariant_attracting`: an invariant law exists, is
unique, and attracts every start at rate `(1 − δ)ⁿ`). For a closed-loop drift that
contracts (`L`-Lipschitz with `L < 1`), `Foundations/ClosedLoopBoxTransfer.lean`
proves the same (`closedLoopBoxTransfer_existsUnique_invariant_attracting`, rate
`Lⁿ`). Under a general transition the full-sanction chain `x' = clipS'(F(x, 1) + η)`
has the same unique, attracting law at rate `ghiⁿ` whenever the corner section
`y ↦ F(y, 1)` lies in a state chord band with `0 ≤ glo` and `ghi < 1`
(`closedLoopBoxTransfer_existsUnique_invariant_attracting_of_stateChordBand`; round
BH-2, item BH2.11). What stays cited is HP's MMC route for a drift that does not
contract. The `L < 1` hypothesis provably fails at the strong-rally witness rule,
the P3 myopic realized rule `clip((9/8)x − 1/12)` under every affine transition
(`affineP3ClosedLoopDrift_lipConst_ge`, `p3ClosedLoopDrift_lipConst_ge`, through
`closedLoop_lipConst_ge_of_diagonal_crossing`), where only the existence half
applies. No equilibrium realized-sanction drift is checked against it.

What IS machine-checkable, measure-free, is the *sharp complement of Goal-3*: the
basin `[xT, 1]` is forward-invariant **iff** `h ≤ d_F(xT) = F(xT, 1) − xT`
(`Params.basin_forward_invariant_iff_le_fullShockDrift` below). The `←` direction
is `Params.basin_forward_invariant_under_box_shock_generalF` above; the `→`
direction is the escape exhibit below — when the shock budget is exceeded the
basin floor leaks downward, so lock-in is no longer guaranteed (the regime where
HP's wash-out applies). For the affine law this is the exact disprove-first
threshold (`docs/archive/workflow-scratch/probe_h_dichotomy.lean`,
`probe_open_steps.lean`): from the floor `xT`, the worst down-shock `η = −h`
crosses below `xT` precisely when `δ·(1 − xT) < h`. -/

/-- **Basin escape in the wash-out regime, over any closed loop.** If the shock
half-width strictly exceeds the loop's drift at the floor, `G xT − xT < h`, then
the worst-case down-shock `η = −h` from the floor `xT > 0` lands strictly below
the watershed: `clipS(G xT − h) < xT`. Hence the basin `[xT, 1]` is **not**
forward-invariant.

Rule 22: general — nothing about `G` is read beyond its value at the floor.
Compared with the former affine statement it drops the functional form
`G x = (1−δ)x + δ` and the hypothesis `xT ≤ 1`, which the escape never uses
(BH6.7, 2026-10-07). -/
theorem basin_escape_of_closedLoop
    {G : ℝ → ℝ} {xT h : ℝ}
    (hxT0 : 0 < xT)
    (hwide : G xT - xT < h) :
    Sanctions.clipS (G xT + (-h)) < xT := by
  unfold Sanctions.clipS
  exact max_lt hxT0 (lt_of_le_of_lt (min_le_right _ _) (by linarith))

/-- **Basin escape in the wash-out regime, for every transition (the sharp
complement of Goal-3).** For any economy `p`: when the shock half-width strictly
exceeds the full-sanction drift at the floor, `d_F(xT) = p.fullShockDrift xT < h`,
the worst-case down-shock `η = −h` from the basin floor `xT > 0` lands strictly
below the watershed: `clipS(F(xT, 1) − h) < xT`. Above the threshold the
high-sanction region leaks — the regime where (by Hopenhayn–Prescott 1992
Theorem 2, cited) the chain mixes across the watershed and deterministic lock-in
washes out. The unique invariant law is proved for a contracting drift
(`closedLoopBoxTransfer_existsUnique_invariant_attracting`; see the correction
above).

Rule 22: general in `F`. Instance of `basin_escape_of_closedLoop` at
`G := (p.F · 1)` (BH6.7, 2026-10-07). -/
theorem Params.basin_escape_of_box_shock_wide_generalF
    (p : Params) {xT h : ℝ}
    (hxT0 : 0 < xT)
    (hwide : p.fullShockDrift xT < h) :
    Sanctions.clipS (p.F xT 1 + (-h)) < xT :=
  basin_escape_of_closedLoop (G := fun y => p.F y 1) hxT0 hwide

/-- **The sharp threshold, for every transition.** For any economy `p` and any
floor `0 < xT ≤ 1`: the basin `[xT, 1]` is forward-invariant under every shock in
the box `[−h, h]` — every basin state `x` and every `η` with `|η| ≤ h` give a
post-shock state `clipS(F(x, 1) + η) ≥ xT` — **if and only if**
`h ≤ d_F(xT) = F(xT, 1) − xT`. Economically: lock-in survives a bounded shock
exactly when the shock is no larger than the push full sanctions give the floor
state in one period.

Rule 22: general in `F` (`F_mono_x` for `←`; `F_mono_s` and `F_diag`, through
`0 ≤ d_F(xT)`, for `→` when `h < 0` makes the box empty). It combines
`Params.basin_forward_invariant_under_box_shock_generalF` and
`Params.basin_escape_of_box_shock_wide_generalF`; no hypothesis beyond the
floor's location is used (BH6.7, 2026-10-07). -/
theorem Params.basin_forward_invariant_iff_le_fullShockDrift
    (p : Params) {xT h : ℝ}
    (hxT0 : 0 < xT) (hxT1 : xT ≤ 1) :
    (∀ x ∈ Set.Icc xT 1, ∀ η : ℝ, |η| ≤ h →
        xT ≤ Sanctions.clipS (p.F x 1 + η))
      ↔ h ≤ p.fullShockDrift xT := by
  constructor
  · intro hinv
    by_contra hwide
    rw [not_le] at hwide
    -- the drift at the floor is nonnegative (`F xT 1 ≥ F xT xT = xT`), so `h > 0`
    have hdrift : 0 ≤ p.fullShockDrift xT := by
      have h1 : p.F xT xT ≤ p.F xT 1 := p.F_mono_s xT hxT1
      rw [p.F_diag xT] at h1
      unfold fullShockDrift
      linarith
    have hh : |(-h)| ≤ h := by
      rw [abs_neg, abs_of_nonneg (by linarith)]
    exact absurd (hinv xT ⟨le_rfl, hxT1⟩ (-h) hh)
      (not_le.mpr (p.basin_escape_of_box_shock_wide_generalF hxT0 hwide))
  · intro hbudget x hx η hη
    exact (p.basin_forward_invariant_under_box_shock_generalF hxT1 hx.1
      (abs_le.mp hη).1 hbudget).1

end AbstractGame
end Sanctions
