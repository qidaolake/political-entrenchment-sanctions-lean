/-
Sanctions/Theory/Microfoundations/KaempferLowenbergPolity.lean

**Kaempfer-Lowenberg (1988, AER, §II) two-group target polity — microfoundation
of the basin-assignment sign.**

K-L model the target's objectionable-policy / hardliner-entrenchment level `x = A*`
as the clearing of a political market between

* group `J` (beneficiaries of the policy / regime supporters): demand FOR `x`,
  marginal willingness-to-pay `P_J(x, s)`, decreasing in `x` (`J₁ < 0`);
* group `K` (opposition): demand to REDUCE `x`, `P_K(x, s)`, increasing in `x`
  (`K₁ > 0`).

The market clears at `P_J(x, s) = P_K(x, s)`, i.e. at the root `x*(s)` of the net
pro-entrenchment pressure `g(x, s) = P_J(x, s) − P_K(x, s)` (strictly decreasing
in `x`).  A sanction `s` shifts `J` and `K` through **three channels** (K-L
eqs 6–8, Fig 2), and K-L emphasise the **net sign is indeterminate**:

* `rally`   — the `E^J(s)` effectiveness channel: rally-around-the-flag
  (`E^J₁ < 0`, raises `P_J`) vs discouraged-rent-seeker (`E^J₁ > 0`, lowers `P_J`);
* `incid`   — income incidence: sanctions that hurt `K` more than `J` raise net
  pro-entrenchment pressure ("hurt the prime beneficiaries less"), the opposite
  if they hurt `J` more;
* `empower` — the `E^K(s)` channel: opposition empowerment (`E^K₁ < 0`, raises
  `P_K`, lowers net pressure).

Net sanction channel `n(s) = rally(s) + incid(s) − empower(s)`.  Via the generic
market-clearing monotonicity (`Foundations/MarketClearingMonotone.lean`):

* **`LockIn`** (`n` non-decreasing): `x*(s)` non-decreasing — sanctions ENTRENCH;
  the **high political basin**.  This DERIVES the project's maintained transition
  sign `F_mono_s` (`∂F/∂s ≥ 0`) instead of asserting it.
* **`WashOut`** (`n` non-increasing): `x*(s)` non-increasing — sanctions ERODE
  hardliner power; the **low political basin** (the destabilization regime —
  Marinov 2005; Escriba-Folch & Wright — that an assumed `F_mono_s ≥ 0` cannot
  reach).

The basin assignment is thus a **derived** consequence of the rally / income-
incidence / empowerment signs (which map to regime cohesion, sanction targeting,
and opposition-empowerability), not a free assumption.  Reduced-form in the K-L
sense: `J`/`K` are static pressure schedules, so this microfounds the transition
*sign and basin assignment*, not a fully dynamic intra-target group game.
-/

import Sanctions.Foundations.MarketClearingMonotone

namespace Sanctions
namespace KaempferLowenberg

/-- A Kaempfer-Lowenberg two-group target polity (§II): the net pro-entrenchment
pressure `b(x)` at sanction level zero (strictly decreasing in the entrenchment
level `x`, from `J₁ < 0`, `K₁ > 0`), the three K-L sanction channels, and the
market-clearing entrenchment level `x*(s)`. -/
structure Polity where
  /-- Baseline net pro-entrenchment pressure `P_J − P_K` as a function of the
  entrenchment level `x` (at the zero-sanction reference). -/
  b : ℝ → ℝ
  /-- `J₁ < 0`, `K₁ > 0` ⟹ net pressure strictly decreasing in `x` (unique root). -/
  hb : StrictAnti b
  /-- `E^J` effectiveness channel: rally (↑) vs discouraged-rent-seeker (↓). -/
  rally : ℝ → ℝ
  /-- Income-incidence channel: `K`-hurt-more (↑) vs `J`-hurt-more (↓). -/
  incid : ℝ → ℝ
  /-- `E^K` effectiveness channel: opposition empowerment (↑). -/
  empower : ℝ → ℝ
  /-- Market-clearing entrenchment level `x*(s)`. -/
  xstar : ℝ → ℝ
  /-- The political market clears: `g(x*(s), s) = 0`. -/
  hroot : ∀ s, b (xstar s) + (rally s + incid s - empower s) = 0

namespace Polity

variable (P : Polity)

/-- Net sanction channel `n(s) = rally(s) + incid(s) − empower(s)`. -/
def netChannel (s : ℝ) : ℝ := P.rally s + P.incid s - P.empower s

/-- Net pro-entrenchment pressure `g(x, s) = b(x) + n(s)`. -/
def g (x s : ℝ) : ℝ := P.b x + P.netChannel s

theorem g_root (s : ℝ) : P.g (P.xstar s) s = 0 := P.hroot s

theorem g_strictAnti_x (s : ℝ) : StrictAnti (fun x => P.g x s) :=
  P.hb.add_const _

/-- **High political basin (lock-in regime).** Net pro-entrenchment channel
non-decreasing in `s`: sanctions tilt the `J`-vs-`K` balance toward the regime. -/
def LockIn : Prop := Monotone P.netChannel

/-- **Low political basin (wash-out / destabilization regime).** Net channel
non-increasing in `s`: sanctions tilt the balance toward the opposition. -/
def WashOut : Prop := Antitone P.netChannel

/-- **Derives `F_mono_s` from the polity.** In the lock-in regime the clearing
entrenchment `x*(s)` is non-decreasing in the sanction — sanctions raise the
political state, the sign the project transition otherwise *assumes*. -/
theorem xstar_mono_of_lockIn (h : P.LockIn) : Monotone P.xstar :=
  MarketClearing.clearing_mono_of_pressureDiff_mono P.g_root P.g_strictAnti_x
    (fun x _ _ hss' => by simp only [g]; have := h hss'; linarith)

/-- **The other basin.** In the wash-out regime the clearing entrenchment is
non-increasing in the sanction — sanctions erode hardliner power. -/
theorem xstar_anti_of_washOut (h : P.WashOut) : Antitone P.xstar :=
  MarketClearing.clearing_anti_of_pressureDiff_anti P.g_root P.g_strictAnti_x
    (fun x _ _ hss' => by simp only [g]; have := h hss'; linarith)

/-- **Sufficient condition for lock-in.** Rally dominates empowerment
(`rally − empower` non-decreasing) and the income incidence favours hurting `K`
more (`incid` non-decreasing) ⟹ lock-in. -/
theorem lockIn_of_rally_dominates
    (h1 : Monotone (fun s => P.rally s - P.empower s))
    (h2 : Monotone P.incid) :
    P.LockIn := by
  intro s s' hss'
  have a := h1 hss'
  have b := h2 hss'
  simp only [netChannel]
  simp only at a
  linarith

/-- **Sufficient condition for wash-out.** Opposition empowerment and discouraged
`J` dominate (`rally − empower` non-increasing) and income incidence favours
hurting `J` more (`incid` non-increasing) ⟹ wash-out. -/
theorem washOut_of_empower_dominates
    (h1 : Antitone (fun s => P.rally s - P.empower s))
    (h2 : Antitone P.incid) :
    P.WashOut := by
  intro s s' hss'
  have a := h1 hss'
  have b := h2 hss'
  simp only [netChannel]
  simp only at a
  linarith

/-! ### Bridge: a lock-in polity induces a model-admissible transition

The political state partially adjusts toward the market-clearing entrenchment:
`F(x, s) = (1 − δ)·x + δ·x*(s)`.  In the **lock-in** regime this is a valid
`AbstractGame` transition whose sanction-monotonicity `F_mono_s` is *exactly* the
lock-in property `xstar_mono_of_lockIn` (no longer assumed).  The diagonal
normalisation `x*(x) = x` (linear market clearing) recovers the affine law
`(1 − δ)·x + δ·s` as the special case.  These four/five discharges let a concrete
`Params` *consume a `Polity`* for its transition, so the entrenchment sign is
sourced from the two-group market rather than asserted. -/

/-- Partial-adjustment transition toward the clearing entrenchment `x*(s)`. -/
def inducedF (δ : ℝ) : ℝ → ℝ → ℝ := fun x s => (1 - δ) * x + δ * P.xstar s

/-- **`F_mono_s` from the polity.** In the lock-in regime the induced transition
is non-decreasing in the sanction `s` — the model's entrenchment sign, *derived*
from `xstar_mono_of_lockIn` rather than assumed. -/
theorem inducedF_mono_s {δ : ℝ} (h : P.LockIn) (hδ0 : 0 ≤ δ) :
    ∀ x, Monotone (fun s => P.inducedF δ x s) := by
  intro x s s' hss'
  have hx := P.xstar_mono_of_lockIn h hss'
  have := mul_le_mul_of_nonneg_left hx hδ0
  simp only [inducedF]; linarith

/-- `F_mono_x`: the induced transition is non-decreasing in the current state
(`∂F/∂x = 1 − δ ≥ 0`). -/
theorem inducedF_mono_x {δ : ℝ} (hδ1 : δ ≤ 1) :
    ∀ s, Monotone (fun x => P.inducedF δ x s) := by
  intro s x x' hxx'
  have := mul_le_mul_of_nonneg_left hxx' (by linarith : (0 : ℝ) ≤ 1 - δ)
  simp only [inducedF]; linarith

/-- `F_diag`: under linear market clearing `x*(x) = x`, a sanction equal to the
current entrenchment reproduces it. -/
theorem inducedF_diag {δ : ℝ} (hdiag : ∀ x, P.xstar x = x) :
    ∀ x, P.inducedF δ x x = x := by
  intro x; simp only [inducedF, hdiag x]; ring

/-- `F_mem`: feasibility — a convex combination of feasible `x` and feasible
`x*(s)` stays in `[0, 1]`. -/
theorem inducedF_mem {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) 1, P.xstar s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      P.inducedF δ x s ∈ Set.Icc (0 : ℝ) 1 := by
  rintro x s ⟨hx0, hx1⟩ hs
  obtain ⟨hxs0, hxs1⟩ := hmem s hs
  obtain ⟨hδ0, hδ1⟩ := hδ
  simp only [inducedF, Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · have a1 : 0 ≤ (1 - δ) * x := mul_nonneg (by linarith) hx0
    have a2 : 0 ≤ δ * P.xstar s := mul_nonneg (by linarith) hxs0
    linarith
  · have b1 : (1 - δ) * x ≤ (1 - δ) * 1 := mul_le_mul_of_nonneg_left hx1 (by linarith)
    have b2 : δ * P.xstar s ≤ δ * 1 := mul_le_mul_of_nonneg_left hxs1 (by linarith)
    nlinarith [b1, b2]

/-- `F_continuous`: the induced transition is jointly continuous when the clearing
schedule `x*` is. -/
theorem inducedF_continuous {δ : ℝ} (hcont : Continuous P.xstar) :
    Continuous (fun xs : ℝ × ℝ => P.inducedF δ xs.1 xs.2) := by
  have h : Continuous (fun xs : ℝ × ℝ => (1 - δ) * xs.1 + δ * P.xstar xs.2) :=
    (continuous_const.mul continuous_fst).add
      (continuous_const.mul (hcont.comp continuous_snd))
  simpa only [inducedF] using h

end Polity
end KaempferLowenberg
end Sanctions
