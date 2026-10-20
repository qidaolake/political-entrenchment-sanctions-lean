/-
Sanctions/Theory/Equilibrium/SecurityCore.lean

**The Target's security value over an arbitrary economy** (renovation item BH3.6,
2026-10-06, on the user's word; the `Params`-level core of
`Examples/PlacableSenderSecurity.lean` and `Examples/PlacableSenderSecurityHistory.lean`).

Over any `Params` — both stage payoffs abstract, the transition general, **the
Sender's objective unrestricted** — fix a start `x₀ ∈ [0,1]` and any sanction
sequence `s : ℕ → [0,1]` (open loop). The state moves by `x_{t+1} = F(x_t, s_t)`
(`episodePath`; compliance does not move the state). Let `W(x₀)` be the Target's
discounted payoff from always defying under permanent relief (`s ≡ 0`).
Suppose:

* **the zero-section state chord**: along the zero-sanction section the transition
  rises at least at rate `g_lo` in the state, `g_lo·(y₂ − y₁) ≤ F(y₂,0) − F(y₁,0)`;
* **the sanction lower chord from zero**: at every state a sanction `s` raises the
  next state by at least `d_lo·s` against relief, `d_lo·s ≤ F(x,s) − F(x,0)`;
* **the three Target bounds**, each only where it is read: at full defiance and
  zero sanction the Target gains at least `v ≥ 0` per unit of state (T6); at full
  defiance a sanction `s` costs it at most `c·s` (T4); and against zero sanctions
  compliance `a` costs it at least `ℓ·a` (T2, or only its sign for attainment);
* **the unrefined loss-offset margin** `c ≤ β_T·d_lo·g⁰`, `g⁰ = v/(1 − β_T·g_lo)`
  (`Params.defianceSlope`).

Then:

1. **The security gap** (`reliefPayoff_add_le_defiancePayoff`, no margin): always
   defying against `s` earns at least `W(x₀) + (β_T·d_lo·g⁰ − c)·Σ β_T^t s_t`.
2. **The security bound** (`reliefPayoff_le_defiancePayoff`): under the margin,
   always defying earns at least `W(x₀)` against every sanction sequence.
3. **Attainment** (`targetPathPayoff_relief_add_cost_le`, `targetPathPayoff_relief_le`,
   `reliefPayoff_isLeast`): permanent relief holds every compliance sequence to at
   most `W(x₀)`, so `W(x₀)` is the Target's minmax over open-loop sanction
   sequences.
4. **History-dependent strategies on both sides** (`reliefPayoff_isLeast_history`,
   `reliefPayoff_isGreatest_history`, `defiance_secures_reliefPayoff_history`): `W(x₀)`
   is the least ceiling and the greatest floor over pure history-dependent
   strategies.
5. **Every top-selector equilibrium** (`reliefPayoff_le_V_T`): `W(x₀) ≤ V_T(x₀)`,
   with no class restriction on the equilibrium.

**What is new against the chord-economy files.** There the result was stated over
`ChordEconomy` (78 fields). Here nothing of the Sender's side is read (no
curvature, carrier, Riccati closure, rates or selector conditions: "for any Sender
objective"), the transition enters through two lower chords only, the state chord
only along the zero section and the sanction chord only from zero, and each Target
rate only at the one compliance or sanction level where it is used. Monotonicity of
`F` in both arguments (a `Params` field) keeps the sanctioned path above the relief
path, so no sign on `g_lo` or `d_lo` is needed. `β_T·g_lo < 1` is derived
(`βT_mul_zeroSectionChord_lt_one`). The chord-economy theorems are corollaries, with
their statements unchanged.

**Scope (Rules 1, 9).** Items 1–4 are security levels of fixed plans, not
equilibrium statements. Item 5 quantifies over every
`FeedbackStackelbergEquilibriumTop` of the economy; it is a bound, not a
characterisation. Pure strategies only, deterministic transition, perfect
monitoring. Rule 22: **general in `F`**. Rule 3: every hypothesis restates a
consequence of a chord-economy field or hypothesis at the `Params` level (the lower
state chord at sanction `0`, the lower sanction chord at `s₁ = 0`, T6 at `(a, s) =
(0, 0)`, T4 at `a = 0` from `s₁ = 0`, T2 at `s = 0` from `a₁ = 0`, `0 < v_lo`
weakened to `0 ≤ v`, `LossOffset₀`); none is new. Rule 9B: every chord economy
satisfies them (`Examples/PlacableSenderSecurity.lean`, `security_band0` and its
siblings), and a member outside the chord class is exhibited there
(`oc_security_outside_chord_class`, at the economy of
`Examples/DefianceCoreOutsideChordWitness.lean`, whose Target's compliance cost is not
monotone), as an existence statement only.
-/
import Sanctions.Theory.Equilibrium.DefianceCore
import Sanctions.Theory.Equilibrium.TopLifetimeVerification
import Sanctions.Theory.LockIn.FiniteEpisodePersistence
import Sanctions.Foundations.DiscountedChordSum
import Sanctions.Foundations.HistoryDependentSecurity

namespace Sanctions
namespace AbstractGame
namespace Params

open Set Filter Topology BoundedContinuousFunction
open Sanctions.Foundations.DiscountedChordSum Sanctions.HistoryDependentSecurity

noncomputable section

variable (p : Params)

/-! ## 0. The hypotheses' forms -/

/-- The full sanction lower chord gives the chord from zero, the form read here.
General in `F`. -/
theorem sanctionLowerChord_from_zero {dl : ℝ}
    (hSlo : Sanctions.TransitionChords.SanctionLowerChord p.F dl) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, dl * s ≤ p.F x s - p.F x 0 := by
  intro x hx s hs
  have h := hSlo hx ⟨le_rfl, zero_le_one⟩ hs hs.1
  simpa using h

/-- With the zero-section state chord, the Target discounts the state's rise
strictly: `β_T·g_lo < 1`. General in `F`. The chord between `0` and `1` reads
`g_lo ≤ F(1,0) − F(0,0) ≤ 1`, by the diagonal `F(0,0) = 0` and feasibility. -/
theorem βT_mul_zeroSectionChord_lt_one {gl : ℝ}
    (hband0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0) :
    p.β_T * gl < 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hb := hband0 0 h0 1 h1 zero_le_one
  have e0 := p.F_diag 0
  have hF10 := (p.F_mem 1 0 h1 h0).2
  have hgl : gl ≤ 1 := by linarith
  have hβ0 := p.β_T_mem.1
  have hβ1 := p.β_T_mem.2
  rcases le_or_gt gl 0 with hg | hg
  · have : p.β_T * gl ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ0 hg
    linarith
  · have : p.β_T * gl ≤ p.β_T * 1 := mul_le_mul_of_nonneg_left hgl hβ0
    linarith

/-! ## 1. Payoffs along an open-loop sanction sequence -/

/-- **The Target's discounted payoff** from the compliance sequence `a` when the
Sender imposes the sanction sequence `s` from the start `x₀`, the state following
`x_{t+1} = F(x_t, s_t)`. General in `F`. -/
def targetPathPayoff (a s : ℕ → ℝ) (x₀ : ℝ) : ℝ :=
  ∑' t, p.β_T ^ t * p.U_T (p.episodePath s x₀ t) (a t) (s t)

/-- The Target's payoff from **always defying** against the sanction sequence `s`. -/
def defiancePayoff (s : ℕ → ℝ) (x₀ : ℝ) : ℝ := p.targetPathPayoff (fun _ => 0) s x₀

/-- **The permanent-relief payoff** `W(x₀)`: always defying against zero sanctions at
every date. -/
def reliefPayoff (x₀ : ℝ) : ℝ := p.defiancePayoff (fun _ => 0) x₀

/-- The Target's payoff series converges for feasible sequences: the stage payoff is
continuous, hence bounded on the cube (`exists_bound_U_T`). General in `F`. -/
theorem summable_targetPath {a s : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I)
    (hs : ∀ t, s t ∈ Sanctions.I) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Summable (fun t => p.β_T ^ t * p.U_T (p.episodePath s x₀ t) (a t) (s t)) := by
  obtain ⟨M, hM⟩ := p.exists_bound_U_T
  exact summable_pow_mul_of_abs_le p.β_T_mem.1 p.β_T_mem.2 (fun t =>
    hM _ (p.episodePath_mem hs hx₀ t) _ (ha t) _ (hs t))

/-! ## 2. The security gap and the security bound -/

/-- **The security gap, over any economy.** For every feasible start and every
feasible sanction sequence `s`, the Target's payoff from always defying against `s`
is at least `W(x₀) + (β_T·d_lo·g⁰ − c)·Σ β_T^t s_t`. No margin: the sign of the
coefficient is left open. General in `F`; a lemma about a fixed Target plan.

It reads the zero-section state chord, the sanction lower chord from zero, the state
rate `v ≥ 0` at full defiance and zero sanction, and the pain bound `c` at full
defiance; nothing of the Sender. The gap `e_t` between the sanctioned and the
relief path is nonnegative by monotonicity of `F` (no sign on `g_lo`, `d_lo`) and
obeys `e_{t+1} ≥ g_lo·e_t + d_lo·s_t`; the chord-sum inequality does the rest. -/
theorem reliefPayoff_add_le_defiancePayoff {gl dl c v : ℝ}
    (hband0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0)
    (hSlo0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, dl * s ≤ p.F x s - p.F x 0)
    (hpain0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s)
    (hstate0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0)
    (hv : 0 ≤ v) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {s : ℕ → ℝ}
    (hs : ∀ t, s t ∈ Sanctions.I) :
    p.reliefPayoff x₀ + (p.β_T * dl * p.defianceSlope gl v - c) * ∑' t, p.β_T ^ t * s t
      ≤ p.defiancePayoff s x₀ := by
  have hβ0 := p.β_T_mem.1
  have hβ1 := p.β_T_mem.2
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  set x : ℕ → ℝ := p.episodePath s x₀ with hxdef
  set r : ℕ → ℝ := p.episodePath (fun _ => 0) x₀ with hrdef
  have hx : ∀ t, x t ∈ Sanctions.I := p.episodePath_mem hs hx₀
  have hr : ∀ t, r t ∈ Sanctions.I := p.episodePath_mem (fun _ => h0) hx₀
  have hx_succ : ∀ t, x (t + 1) = p.F (x t) (s t) := fun t => rfl
  have hr_succ : ∀ t, r (t + 1) = p.F (r t) 0 := fun t => rfl
  -- the sanctioned path stays above the relief path: `F` is monotone in both arguments
  have hle : ∀ t, r t ≤ x t := by
    intro t
    induction t with
    | zero => exact le_of_eq rfl
    | succ t ih =>
      rw [hx_succ, hr_succ]
      exact (p.F_mono_x 0 ih).trans (p.F_mono_s (x t) (hs t).1)
  -- the chord recursion for the gap `e = x − r`
  have hrec : ∀ t, gl * (x t - r t) + dl * s t ≤ x (t + 1) - r (t + 1) := by
    intro t
    have hband := hband0 (r t) (hr t) (x t) (hx t) (hle t)
    have hchord := hSlo0 (x t) (hx t) (s t) (hs t)
    rw [hx_succ, hr_succ]
    linarith
  -- the discounted gap dominates the discounted drive
  have he_bd : ∀ t, |x t - r t| ≤ 1 := fun t => by
    rw [abs_le]; constructor <;> linarith [(hx t).1, (hx t).2, (hr t).1, (hr t).2]
  have hs_bd : ∀ t, |s t| ≤ 1 := fun t => by
    rw [abs_le]; constructor <;> linarith [(hs t).1, (hs t).2]
  have hchord := head_add_mul_tsum_le (g := gl) (d := dl) hβ0 hβ1 he_bd hs_bd hrec
  have he0 : x 0 - r 0 = 0 := sub_eq_zero.mpr rfl
  rw [he0] at hchord
  -- the stage gap, weighted
  have hstage : ∀ t, v * (p.β_T ^ t * (x t - r t)) - c * (p.β_T ^ t * s t)
      ≤ p.β_T ^ t * p.U_T (x t) 0 (s t) - p.β_T ^ t * p.U_T (r t) 0 0 := by
    intro t
    have h1 := hstate0 (r t) (hr t) (x t) (hx t) (hle t)
    have h2 := hpain0 (x t) (hx t) (s t) (hs t)
    have hp := pow_nonneg hβ0 t
    have := mul_le_mul_of_nonneg_left
      (show v * (x t - r t) - c * s t ≤ p.U_T (x t) 0 (s t) - p.U_T (r t) 0 0 by linarith) hp
    linarith
  obtain ⟨M, hM⟩ := p.exists_bound_U_T
  have hsx : Summable (fun t => p.β_T ^ t * p.U_T (x t) 0 (s t)) :=
    summable_pow_mul_of_abs_le hβ0 hβ1 (fun t => hM _ (hx t) _ h0 _ (hs t))
  have hsr : Summable (fun t => p.β_T ^ t * p.U_T (r t) 0 0) :=
    summable_pow_mul_of_abs_le hβ0 hβ1 (fun t => hM _ (hr t) _ h0 _ h0)
  have hse := summable_pow_mul_of_abs_le hβ0 hβ1 he_bd
  have hss := summable_pow_mul_of_abs_le hβ0 hβ1 hs_bd
  have hsum := Summable.tsum_le_tsum hstage ((hse.mul_left v).sub (hss.mul_left c))
    (hsx.sub hsr)
  rw [Summable.tsum_sub (hse.mul_left _) (hss.mul_left _), Summable.tsum_sub hsx hsr,
    tsum_mul_left, tsum_mul_left] at hsum
  have hD : p.defiancePayoff s x₀ = ∑' t, p.β_T ^ t * p.U_T (x t) 0 (s t) := rfl
  have hW : p.reliefPayoff x₀ = ∑' t, p.β_T ^ t * p.U_T (r t) 0 0 := rfl
  -- `g⁰·(1 − β_T g_lo) = v` turns the chord sum into the margin
  have hβgl := p.βT_mul_zeroSectionChord_lt_one hband0
  set g := p.defianceSlope gl v with hgdef
  have hgmul : g * (1 - p.β_T * gl) = v := by
    rw [hgdef, defianceSlope]; exact div_mul_cancel₀ _ (by linarith)
  have hg0 : 0 ≤ g := by rw [hgdef, defianceSlope]; exact div_nonneg hv (by linarith)
  have h3 := mul_le_mul_of_nonneg_left hchord hg0
  have h4 : g * ((1 - p.β_T * gl) * ∑' t, p.β_T ^ t * (x t - r t))
      = v * ∑' t, p.β_T ^ t * (x t - r t) := by
    rw [← mul_assoc, hgmul]
  rw [hD, hW]
  linarith

/-- **The Target's security bound, over any economy.** Under the unrefined
loss-offset margin `c ≤ β_T·d_lo·g⁰`, always defying earns the Target at least its
permanent-relief payoff `W(x₀)` against **every** feasible sanction sequence.
General in `F`; a security level for a fixed Target plan. -/
theorem reliefPayoff_le_defiancePayoff {gl dl c v : ℝ}
    (hband0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0)
    (hSlo0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, dl * s ≤ p.F x s - p.F x 0)
    (hpain0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s)
    (hstate0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0)
    (hv : 0 ≤ v) (hTM : c ≤ p.β_T * dl * p.defianceSlope gl v)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {s : ℕ → ℝ} (hs : ∀ t, s t ∈ Sanctions.I) :
    p.reliefPayoff x₀ ≤ p.defiancePayoff s x₀ := by
  have h := p.reliefPayoff_add_le_defiancePayoff hband0 hSlo0 hpain0 hstate0 hv hx₀ hs
  have hS : 0 ≤ ∑' t, p.β_T ^ t * s t :=
    tsum_nonneg fun t => mul_nonneg (pow_nonneg p.β_T_mem.1 t) (hs t).1
  have := mul_nonneg (sub_nonneg.mpr hTM) hS
  linarith

/-! ## 3. Attainment: relief is the harshest open-loop punishment -/

/-- **Against permanent relief, compliance only costs.** If compliance `a` costs the
Target at least `ℓ·a` against a zero sanction (T2 at `s = 0`), every feasible
compliance sequence earns, against zero sanctions at every date, at most `W(x₀)` less
its discounted cost `ℓ·Σ β_T^t a_t`: compliance moves neither the state nor the
sanction. No margin, no sign on `ℓ`. General in `F`. -/
theorem targetPathPayoff_relief_add_cost_le {ℓ : ℝ}
    (hcost0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ℓ * a ≤ p.U_T x 0 0 - p.U_T x a 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) :
    p.targetPathPayoff a (fun _ => 0) x₀ + ℓ * ∑' t, p.β_T ^ t * a t
      ≤ p.reliefPayoff x₀ := by
  have hβ0 := p.β_T_mem.1
  have hβ1 := p.β_T_mem.2
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hr : ∀ t, p.episodePath (fun _ => 0) x₀ t ∈ Sanctions.I :=
    p.episodePath_mem (fun _ => h0) hx₀
  obtain ⟨M, hM⟩ := p.exists_bound_U_T
  have hA : Summable (fun t => p.β_T ^ t * p.U_T (p.episodePath (fun _ => 0) x₀ t) (a t) 0) :=
    summable_pow_mul_of_abs_le hβ0 hβ1 (fun t => hM _ (hr t) _ (ha t) _ h0)
  have hZ : Summable (fun t => p.β_T ^ t * p.U_T (p.episodePath (fun _ => 0) x₀ t) 0 0) :=
    summable_pow_mul_of_abs_le hβ0 hβ1 (fun t => hM _ (hr t) _ h0 _ h0)
  have hB : Summable (fun t => p.β_T ^ t * a t) :=
    summable_pow_mul_of_abs_le hβ0 hβ1 (M := 1)
      (fun t => by rw [abs_le]; constructor <;> linarith [(ha t).1, (ha t).2])
  have hterm : ∀ t, p.β_T ^ t * p.U_T (p.episodePath (fun _ => 0) x₀ t) (a t) 0
      + ℓ * (p.β_T ^ t * a t) ≤ p.β_T ^ t * p.U_T (p.episodePath (fun _ => 0) x₀ t) 0 0 := by
    intro t
    have h := hcost0 _ (hr t) (a t) (ha t)
    have hp := pow_nonneg hβ0 t
    have := mul_le_mul_of_nonneg_left h hp
    linarith
  have hsum := Summable.tsum_le_tsum hterm (hA.add (hB.mul_left _)) hZ
  rw [Summable.tsum_add hA (hB.mul_left _), tsum_mul_left] at hsum
  exact hsum

/-- **Against permanent relief no compliance sequence beats always defying**, when
compliance is weakly costly against a zero sanction (`U_T(x, a, 0) ≤ U_T(x, 0, 0)`,
the sign of T2 at `s = 0`). General in `F`. -/
theorem targetPathPayoff_relief_le
    (hcost0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, p.U_T x a 0 ≤ p.U_T x 0 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) :
    p.targetPathPayoff a (fun _ => 0) x₀ ≤ p.reliefPayoff x₀ := by
  have h := p.targetPathPayoff_relief_add_cost_le (ℓ := 0)
    (fun x hx a ha => by have := hcost0 x hx a ha; linarith) hx₀ ha
  linarith

/-- **`W(x₀)` is the Target's minmax over pure open-loop sanction sequences,
attained by relief, over any economy.** Among the payoff ceilings the Sender can
impose with a feasible sanction sequence against every feasible compliance sequence,
the least is `W(x₀)`. General in `F`. -/
theorem reliefPayoff_isLeast {gl dl c v : ℝ}
    (hband0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0)
    (hSlo0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, dl * s ≤ p.F x s - p.F x 0)
    (hpain0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s)
    (hstate0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0)
    (hv : 0 ≤ v)
    (hcost0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, p.U_T x a 0 ≤ p.U_T x 0 0)
    (hTM : c ≤ p.β_T * dl * p.defianceSlope gl v) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    IsLeast {w : ℝ | ∃ s : ℕ → ℝ, (∀ t, s t ∈ Sanctions.I) ∧
        ∀ a : ℕ → ℝ, (∀ t, a t ∈ Sanctions.I) → p.targetPathPayoff a s x₀ ≤ w}
      (p.reliefPayoff x₀) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine ⟨⟨fun _ => 0, fun _ => h0, fun a ha => p.targetPathPayoff_relief_le hcost0 hx₀ ha⟩, ?_⟩
  rintro w ⟨s, hs, hw⟩
  exact (p.reliefPayoff_le_defiancePayoff hband0 hSlo0 hpain0 hstate0 hv hTM hx₀ hs).trans
    (hw _ fun _ => h0)

/-! ## 4. History-dependent strategies on both sides -/

/-- The transition in the joint-history form: compliance does not move the state. -/
def histF : ℝ → ℝ → ℝ → ℝ := fun x _ s => p.F x s

/-- The open-loop path of the joint-history form is the episode path of the sanction
sequence. -/
theorem openLoopPath_histF (a s : ℕ → ℝ) (x₀ : ℝ) :
    openLoopPath p.histF a s x₀ = p.episodePath s x₀ := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
      change p.F (openLoopPath p.histF a s x₀ n) (s n) = _
      rw [ih]
      rfl

/-- The Target's open-loop payoff is `targetPathPayoff`. -/
theorem targetPathPayoff_eq_openLoopPayoff (a s : ℕ → ℝ) (x₀ : ℝ) :
    p.targetPathPayoff a s x₀ = openLoopPayoff p.U_T p.histF p.β_T a s x₀ := by
  unfold targetPathPayoff openLoopPayoff
  rw [p.openLoopPath_histF]

/-- **The Target's payoff from a profile of pure history-dependent strategies**: `τ`
chooses compliance from the past and the current state, `σ` chooses the sanction
from the past, the current state and current compliance. -/
def targetHistoryPayoff (τ : LeaderPlan ℝ ℝ ℝ) (σ : FollowerPlan ℝ ℝ ℝ) (x₀ : ℝ) : ℝ :=
  jointPayoff p.U_T p.histF p.β_T τ σ x₀

/-- **Minmax over pure history-dependent strategies, over any economy.** Under the
margin, the least payoff ceiling the Sender can impose on the Target with a feasible
pure history-dependent sanction strategy, against every feasible pure
history-dependent compliance strategy, is `W(x₀)`, attained by permanent relief.
General in `F`; for any Sender objective. -/
theorem reliefPayoff_isLeast_history {gl dl c v : ℝ}
    (hband0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0)
    (hSlo0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, dl * s ≤ p.F x s - p.F x 0)
    (hpain0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s)
    (hstate0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0)
    (hv : 0 ≤ v)
    (hcost0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, p.U_T x a 0 ≤ p.U_T x 0 0)
    (hTM : c ≤ p.β_T * dl * p.defianceSlope gl v) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    IsLeast {w : ℝ | ∃ σ : FollowerPlan ℝ ℝ ℝ, (∀ h x a, σ h x a ∈ Sanctions.I) ∧
        ∀ τ : LeaderPlan ℝ ℝ ℝ, (∀ h x, τ h x ∈ Sanctions.I) →
          p.targetHistoryPayoff τ σ x₀ ≤ w}
      (p.reliefPayoff x₀) :=
  isLeast_ceiling_history_of_openLoop_saddle (a₀ := fun _ => 0) (b₀ := fun _ => 0)
    (fun _ => ⟨le_rfl, zero_le_one⟩) (fun _ => ⟨le_rfl, zero_le_one⟩)
    (fun b hb => by
      rw [← p.targetPathPayoff_eq_openLoopPayoff]
      exact p.reliefPayoff_le_defiancePayoff hband0 hSlo0 hpain0 hstate0 hv hTM hx₀ hb)
    (fun a ha => by
      rw [← p.targetPathPayoff_eq_openLoopPayoff]
      exact p.targetPathPayoff_relief_le hcost0 hx₀ ha)

/-- **Maxmin over pure history-dependent strategies, over any economy.** Under the
margin, the greatest payoff floor the Target can guarantee with a feasible pure
history-dependent compliance strategy, against every feasible pure history-dependent
sanction strategy, is `W(x₀)`, attained by always defying. General in `F`; for any
Sender objective. -/
theorem reliefPayoff_isGreatest_history {gl dl c v : ℝ}
    (hband0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0)
    (hSlo0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, dl * s ≤ p.F x s - p.F x 0)
    (hpain0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s)
    (hstate0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0)
    (hv : 0 ≤ v)
    (hcost0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, p.U_T x a 0 ≤ p.U_T x 0 0)
    (hTM : c ≤ p.β_T * dl * p.defianceSlope gl v) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    IsGreatest {w : ℝ | ∃ τ : LeaderPlan ℝ ℝ ℝ, (∀ h x, τ h x ∈ Sanctions.I) ∧
        ∀ σ : FollowerPlan ℝ ℝ ℝ, (∀ h x a, σ h x a ∈ Sanctions.I) →
          w ≤ p.targetHistoryPayoff τ σ x₀}
      (p.reliefPayoff x₀) :=
  isGreatest_floor_history_of_openLoop_saddle (a₀ := fun _ => 0) (b₀ := fun _ => 0)
    (fun _ => ⟨le_rfl, zero_le_one⟩) (fun _ => ⟨le_rfl, zero_le_one⟩)
    (fun b hb => by
      rw [← p.targetPathPayoff_eq_openLoopPayoff]
      exact p.reliefPayoff_le_defiancePayoff hband0 hSlo0 hpain0 hstate0 hv hTM hx₀ hb)
    (fun a ha => by
      rw [← p.targetPathPayoff_eq_openLoopPayoff]
      exact p.targetPathPayoff_relief_le hcost0 hx₀ ha)

/-- **Always defying secures `W(x₀)` against every pure history-dependent Sender
strategy, over any economy.** Under the margin, the plan that never complies earns
at least the permanent-relief payoff against every feasible sanction strategy,
however it conditions on the past. General in `F`; it reads no compliance cost. -/
theorem defiance_secures_reliefPayoff_history {gl dl c v : ℝ}
    (hband0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0)
    (hSlo0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, dl * s ≤ p.F x s - p.F x 0)
    (hpain0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s)
    (hstate0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0)
    (hv : 0 ≤ v) (hTM : c ≤ p.β_T * dl * p.defianceSlope gl v)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (σ : FollowerPlan ℝ ℝ ℝ)
    (hσ : ∀ h x a, σ h x a ∈ Sanctions.I) :
    p.reliefPayoff x₀ ≤ p.targetHistoryPayoff (LeaderPlan.ofSeq fun _ => 0) σ x₀ := by
  unfold targetHistoryPayoff
  rw [jointPayoff_eq_openLoopPayoff, ← p.targetPathPayoff_eq_openLoopPayoff]
  have ha : leaderAction p.histF (LeaderPlan.ofSeq fun _ => (0 : ℝ)) σ x₀ = fun _ => 0 :=
    funext (leaderAction_ofSeq p.histF _ σ x₀)
  rw [ha]
  exact p.reliefPayoff_le_defiancePayoff hband0 hSlo0 hpain0 hstate0 hv hTM hx₀
    fun n => hσ _ _ _

/-! ## 5. Every top-selector equilibrium -/

/-- The state path on which the Target defies at every date and the Sender answers
with its equilibrium response `σ_dyn_top V_S` (the greatest maximiser of its dynamic
objective at the equilibrium's own Sender value). -/
def defiancePath (Eq : p.FeedbackStackelbergEquilibriumTop) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | t + 1 => p.F (defiancePath Eq x₀ t) (p.σ_dyn_top Eq.V_S (defiancePath Eq x₀ t) 0)

/-- The Sender's equilibrium response to defiance along `defiancePath`. -/
def defianceSanction (Eq : p.FeedbackStackelbergEquilibriumTop) (x₀ : ℝ) (t : ℕ) : ℝ :=
  p.σ_dyn_top Eq.V_S (p.defiancePath Eq x₀ t) 0

theorem defianceSanction_mem (Eq : p.FeedbackStackelbergEquilibriumTop) (x₀ : ℝ) (t : ℕ) :
    p.defianceSanction Eq x₀ t ∈ Sanctions.I :=
  p.σ_dyn_top_mem_I _ _ _

/-- The deviation path is the state path of its own sanction sequence. -/
theorem episodePath_defianceSanction (Eq : p.FeedbackStackelbergEquilibriumTop) (x₀ : ℝ)
    (t : ℕ) : p.episodePath (p.defianceSanction Eq x₀) x₀ t = p.defiancePath Eq x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [episodePath_succ, ih]
    rfl

/-- **The Target's value dominates its full-defiance deviation, over any economy.**
At every top-selector equilibrium and every feasible start, the Target's value is at
least its discounted payoff from defying at every date against the Sender's
equilibrium responses: its policy is an argmax of its joint integrand
(`target_one_shot_deviation_top`), so the one-step inequality holds at every date and
sums by boundedness. No hypothesis on the economy beyond `Params`. General in `F`. -/
theorem defiancePayoff_le_V_T (Eq : p.FeedbackStackelbergEquilibriumTop) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    p.defiancePayoff (p.defianceSanction Eq x₀) x₀ ≤ Eq.V_T ⟨x₀, hx₀⟩ := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hsm := p.defianceSanction_mem Eq x₀
  have hy : ∀ t, p.defiancePath Eq x₀ t ∈ Sanctions.I := by
    intro t
    rw [← p.episodePath_defianceSanction]
    exact p.episodePath_mem hsm hx₀ t
  obtain ⟨M, hM⟩ := p.exists_bound_U_T
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 h0 0 h0 0 h0)
  have hV : ∀ t, |Eq.V_T (Sanctions.clipS' (p.defiancePath Eq x₀ t))| ≤ ‖Eq.V_T‖ + M :=
    fun t => by
      have := BoundedContinuousFunction.norm_coe_le_norm Eq.V_T
        (Sanctions.clipS' (p.defiancePath Eq x₀ t))
      rw [Real.norm_eq_abs] at this
      linarith
  have hu : ∀ t, |p.U_T (p.defiancePath Eq x₀ t) 0 (p.defianceSanction Eq x₀ t)|
      ≤ ‖Eq.V_T‖ + M := fun t => by
    have := hM _ (hy t) _ h0 _ (hsm t)
    linarith [norm_nonneg Eq.V_T]
  have hstep : ∀ t, p.U_T (p.defiancePath Eq x₀ t) 0 (p.defianceSanction Eq x₀ t)
      + p.β_T * Eq.V_T (Sanctions.clipS' (p.defiancePath Eq x₀ (t + 1)))
      ≤ Eq.V_T (Sanctions.clipS' (p.defiancePath Eq x₀ t)) := by
    intro t
    have h := Eq.target_one_shot_deviation_top ⟨p.defiancePath Eq x₀ t, hy t⟩ 0 h0
    have hclip : Sanctions.clipS' (p.defiancePath Eq x₀ t) = ⟨p.defiancePath Eq x₀ t, hy t⟩ :=
      Subtype.ext (Sanctions.clipS'_val_eq_of_mem (hy t))
    rw [hclip]
    exact h
  have hsum := tsum_pow_mul_le_of_le_add_mul_succ p.β_T_mem.1 p.β_T_mem.2 hV hu hstep
  have hclip0 : Sanctions.clipS' (p.defiancePath Eq x₀ 0) = ⟨x₀, hx₀⟩ :=
    Subtype.ext (Sanctions.clipS'_val_eq_of_mem hx₀)
  rw [hclip0] at hsum
  have hD : p.defiancePayoff (p.defianceSanction Eq x₀) x₀
      = ∑' t, p.β_T ^ t
          * p.U_T (p.defiancePath Eq x₀ t) 0 (p.defianceSanction Eq x₀ t) := by
    unfold defiancePayoff targetPathPayoff
    simp only [p.episodePath_defianceSanction]
  rw [hD]
  exact hsum

/-- **The security gap at every equilibrium, over any economy.** At every top-selector
equilibrium and every feasible start, `V_T(x₀) ≥ W(x₀) + (β_T·d_lo·g⁰ − c)` times the
discounted sanctions the Sender's equilibrium response would impose on a Target that
defied at every date. No margin, no class restriction. General in `F`. -/
theorem reliefPayoff_add_le_V_T {gl dl c v : ℝ}
    (hband0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0)
    (hSlo0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, dl * s ≤ p.F x s - p.F x 0)
    (hpain0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s)
    (hstate0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0)
    (hv : 0 ≤ v) (Eq : p.FeedbackStackelbergEquilibriumTop) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) :
    p.reliefPayoff x₀
        + (p.β_T * dl * p.defianceSlope gl v - c) * ∑' t, p.β_T ^ t * p.defianceSanction Eq x₀ t
      ≤ Eq.V_T ⟨x₀, hx₀⟩ :=
  (p.reliefPayoff_add_le_defiancePayoff hband0 hSlo0 hpain0 hstate0 hv hx₀
    (p.defianceSanction_mem Eq x₀)).trans (p.defiancePayoff_le_V_T Eq hx₀)

/-- **Every top-selector equilibrium gives the Target at least its permanent-relief
payoff, over any economy** (the coercion theorem, `prop:security` (iii)). Under the
unrefined loss-offset margin, for **every** `FeedbackStackelbergEquilibriumTop` of an
arbitrary `Params` with the zero-section state chord, the sanction lower chord from
zero and the Target's state and pain bounds at full defiance, `W(x₀) ≤ V_T(x₀)` at
every feasible state. For any Sender objective; a bound, not a characterisation.
General in `F`. -/
theorem reliefPayoff_le_V_T {gl dl c v : ℝ}
    (hband0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0)
    (hSlo0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, dl * s ≤ p.F x s - p.F x 0)
    (hpain0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s)
    (hstate0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0)
    (hv : 0 ≤ v) (hTM : c ≤ p.β_T * dl * p.defianceSlope gl v)
    (Eq : p.FeedbackStackelbergEquilibriumTop) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    p.reliefPayoff x₀ ≤ Eq.V_T ⟨x₀, hx₀⟩ :=
  (p.reliefPayoff_le_defiancePayoff hband0 hSlo0 hpain0 hstate0 hv hTM hx₀
    (p.defianceSanction_mem Eq x₀)).trans (p.defiancePayoff_le_V_T Eq hx₀)

/-- **Compliance paired with permanent relief is worth at most the equilibrium value
less the compliance cost, over any economy.** Under the margin and a compliance cost
of at least `ℓ` per unit against a zero sanction, at every top-selector equilibrium a
feasible compliance sequence paired with zero sanctions at every date gives the
Target at most `V_T(x₀) − ℓ·Σ β_T^t a_t`. Covers compliance paired with zero
sanctions only. General in `F`. -/
theorem compliance_for_relief_add_cost_le_V_T {gl dl c v ℓ : ℝ}
    (hband0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ 0 - p.F y₁ 0)
    (hSlo0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, dl * s ≤ p.F x s - p.F x 0)
    (hpain0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, p.U_T x 0 0 - p.U_T x 0 s ≤ c * s)
    (hstate0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 0 - p.U_T y₁ 0 0)
    (hv : 0 ≤ v)
    (hcost0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ℓ * a ≤ p.U_T x 0 0 - p.U_T x a 0)
    (hTM : c ≤ p.β_T * dl * p.defianceSlope gl v)
    (Eq : p.FeedbackStackelbergEquilibriumTop) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {a : ℕ → ℝ} (ha : ∀ t, a t ∈ Sanctions.I) :
    p.targetPathPayoff a (fun _ => 0) x₀ + ℓ * ∑' t, p.β_T ^ t * a t ≤ Eq.V_T ⟨x₀, hx₀⟩ :=
  (p.targetPathPayoff_relief_add_cost_le hcost0 hx₀ ha).trans
    (p.reliefPayoff_le_V_T hband0 hSlo0 hpain0 hstate0 hv hTM Eq hx₀)

end

end Params
end AbstractGame
end Sanctions

#print axioms Sanctions.AbstractGame.Params.reliefPayoff_add_le_defiancePayoff
#print axioms Sanctions.AbstractGame.Params.reliefPayoff_le_defiancePayoff
#print axioms Sanctions.AbstractGame.Params.reliefPayoff_isLeast
#print axioms Sanctions.AbstractGame.Params.reliefPayoff_isLeast_history
#print axioms Sanctions.AbstractGame.Params.reliefPayoff_isGreatest_history
#print axioms Sanctions.AbstractGame.Params.defiance_secures_reliefPayoff_history
#print axioms Sanctions.AbstractGame.Params.defiancePayoff_le_V_T
#print axioms Sanctions.AbstractGame.Params.reliefPayoff_le_V_T
#print axioms Sanctions.AbstractGame.Params.compliance_for_relief_add_cost_le_V_T
