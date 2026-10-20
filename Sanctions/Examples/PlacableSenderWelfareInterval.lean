/-
Sanctions/Examples/PlacableSenderWelfareInterval.lean

**Partial identification of the welfare ranking of the two defiance regimes
under a restricted completion class** (round AG, 2026-09-20; doc 94 E10, on the
user's word; the outside reader's literature-verification package §2 of
`02_NOISE_AND_WELFARE.md`, and its inspection package, 04_SIGNIFICANCE §5).

`PlacableSenderWelfareCompletion` shows that unrestricted positive-weight
completions of the governments' payoffs reverse the welfare ranking of the
constructed regimes. A sceptic's reply is that with free cardinal group
benefits and compensating political weights this is unsurprising. This file
says what a restriction buys, and what it does not.

**The decomposition** (`regimeValue11_sub_10_eq`). Along the two defiance
regimes compliance is zero, so for every completion, start and planner discount

  `V¹¹ − V¹⁰ = K·ΔX + η·ΔS − (q/2)·ΔS₂`,

where `ΔX`, `ΔS`, `ΔS₂` are the discounted differences of the two constructed
state paths, sanctions and squared sanctions — numbers that do **not** depend on
the completion — `K = w + b_J − b_K` and `η = g_H − Q − c`. The wedge makes
`ΔS ≥ wedge/(1−β) > 0` (`dS_ge`). The two regimes are the member's chord
economy's (`E.toChordCs`, round AV, 2026-09-25, doc 104); the completion class
stays on the quadratic–linear family (sign-off M5).

**The restricted class** (`HawkBounded`). Fix the commercial lobby's exposure
`Q = Q̄` and bound the hawks' political weight on the feasible states,
`m ≤ θ_H(x) ≤ M`. Since `θ_H(x) = (u₀ + Q̄ + r·x)/g_H` rises with the state
(`r ≥ 0`), this is `(u₀+Q̄+r)/M ≤ g_H ≤ (u₀+Q̄)/m` (`hawkBounded_iff`): the class
is non-empty iff `m(u₀+Q̄+r) ≤ M(u₀+Q̄)` (`hawkBounded_nonempty_iff`), and on it
`η` ranges over exactly `[η_L, η_U]`, every value attained with the Target side
held fixed (`hawkBounded_eta_mem`, `exists_hawkBounded_eta`).

**The sharp interval** (`gap_mem_interval`, `gap_attained`). With the Target
side, hence `K`, held fixed, the welfare gap `V¹¹ − V¹⁰` over the class is
exactly the closed interval with endpoints `K·ΔX − (q/2)ΔS₂ + η_L·ΔS` and
`… + η_U·ΔS`. So the ranking is identified iff that interval strictly excludes
zero — its lower endpoint positive or its upper endpoint negative
(`gap_pos_of_lower_pos`, `gap_neg_of_upper_neg`) — and both rankings occur when
it straddles zero (`exists_both_signs_of_straddle`); an endpoint at zero
identifies a weak ranking only (N1, round AI, 2026-09-22).

**Weight bounds alone identify nothing** (`exists_weightBounded_reversal`,
Rule 11). With a band `m < 1 < M` and no bound on exposure, completions with
weights inside the band give the gap either sign: letting `Q` grow with
`g_H = (u₀+Q)/m'` sends `η` to `+∞`, with `g_H = (u₀+Q+r)/M` to `−∞`. Here
`m' = max m ½ ∈ (0, 1)`; a completion inside `[m', M]` is inside `[m, M]`, so no
sign of `m` is assumed (round BG3, BG3.6).

**Status.** `HawkBounded` is a new *definition* — a relation written over the
completion's own data (Rule 14) — not a hypothesis on the game: every
government payoff and every constructed equilibrium is untouched. What it
changes is what a welfare statement may say, which is why its use in the paper
was the author's decision (doc 94 E10). Rule 22: general in `F`. Rule 9: the
existence statements license non-vacuity and attainment, not magnitudes.

**Positivity bounds that follow from the rest are not assumed** (round BG3,
2026-10-06, plan item BG3.6). `0 < M` follows from the class itself, since the
hawks' weight is positive (`HawkBounded.upper_pos`); `0 < m` follows from a
non-empty range `η_L ≤ η_U` (`pos_of_etaLo_le_etaHi`); and the reversal needs
no `0 < m` at all, because the band condition only gets easier as `m` falls.
`0 < m` is kept where the upper endpoint `η_U` is read without the range premise
`η_L ≤ η_U` (`gap_mem_interval`, `exists_both_signs_iff`): at `m ≤ 0` the floor
is vacuous and `η_U` falls below every member's `η`. The fixed exposure stays
positive, `0 < Q̄`, matching the structure's field `0 < Q`: every completion's
commercial lobby has a positive stake.

**The rally margin becomes a monotone response** (renovation item BH4.1, 2026-10-06). The
objects `sanction11`, `dX`, `dS`, `dS2`, `gap` and `gapAt` are indexed by the rally margin,
which they read only through the forward-looking regime: the margin makes the forward-looking
response nondecreasing, which orders the two state paths and gives the wedge along them.
Their `Of` siblings and the `_of_response_monotone` theorems take that nondecreasing
response `hmono` in place of the margin, at `equilibriumTop` and its path `dynamicPathOf`.
The margin forms keep their statements: each definition equals its sibling by `rfl` (the
`_eq_..Of` bridges) and each theorem is the corollary at
`hmono := responsePath_monotoneOn_of_margin hmargin`. In plain terms, partial identification
of the welfare ranking needs only that the forward-looking Sender never sanctions a defiant
Target less at a higher state, not the rate inequality that guarantees it. That condition
is on the constructed Sender value, so it is not checkable from the primitives alone.

**Interiority becomes a hypothesis** (renovation item BJ2.3, 2026-10-07). The family no
longer carries the interiority field. That the forward-looking sanction exceeds the
Target-only one by the wedge is proved under interiority (the bound reads `hInt`), so
`dS_ge` and every result built on it (the
sharp interval, its attainment, the sign and reversal results) take the member's
interiority `hInt : E.toChordCs.Interior` as a hypothesis. The definitions are unchanged.
General in `F`.
-/
import Sanctions.Examples.PlacableSenderWelfareCompletion

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

/-- Bounded flows are summable against a geometric discount. -/
theorem summable_geometric_mul_of_abs_le {β M : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    {f : ℕ → ℝ} (hf : ∀ t, |f t| ≤ M) : Summable (fun t : ℕ => β ^ t * f t) := by
  refine Summable.of_norm_bounded (g := fun t : ℕ => M * β ^ t)
    ((summable_geometric_of_lt_one hβ.1 hβ.2).mul_left _) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ.1, mul_comm]
  exact mul_le_mul_of_nonneg_right (hf t) (pow_nonneg hβ.1 t)

namespace PlacableEconomyF

variable {E : PlacableEconomyF}

namespace WelfareCompletion

variable (C : E.WelfareCompletion)

/-- The same Target side with a different Sender side. The three representation
equations involve neither `g_H` nor `Q`. -/
def withSender (gH Q : ℝ) (hgH : 0 < gH) (hQ : 0 < Q) : E.WelfareCompletion :=
  { C with gH := gH, Q := Q, hgH := hgH, hQ := hQ }

@[simp] theorem withSender_K (gH Q : ℝ) (hgH : 0 < gH) (hQ : 0 < Q) :
    (C.withSender gH Q hgH hQ).K = C.K := rfl

@[simp] theorem withSender_η (gH Q : ℝ) (hgH : 0 < gH) (hQ : 0 < Q) :
    (C.withSender gH Q hgH hQ).η = gH - Q - E.c := rfl

@[simp] theorem withSender_Q (gH Q : ℝ) (hgH : 0 < gH) (hQ : 0 < Q) :
    (C.withSender gH Q hgH hQ).Q = Q := rfl

@[simp] theorem withSender_gH (gH Q : ℝ) (hgH : 0 < gH) (hQ : 0 < Q) :
    (C.withSender gH Q hgH hQ).gH = gH := rfl

/-- The hawks' political weight is bounded on the feasible states. -/
def WeightBounded (m M : ℝ) : Prop :=
  ∀ x ∈ Sanctions.I, m ≤ C.thetaJS x ∧ C.thetaJS x ≤ M

/-- **The restricted class**: commercial exposure fixed at `Q̄` and the hawks'
weight in `[m, M]` on the feasible states. -/
def HawkBounded (Qbar m M : ℝ) : Prop := C.Q = Qbar ∧ C.WeightBounded m M

/-- The band condition only gets easier as its lower bound falls: a completion
whose hawks' weight lies in `[m', M]` also lies in `[m, M]` for every `m ≤ m'`.
Round BG3 (BG3.6), used to drop `0 < m` from the reversal. General in `F`. -/
theorem WeightBounded.mono_lower {m m' M : ℝ} (hmm' : m ≤ m') (h : C.WeightBounded m' M) :
    C.WeightBounded m M :=
  fun x hx => ⟨hmm'.trans (h x hx).1, (h x hx).2⟩

/-- **A member of the class has a positive upper weight bound**: `M` is at least
the hawks' weight at `x = 0`, `(u₀ + Q)/g_H`, which is positive (`thetaJS_pos`).
So `0 < M` never needs to be assumed next to `HawkBounded` (round BG3, BG3.6).
General in `F`. -/
theorem HawkBounded.upper_pos {Qbar m M : ℝ} (h : C.HawkBounded Qbar m M) : 0 < M :=
  (C.thetaJS_pos le_rfl).trans_le (h.2 0 ⟨le_rfl, zero_le_one⟩).2

/-- Weight bounds are two bounds on the hawks' benefit `g_H`. -/
theorem weightBounded_iff {m M : ℝ} (hm : 0 < m) (hM : 0 < M) :
    C.WeightBounded m M ↔
      (E.u₀ + C.Q + E.r) / M ≤ C.gH ∧ C.gH ≤ (E.u₀ + C.Q) / m := by
  have hg := C.hgH
  constructor
  · intro h
    have h0 := (h 0 ⟨le_rfl, zero_le_one⟩).1
    have h1 := (h 1 ⟨zero_le_one, le_rfl⟩).2
    unfold thetaJS at h0 h1
    rw [le_div_iff₀ hg] at h0
    rw [div_le_iff₀ hg] at h1
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hM]; linarith
    · rw [le_div_iff₀ hm]; linarith
  · rintro ⟨hlo, hhi⟩ x hx
    rw [div_le_iff₀ hM] at hlo
    rw [le_div_iff₀ hm] at hhi
    have hrx : 0 ≤ E.r * x := mul_nonneg E.hr hx.1
    have hrx1 : E.r * x ≤ E.r := by
      have := mul_le_mul_of_nonneg_left hx.2 E.hr
      linarith
    unfold thetaJS
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hg]; linarith
    · rw [div_le_iff₀ hg]; linarith

theorem hawkBounded_iff {Qbar m M : ℝ} (hm : 0 < m) (hM : 0 < M) :
    C.HawkBounded Qbar m M ↔
      C.Q = Qbar ∧ (E.u₀ + Qbar + E.r) / M ≤ C.gH ∧ C.gH ≤ (E.u₀ + Qbar) / m := by
  unfold HawkBounded
  constructor
  · rintro ⟨hQ, hW⟩
    have := (C.weightBounded_iff hm hM).mp hW
    rw [hQ] at this
    exact ⟨hQ, this⟩
  · rintro ⟨hQ, hb⟩
    refine ⟨hQ, (C.weightBounded_iff hm hM).mpr ?_⟩
    rw [hQ]
    exact hb

/-- The lower end of the identified range of the net sanction coefficient. -/
def etaLo (E : PlacableEconomyF) (Qbar M : ℝ) : ℝ := (E.u₀ + Qbar + E.r) / M - Qbar - E.c

/-- The upper end. -/
def etaHi (E : PlacableEconomyF) (Qbar m : ℝ) : ℝ := (E.u₀ + Qbar) / m - Qbar - E.c

/-- **A non-empty range forces a positive lower weight bound.** With exposure
`Q̄ ≥ 0` and `0 < M`, `η_L ≤ η_U` gives `0 < m`: `η_L + Q̄ + c = (u₀+Q̄+r)/M` is
positive, while `η_U + Q̄ + c = (u₀+Q̄)/m` is not when `m ≤ 0`. This lets the
attainment, straddle and iff lemmas below drop `0 < m` (round BG3, BG3.6). The
statement involves no completion, so `Q̄ ≥ 0` is all it needs; the lemmas below
assume `0 < Q̄`, as the structure's field does, and pass `hQbar.le`. General in
`F`. -/
theorem pos_of_etaLo_le_etaHi {Qbar m M : ℝ} (hQbar : 0 ≤ Qbar) (hM : 0 < M)
    (h : etaLo E Qbar M ≤ etaHi E Qbar m) : 0 < m := by
  unfold etaLo etaHi at h
  have hlo : 0 < (E.u₀ + Qbar + E.r) / M := div_pos (by linarith [E.hu₀, E.hr]) hM
  have hdiv : 0 < (E.u₀ + Qbar) / m := by linarith
  rcases div_pos_iff.mp hdiv with ⟨_, hm⟩ | ⟨hneg, _⟩
  · exact hm
  · linarith [E.hu₀]

/-- On the restricted class the net sanction coefficient lies in `[η_L, η_U]`. -/
theorem hawkBounded_eta_mem {Qbar m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (h : C.HawkBounded Qbar m M) : etaLo E Qbar M ≤ C.η ∧ C.η ≤ etaHi E Qbar m := by
  obtain ⟨hQ, hlo, hhi⟩ := (C.hawkBounded_iff hm hM).mp h
  unfold etaLo etaHi η
  rw [hQ]
  constructor <;> linarith

/-- **Every value in `[η_L, η_U]` is attained by changing the hawks' benefit
alone**: the attaining completion is `C.withSender g_H Q̄`, whose Target side is
`C`'s field for field. Round BG3 (BG3.6): no `0 < m`, which follows from
`η_L ≤ η' ≤ η_U` (`pos_of_etaLo_le_etaHi`). General in `F`. -/
theorem exists_withSender_hawkBounded_eta {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {η' : ℝ} (hlo : etaLo E Qbar M ≤ η') (hhi : η' ≤ etaHi E Qbar m) :
    ∃ (gH : ℝ) (hgH : 0 < gH),
      (C.withSender gH Qbar hgH hQbar).HawkBounded Qbar m M ∧
      (C.withSender gH Qbar hgH hQbar).η = η' := by
  have hm : 0 < m := pos_of_etaLo_le_etaHi hQbar.le hM (hlo.trans hhi)
  have hnum : 0 < E.u₀ + Qbar + E.r := by linarith [E.hu₀, E.hr]
  have hgL : 0 < (E.u₀ + Qbar + E.r) / M := div_pos hnum hM
  have hg : 0 < η' + Qbar + E.c := by
    unfold etaLo at hlo
    linarith
  refine ⟨η' + Qbar + E.c, hg, ?_, ?_⟩
  · rw [hawkBounded_iff _ hm hM]
    refine ⟨rfl, ?_, ?_⟩
    · change (E.u₀ + Qbar + E.r) / M ≤ η' + Qbar + E.c
      unfold etaLo at hlo
      linarith
    · change η' + Qbar + E.c ≤ (E.u₀ + Qbar) / m
      unfold etaHi at hhi
      linarith
  · change η' + Qbar + E.c - Qbar - E.c = η'
    ring

/-- **Every value in `[η_L, η_U]` is attained**, with the Target side — hence
the state coefficient `K` — held fixed. Round BG3 (BG3.6): no `0 < m`, which
follows from `η_L ≤ η_U`. General in `F`. -/
theorem exists_hawkBounded_eta {Qbar m M : ℝ} (hQbar : 0 < Qbar) (hM : 0 < M)
    {η' : ℝ} (hlo : etaLo E Qbar M ≤ η') (hhi : η' ≤ etaHi E Qbar m) :
    ∃ C' : E.WelfareCompletion, C'.HawkBounded Qbar m M ∧ C'.K = C.K ∧ C'.η = η' := by
  obtain ⟨gH, hgH, hB, hη⟩ := C.exists_withSender_hawkBounded_eta hQbar hM hlo hhi
  exact ⟨_, hB, rfl, hη⟩

end WelfareCompletion

/-- **The restricted class is non-empty exactly when the weight band is wide
enough for the state's effect on the hawks' weight**:
`m·(u₀ + Q̄ + r) ≤ M·(u₀ + Q̄)`. Round BG3 (BG3.6): no `0 < M`, derived in each
direction — from a member of the class (`HawkBounded.upper_pos`), and from the
inequality, whose left side is positive. General in `F`. -/
theorem hawkBounded_nonempty_iff {Qbar m M : ℝ} (hQbar : 0 < Qbar) (hm : 0 < m) :
    (∃ C : E.WelfareCompletion, C.HawkBounded Qbar m M) ↔
      m * (E.u₀ + Qbar + E.r) ≤ M * (E.u₀ + Qbar) := by
  constructor
  · rintro ⟨C, hC⟩
    have hM : 0 < M := hC.upper_pos
    obtain ⟨_, hlo, hhi⟩ := (C.hawkBounded_iff hm hM).mp hC
    have h := hlo.trans hhi
    rw [div_le_div_iff₀ hM hm] at h
    linarith
  · intro h
    have hnum : 0 < E.u₀ + Qbar := by linarith [E.hu₀]
    have hM : 0 < M := by
      have h1 : 0 < m * (E.u₀ + Qbar + E.r) := mul_pos hm (by linarith [E.hr])
      by_contra hM0
      have h2 : M * (E.u₀ + Qbar) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hM0) hnum.le
      linarith
    obtain ⟨C₀, -, -⟩ := E.exists_welfareCompletion 0 one_pos
    have hle : WelfareCompletion.etaLo E Qbar M ≤ WelfareCompletion.etaHi E Qbar m := by
      unfold WelfareCompletion.etaLo WelfareCompletion.etaHi
      have : (E.u₀ + Qbar + E.r) / M ≤ (E.u₀ + Qbar) / m := by
        rw [div_le_div_iff₀ hM hm]; linarith
      linarith
    obtain ⟨C, hC, -, -⟩ := C₀.exists_hawkBounded_eta hQbar hM le_rfl hle
    exact ⟨C, hC⟩

end PlacableEconomyF

namespace PlacableEconomyFcs

variable {E : PlacableEconomyFcs}

/-! ## The welfare gap between the two defiance regimes is affine in `η` -/

/-- The forward-looking regime's realised sanction at date `t`.
This is `sanction11` with the rally margin replaced by a response `responsePath VSstar`
that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`. General in `F`. -/
def sanction11Of (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (x₀ : ℝ) (t : ℕ) : ℝ := E.toChordCs.responsePath E.toChordCs.VSstar
        ((E.toChordCs.dynamicPathOf hTM) hmono x₀ t)

/-- The forward-looking regime's realised sanction at date `t`.
The rally-margin form of `sanction11Of` (BH4.1). -/
def sanction11 (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (x₀ : ℝ) (t : ℕ) : ℝ := E.toChordCs.responsePath E.toChordCs.VSstar ((E.toChordCs.dynamicPath
        hTM) hmargin x₀ t)

/-- The bridge (BH4.1): `sanction11` is `sanction11Of` at the nondecreasing
response that the rally margin gives. Definitional. General in `F`. -/
theorem sanction11_eq_sanction11Of (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (x₀ : ℝ) (t : ℕ) :
    (E.sanction11 hTM) hmargin x₀ t
      = (E.sanction11Of hTM) (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) x₀ t := rfl

/-- The Target-only regime's realised sanction at date `t`. -/
def sanction10 (hTM : E.toChordCs.LossOffset) (x₀ : ℝ) (t : ℕ) : ℝ := E.toChordCs.σ
    ((E.toChordCs.targetOnlyPath hTM) x₀ t) 0

/-- Discounted difference of the two state paths.
This is `dX` with the rally margin replaced by a response `responsePath VSstar` that is
nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`. General in `F`. -/
def dXOf (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (β x₀ : ℝ) : ℝ :=
  regimeValue β ((E.toChordCs.dynamicPathOf hTM) hmono x₀) - regimeValue β
      ((E.toChordCs.targetOnlyPath hTM) x₀)

/-- Discounted difference of the two state paths.
The rally-margin form of `dXOf` (BH4.1). -/
def dX (hTM : E.toChordCs.LossOffset) (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC *
    E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (β x₀ : ℝ) : ℝ :=
  regimeValue β ((E.toChordCs.dynamicPath hTM) hmargin x₀) - regimeValue β
      ((E.toChordCs.targetOnlyPath hTM) x₀)

/-- The bridge (BH4.1): `dX` is `dXOf` at the nondecreasing
response that the rally margin gives. Definitional. General in `F`. -/
theorem dX_eq_dXOf (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (β x₀ : ℝ) :
    (E.dX hTM) hmargin β x₀
      = (E.dXOf hTM) (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) β x₀ := rfl

/-- Discounted difference of the two sanction paths.
This is `dS` with the rally margin replaced by a response `responsePath VSstar` that is
nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`. General in `F`. -/
def dSOf (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (β x₀ : ℝ) : ℝ :=
  regimeValue β ((E.sanction11Of hTM) hmono x₀) - regimeValue β ((E.sanction10 hTM) x₀)

/-- Discounted difference of the two sanction paths.
The rally-margin form of `dSOf` (BH4.1). -/
def dS (hTM : E.toChordCs.LossOffset) (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC *
    E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (β x₀ : ℝ) : ℝ :=
  regimeValue β ((E.sanction11 hTM) hmargin x₀) - regimeValue β ((E.sanction10 hTM) x₀)

/-- The bridge (BH4.1): `dS` is `dSOf` at the nondecreasing
response that the rally margin gives. Definitional. General in `F`. -/
theorem dS_eq_dSOf (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (β x₀ : ℝ) :
    (E.dS hTM) hmargin β x₀
      = (E.dSOf hTM) (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) β x₀ := rfl

/-- Discounted difference of the two squared-sanction paths.
This is `dS2` with the rally margin replaced by a response `responsePath VSstar` that is
nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`. General in `F`. -/
def dS2Of (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (β x₀ : ℝ) : ℝ :=
  regimeValue β (fun t => (E.sanction11Of hTM) hmono x₀ t ^ 2)
    - regimeValue β (fun t => (E.sanction10 hTM) x₀ t ^ 2)

/-- Discounted difference of the two squared-sanction paths.
The rally-margin form of `dS2Of` (BH4.1). -/
def dS2 (hTM : E.toChordCs.LossOffset) (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC *
    E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (β x₀ : ℝ) : ℝ :=
  regimeValue β (fun t => (E.sanction11 hTM) hmargin x₀ t ^ 2)
    - regimeValue β (fun t => (E.sanction10 hTM) x₀ t ^ 2)

/-- The bridge (BH4.1): `dS2` is `dS2Of` at the nondecreasing
response that the rally margin gives. Definitional. General in `F`. -/
theorem dS2_eq_dS2Of (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (β x₀ : ℝ) :
    (E.dS2 hTM) hmargin β x₀
      = (E.dS2Of hTM) (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) β x₀ := rfl

theorem abs_le_one_of_mem {y : ℝ} (hy : y ∈ Sanctions.I) : |y| ≤ 1 :=
  abs_le.mpr ⟨by linarith [hy.1], hy.2⟩

theorem abs_sq_le_one_of_mem {y : ℝ} (hy : y ∈ Sanctions.I) : |y ^ 2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg y)]
  nlinarith [hy.1, hy.2]

/-- A regime value is linear in a flow of the form `K·x + η·s − (q/2)·s²`. -/
theorem regimeValue_flow_eq {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) (K η : ℝ)
    {x s : ℕ → ℝ} (hx : ∀ t, x t ∈ Sanctions.I) (hs : ∀ t, s t ∈ Sanctions.I) :
    regimeValue β (fun t => K * x t + η * s t - E.q / 2 * s t ^ 2)
      = K * regimeValue β x + η * regimeValue β s
        - E.q / 2 * regimeValue β (fun t => s t ^ 2) := by
  have hX := (summable_geometric_mul_of_abs_le hβ (fun t => abs_le_one_of_mem (hx t))).hasSum
  have hS := (summable_geometric_mul_of_abs_le hβ (fun t => abs_le_one_of_mem (hs t))).hasSum
  have hS2 := (summable_geometric_mul_of_abs_le hβ
    (f := fun t => s t ^ 2) (fun t => abs_sq_le_one_of_mem (hs t))).hasSum
  have hcomb := ((hX.mul_left K).add (hS.mul_left η)).sub (hS2.mul_left (E.q / 2))
  unfold regimeValue at hcomb ⊢
  rw [← hcomb.tsum_eq]
  exact tsum_congr fun t => by ring

/-- **The decomposition.** For every completion, feasible start and planner
discount, the welfare gap between the forward-looking and the Target-only
regimes is `K·ΔX + η·ΔS − (q/2)·ΔS₂`; the three differences do not depend on
the completion.
This is `regimeValue11_sub_10_eq` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`. General in `F`. -/
theorem regimeValue11_sub_10_eq_of_response_monotone (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C : E.toPlacableEconomyF.WelfareCompletion) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    regimeValue β ((E.flow11Of hTM) hmono C x₀) - regimeValue β ((E.flow10 hTM) C x₀)
      = C.K * (E.dXOf hTM) hmono β x₀ + C.η * (E.dSOf hTM) hmono β x₀ - E.q / 2 *
          (E.dS2Of hTM) hmono β x₀ := by
  have h11 : (E.flow11Of hTM) hmono C x₀
      = fun t => C.K * (E.toChordCs.dynamicPathOf hTM) hmono x₀ t
          + C.η * (E.sanction11Of hTM) hmono x₀ t
          - E.q / 2 * (E.sanction11Of hTM) hmono x₀ t ^ 2 :=
    funext fun t => flow11_eq_of_response_monotone hTM hmono C hx₀ t
  have h10 : (E.flow10 hTM) C x₀
      = fun t => C.K * (E.toChordCs.targetOnlyPath hTM) x₀ t + C.η * (E.sanction10 hTM) x₀ t
          - E.q / 2 * (E.sanction10 hTM) x₀ t ^ 2 :=
    funext fun t => flow10_eq hTM C hx₀ t
  rw [h11, h10,
    regimeValue_flow_eq (E := E) hβ C.K C.η (x := (E.toChordCs.dynamicPathOf hTM) hmono x₀)
      (s := (E.sanction11Of hTM) hmono x₀)
      (fun t => dynamicPath_mem_of_response_monotone hTM hmono hx₀ t)
      (fun t => E.toChordCs.responsePath_mem _ _),
    regimeValue_flow_eq (E := E) hβ C.K C.η (x := (E.toChordCs.targetOnlyPath hTM) x₀)
      (s := (E.sanction10 hTM) x₀) (fun t => targetOnlyPath_mem hTM hx₀ t)
      (fun t => E.toChordCs.σ_mem _ 0)]
  unfold dXOf dSOf dS2Of
  ring

/-- **The decomposition.** For every completion, feasible start and planner
discount, the welfare gap between the forward-looking and the Target-only
regimes is `K·ΔX + η·ΔS − (q/2)·ΔS₂`; the three differences do not depend on
the completion.
The rally-margin form of `regimeValue11_sub_10_eq_of_response_monotone` (BH4.1). -/
theorem regimeValue11_sub_10_eq (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C : E.toPlacableEconomyF.WelfareCompletion) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    regimeValue β ((E.flow11 hTM) hmargin C x₀) - regimeValue β ((E.flow10 hTM) C x₀)
      = C.K * (E.dX hTM) hmargin β x₀ + C.η * (E.dS hTM) hmargin β x₀ - E.q / 2 *
          (E.dS2 hTM) hmargin β x₀ :=
  regimeValue11_sub_10_eq_of_response_monotone (E := E) hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C hx₀ hβ

/-- **The discounted sanction difference is at least `wedge/(1−β)`**, hence
strictly positive: the closed-form wedge holds at every date.
This is `dS_ge` with the rally margin replaced by a response `responsePath VSstar` that is
nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`. General in `F`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem dS_ge_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    E.toChordCs.wedge / (1 - β) ≤ (E.dSOf hTM) hmono β x₀ := by
  have h10 := fun t => targetOnlyPath_mem (E := E) hTM hx₀ t
  have h11 := fun t => dynamicPath_mem_of_response_monotone (E := E) hTM hmono hx₀ t
  have hgap : ∀ t, (E.sanction10 hTM) x₀ t + E.toChordCs.wedge ≤ (E.sanction11Of hTM) hmono x₀ t :=
      by
    intro t
    have h := (E.toChordCs.targetOnlySanction_add_wedge_le_dynamicSanction_of_response_monotone
        hInt hTM) hmono hx₀ t
    rwa [(E.toChordCs.targetOnlyRule_eq_stage hTM) (h10 t),
        (E.toChordCs.dynamicRule_eq_responsePath_of_response_monotone hTM) hmono (h11 t)] at h
  have hS11 := (summable_geometric_mul_of_abs_le hβ
    (f := (E.sanction11Of hTM) hmono x₀) (fun t => abs_le_one_of_mem (E.toChordCs.responsePath_mem _
        _))).hasSum
  have hS10 := (summable_geometric_mul_of_abs_le hβ
    (f := (E.sanction10 hTM) x₀) (fun t => abs_le_one_of_mem (E.toChordCs.σ_mem _ 0))).hasSum
  have hgeo : HasSum (fun t : ℕ => β ^ t * E.toChordCs.wedge) ((1 - β)⁻¹ * E.toChordCs.wedge) :=
    (hasSum_geometric_of_lt_one hβ.1 hβ.2).mul_right _
  have hle := hasSum_le (fun t => ?_) (hS10.add hgeo) hS11
  · unfold dSOf regimeValue
    have : (1 - β)⁻¹ * E.toChordCs.wedge = E.toChordCs.wedge / (1 - β) := by rw [div_eq_inv_mul]
    linarith
  · have hpow : 0 ≤ β ^ t := pow_nonneg hβ.1 t
    have := mul_le_mul_of_nonneg_left (hgap t) hpow
    linarith [mul_add (β ^ t) ((E.sanction10 hTM) x₀ t) E.toChordCs.wedge]

/-- **The discounted sanction difference is at least `wedge/(1−β)`**, hence
strictly positive: the closed-form wedge holds at every date.
The rally-margin form of `dS_ge_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family).
General in `F`. -/
theorem dS_ge (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    E.toChordCs.wedge / (1 - β) ≤ (E.dS hTM) hmargin β x₀ :=
  dS_ge_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin)
    hx₀ hβ

/-- This is `dS_pos` with the rally margin replaced by a response `responsePath VSstar` that
is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`. General in `F`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem dS_pos_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    0 < (E.dSOf hTM) hmono β x₀ :=
  lt_of_lt_of_le (div_pos E.toChordCs.wedge_pos (by linarith [hβ.2]))
      ((E.dS_ge_of_response_monotone hInt hTM) hmono hx₀ hβ)

/-- The rally-margin form of `dS_pos_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family).
General in `F`. -/
theorem dS_pos (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    0 < (E.dS hTM) hmargin β x₀ :=
  dS_pos_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin)
    hx₀ hβ

/-! ## The sharp interval on the restricted class -/

/-- The welfare gap `V¹¹ − V¹⁰` of a completion.
This is `gap` with the rally margin replaced by a response `responsePath VSstar` that is
nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`. General in `F`. -/
def gapOf (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C : E.toPlacableEconomyF.WelfareCompletion) (β x₀ : ℝ) : ℝ :=
  regimeValue β ((E.flow11Of hTM) hmono C x₀) - regimeValue β ((E.flow10 hTM) C x₀)

/-- The welfare gap `V¹¹ − V¹⁰` of a completion.
The rally-margin form of `gapOf` (BH4.1). -/
def gap (hTM : E.toChordCs.LossOffset) (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC *
    E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C : E.toPlacableEconomyF.WelfareCompletion) (β x₀ : ℝ) : ℝ :=
  regimeValue β ((E.flow11 hTM) hmargin C x₀) - regimeValue β ((E.flow10 hTM) C x₀)

/-- The bridge (BH4.1): `gap` is `gapOf` at the nondecreasing
response that the rally margin gives. Definitional. General in `F`. -/
theorem gap_eq_gapOf (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C : E.toPlacableEconomyF.WelfareCompletion) (β x₀ : ℝ) :
    (E.gap hTM) hmargin C β x₀
      = (E.gapOf hTM) (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C β x₀ := rfl

/-- The gap as a function of the state coefficient and the net sanction
coefficient.
This is `gapAt` with the rally margin replaced by a response `responsePath VSstar` that is
nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`. General in `F`. -/
def gapAtOf (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (K η β x₀ : ℝ) : ℝ :=
  K * (E.dXOf hTM) hmono β x₀ + η * (E.dSOf hTM) hmono β x₀ - E.q / 2 * (E.dS2Of hTM) hmono β x₀

/-- The gap as a function of the state coefficient and the net sanction
coefficient.
The rally-margin form of `gapAtOf` (BH4.1). -/
def gapAt (hTM : E.toChordCs.LossOffset) (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC *
    E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (K η β x₀ : ℝ) : ℝ :=
  K * (E.dX hTM) hmargin β x₀ + η * (E.dS hTM) hmargin β x₀ - E.q / 2 * (E.dS2 hTM) hmargin β x₀

/-- The bridge (BH4.1): `gapAt` is `gapAtOf` at the nondecreasing
response that the rally margin gives. Definitional. General in `F`. -/
theorem gapAt_eq_gapAtOf (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (K η β x₀ : ℝ) :
    (E.gapAt hTM) hmargin K η β x₀
      = (E.gapAtOf hTM) (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) K η β x₀ := rfl

/-- This is `gap_eq_gapAt` with the rally margin replaced by a response `responsePath VSstar`
that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`. General in `F`. -/
theorem gap_eq_gapAt_of_response_monotone (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C : E.toPlacableEconomyF.WelfareCompletion) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    (E.gapOf hTM) hmono C β x₀ = (E.gapAtOf hTM) hmono C.K C.η β x₀ :=
  regimeValue11_sub_10_eq_of_response_monotone hTM hmono C hx₀ hβ

/-- The rally-margin form of `gap_eq_gapAt_of_response_monotone` (BH4.1). -/
theorem gap_eq_gapAt (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C : E.toPlacableEconomyF.WelfareCompletion) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    (E.gap hTM) hmargin C β x₀ = (E.gapAt hTM) hmargin C.K C.η β x₀ :=
  gap_eq_gapAt_of_response_monotone (E := E) hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C hx₀ hβ

/-- **On the restricted class the gap lies in the interval** with endpoints at
`η_L` and `η_U`. Round BG3 (BG3.6): no `0 < M`, which follows from the class
(`HawkBounded.upper_pos`). `0 < m` is kept, because membership alone does not
force it: a floor `m ≤ 0` is met vacuously, and then `η_U` lies below every
member's `η`, so the upper bound fails. The range premise `η_L ≤ η_U`, which
would force `0 < m` (`pos_of_etaLo_le_etaHi`), is not assumed here. General in
`F`.
This is `gap_mem_interval` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem gap_mem_interval_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hm : 0 < m)
    (hC : C.HawkBounded Qbar m M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    (E.gapAtOf hTM) hmono C.K (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M)
        β x₀ ≤ (E.gapOf hTM) hmono C β x₀ ∧
    (E.gapOf hTM) hmono C β x₀ ≤
      (E.gapAtOf hTM) hmono C.K
        (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀ := by
  obtain ⟨hlo, hhi⟩ := C.hawkBounded_eta_mem hm hC.upper_pos hC
  have hpos := ((E.dS_pos_of_response_monotone hInt hTM) hmono hx₀ hβ).le
  rw [(E.gap_eq_gapAt_of_response_monotone hTM) hmono C hx₀ hβ]
  unfold gapAtOf
  constructor
  · have := mul_le_mul_of_nonneg_right hlo hpos
    linarith
  · have := mul_le_mul_of_nonneg_right hhi hpos
    linarith

/-- **On the restricted class the gap lies in the interval** with endpoints at
`η_L` and `η_U`. Round BG3 (BG3.6): no `0 < M`, which follows from the class
(`HawkBounded.upper_pos`). `0 < m` is kept, because membership alone does not
force it: a floor `m ≤ 0` is met vacuously, and then `η_U` lies below every
member's `η`, so the upper bound fails. The range premise `η_L ≤ η_U`, which
would force `0 < m` (`pos_of_etaLo_le_etaHi`), is not assumed here. General in
`F`.
The rally-margin form of `gap_mem_interval_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem gap_mem_interval (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hm : 0 < m)
    (hC : C.HawkBounded Qbar m M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    (E.gapAt hTM) hmargin C.K (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M)
        β x₀ ≤ (E.gap hTM) hmargin C β x₀ ∧
    (E.gap hTM) hmargin C β x₀ ≤
      (E.gapAt hTM) hmargin C.K
        (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀ :=
  gap_mem_interval_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C hm hC hx₀ hβ

/-- **Every point of the interval is attained by changing the hawks' benefit
alone**: the attaining completion is `C₀.withSender g_H Q̄`, so its Target side
is `C₀`'s field for field. Round BG3 (BG3.6): no `0 < m`, which follows from
the two endpoint bounds on `g` (they give `η_L ≤ η_U`). General in `F`.
This is `gap_attained_withSender` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem gap_attained_withSender_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {g : ℝ}
    (hlo : (E.gapAtOf hTM) hmono C₀.K
      (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ ≤ g)
    (hhi : g ≤ (E.gapAtOf hTM) hmono C₀.K
      (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀) :
    ∃ (gH : ℝ) (hgH : 0 < gH),
      (C₀.withSender gH Qbar hgH hQbar).HawkBounded Qbar m M ∧
      (E.gapOf hTM) hmono (C₀.withSender gH Qbar hgH hQbar) β x₀ = g := by
  have hpos := (E.dS_pos_of_response_monotone hInt hTM) hmono hx₀ hβ
  set η' := (g - C₀.K * (E.dXOf hTM) hmono β x₀ + E.q / 2 * (E.dS2Of hTM) hmono β x₀)
    / (E.dSOf hTM) hmono β x₀ with hη'
  have hval : C₀.K * (E.dXOf hTM) hmono β x₀ + η' * (E.dSOf hTM) hmono β x₀
      - E.q / 2 * (E.dS2Of hTM) hmono β x₀ = g := by
    rw [hη', div_mul_cancel₀ _ hpos.ne']
    ring
  have h1 : PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M ≤ η' := by
    rw [hη', le_div_iff₀ hpos]
    unfold gapAtOf at hlo
    linarith
  have h2 : η' ≤ PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m := by
    rw [hη', div_le_iff₀ hpos]
    unfold gapAtOf at hhi
    linarith
  obtain ⟨gH, hgH, hC, hη⟩ := C₀.exists_withSender_hawkBounded_eta hQbar hM h1 h2
  refine ⟨gH, hgH, hC, ?_⟩
  rw [(E.gap_eq_gapAt_of_response_monotone hTM) hmono _ hx₀ hβ,
      PlacableEconomyF.WelfareCompletion.withSender_K, hη]
  exact hval

/-- **Every point of the interval is attained by changing the hawks' benefit
alone**: the attaining completion is `C₀.withSender g_H Q̄`, so its Target side
is `C₀`'s field for field. Round BG3 (BG3.6): no `0 < m`, which follows from
the two endpoint bounds on `g` (they give `η_L ≤ η_U`). General in `F`.
The rally-margin form of `gap_attained_withSender_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem gap_attained_withSender (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {g : ℝ}
    (hlo : (E.gapAt hTM) hmargin C₀.K
      (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ ≤ g)
    (hhi : g ≤ (E.gapAt hTM) hmargin C₀.K
      (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀) :
    ∃ (gH : ℝ) (hgH : 0 < gH),
      (C₀.withSender gH Qbar hgH hQbar).HawkBounded Qbar m M ∧
      (E.gap hTM) hmargin (C₀.withSender gH Qbar hgH hQbar) β x₀ = g :=
  gap_attained_withSender_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C₀ hQbar hM hx₀ hβ hlo hhi

/-- **Every point of the interval is attained** by a completion of the class
with the same state coefficient; `gap_attained_withSender_of_response_monotone` names the
completion.
Round BG3 (BG3.6): no `0 < m`. General in `F`.
This is `gap_attained` with the rally margin replaced by a response `responsePath VSstar`
that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem gap_attained_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {g : ℝ}
    (hlo : (E.gapAtOf hTM) hmono C₀.K
      (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ ≤ g)
    (hhi : g ≤ (E.gapAtOf hTM) hmono C₀.K
      (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀) :
    ∃ C : E.toPlacableEconomyF.WelfareCompletion,
      C.HawkBounded Qbar m M ∧ C.K = C₀.K ∧ (E.gapOf hTM) hmono C β x₀ = g := by
  obtain ⟨gH, hgH, hC, hg⟩ :=
    (E.gap_attained_withSender_of_response_monotone hInt hTM) hmono C₀ hQbar hM hx₀ hβ hlo hhi
  exact ⟨_, hC, rfl, hg⟩

/-- **Every point of the interval is attained** by a completion of the class
with the same state coefficient; `gap_attained_withSender` names the completion.
Round BG3 (BG3.6): no `0 < m`. General in `F`.
The rally-margin form of `gap_attained_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem gap_attained (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) {g : ℝ}
    (hlo : (E.gapAt hTM) hmargin C₀.K
      (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ ≤ g)
    (hhi : g ≤ (E.gapAt hTM) hmargin C₀.K
      (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀) :
    ∃ C : E.toPlacableEconomyF.WelfareCompletion,
      C.HawkBounded Qbar m M ∧ C.K = C₀.K ∧ (E.gap hTM) hmargin C β x₀ = g :=
  gap_attained_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C₀ hQbar hM hx₀ hβ hlo hhi

/-- **Identified: the forward-looking regime ranks first** whenever the lower
endpoint is positive. Round BG3: no `0 < M`, which follows from the class, as in
`gap_mem_interval_of_response_monotone` (BG3.6). General in `F`.
This is `gap_pos_of_lower_pos` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem gap_pos_of_lower_pos_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hm : 0 < m)
    (hC : C.HawkBounded Qbar m M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (h : 0 < (E.gapAtOf hTM) hmono C.K
      (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀) :
    regimeValue β ((E.flow10 hTM) C x₀) < regimeValue β ((E.flow11Of hTM) hmono C x₀) := by
  have := ((E.gap_mem_interval_of_response_monotone hInt hTM) hmono C hm hC hx₀ hβ).1
  unfold gapOf at this
  linarith

/-- **Identified: the forward-looking regime ranks first** whenever the lower
endpoint is positive. Round BG3: no `0 < M`, which follows from the class, as in
`gap_mem_interval` (BG3.6). General in `F`.
The rally-margin form of `gap_pos_of_lower_pos_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem gap_pos_of_lower_pos (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hm : 0 < m)
    (hC : C.HawkBounded Qbar m M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (h : 0 < (E.gapAt hTM) hmargin C.K
      (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀) :
    regimeValue β ((E.flow10 hTM) C x₀) < regimeValue β ((E.flow11 hTM) hmargin C x₀) :=
  gap_pos_of_lower_pos_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C hm hC hx₀ hβ h

/-- **Identified: the Target-only regime ranks first** whenever the upper
endpoint is negative. Round BG3: no `0 < M`, which follows from the class, as in
`gap_mem_interval_of_response_monotone` (BG3.6). General in `F`.
This is `gap_neg_of_upper_neg` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem gap_neg_of_upper_neg_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hm : 0 < m)
    (hC : C.HawkBounded Qbar m M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (h : (E.gapAtOf hTM) hmono C.K
      (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀ < 0) :
    regimeValue β ((E.flow11Of hTM) hmono C x₀) < regimeValue β ((E.flow10 hTM) C x₀) := by
  have := ((E.gap_mem_interval_of_response_monotone hInt hTM) hmono C hm hC hx₀ hβ).2
  unfold gapOf at this
  linarith

/-- **Identified: the Target-only regime ranks first** whenever the upper
endpoint is negative. Round BG3: no `0 < M`, which follows from the class, as in
`gap_mem_interval` (BG3.6). General in `F`.
The rally-margin form of `gap_neg_of_upper_neg_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem gap_neg_of_upper_neg (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hm : 0 < m)
    (hC : C.HawkBounded Qbar m M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (h : (E.gapAt hTM) hmargin C.K
      (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀ < 0) :
    regimeValue β ((E.flow11 hTM) hmargin C x₀) < regimeValue β ((E.flow10 hTM) C x₀) :=
  gap_neg_of_upper_neg_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C hm hC hx₀ hβ h

/-- **Not identified when the interval straddles zero**: both strict rankings
occur inside the class, at completions that differ from `C₀` in the hawks'
benefit alone, so the Target side is `C₀`'s field for field. Round BG3
(BG3.6): no `0 < m`, which follows from the straddle (it gives `η_L < η_U`).
General in `F`.
This is `exists_withSender_both_signs_of_straddle` with the rally margin replaced by a
response `responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item
BH4.1, 2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem exists_withSender_both_signs_of_straddle_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hlo : (E.gapAtOf hTM) hmono C₀.K
      (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ < 0)
    (hhi : 0 < (E.gapAtOf hTM) hmono C₀.K
      (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀) :
    ∃ (gp : ℝ) (hgp : 0 < gp) (gm : ℝ) (hgm : 0 < gm),
      (C₀.withSender gp Qbar hgp hQbar).HawkBounded Qbar m M ∧
      (C₀.withSender gm Qbar hgm hQbar).HawkBounded Qbar m M ∧
      regimeValue β ((E.flow10 hTM) (C₀.withSender gp Qbar hgp hQbar) x₀)
        < regimeValue β ((E.flow11Of hTM) hmono (C₀.withSender gp Qbar hgp hQbar) x₀) ∧
      regimeValue β ((E.flow11Of hTM) hmono (C₀.withSender gm Qbar hgm hQbar) x₀)
        < regimeValue β ((E.flow10 hTM) (C₀.withSender gm Qbar hgm hQbar) x₀) := by
  obtain ⟨gp, hgp, hCp, hgapp⟩ :=
      (E.gap_attained_withSender_of_response_monotone hInt hTM) hmono C₀ hQbar hM hx₀ hβ
    (g := (E.gapAtOf hTM) hmono C₀.K
      (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀)
    (by linarith) le_rfl
  obtain ⟨gm, hgm, hCm, hgapm⟩ :=
      (E.gap_attained_withSender_of_response_monotone hInt hTM) hmono C₀ hQbar hM hx₀ hβ
    (g := (E.gapAtOf hTM) hmono C₀.K
      (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀)
    le_rfl (by linarith)
  refine ⟨gp, hgp, gm, hgm, hCp, hCm, ?_, ?_⟩
  · unfold gapOf at hgapp; linarith
  · unfold gapOf at hgapm; linarith

/-- **Not identified when the interval straddles zero**: both strict rankings
occur inside the class, at completions that differ from `C₀` in the hawks'
benefit alone, so the Target side is `C₀`'s field for field. Round BG3
(BG3.6): no `0 < m`, which follows from the straddle (it gives `η_L < η_U`).
General in `F`.
The rally-margin form of `exists_withSender_both_signs_of_straddle_of_response_monotone`
(BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem exists_withSender_both_signs_of_straddle (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hlo : (E.gapAt hTM) hmargin C₀.K
      (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ < 0)
    (hhi : 0 < (E.gapAt hTM) hmargin C₀.K
      (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀) :
    ∃ (gp : ℝ) (hgp : 0 < gp) (gm : ℝ) (hgm : 0 < gm),
      (C₀.withSender gp Qbar hgp hQbar).HawkBounded Qbar m M ∧
      (C₀.withSender gm Qbar hgm hQbar).HawkBounded Qbar m M ∧
      regimeValue β ((E.flow10 hTM) (C₀.withSender gp Qbar hgp hQbar) x₀)
        < regimeValue β ((E.flow11 hTM) hmargin (C₀.withSender gp Qbar hgp hQbar) x₀) ∧
      regimeValue β ((E.flow11 hTM) hmargin (C₀.withSender gm Qbar hgm hQbar) x₀)
        < regimeValue β ((E.flow10 hTM) (C₀.withSender gm Qbar hgm hQbar) x₀) :=
  exists_withSender_both_signs_of_straddle_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C₀ hQbar hM hx₀ hβ hlo hhi

/-- **Not identified when the interval straddles zero**: both rankings occur
inside the class, with the state coefficient held fixed;
`exists_withSender_both_signs_of_straddle_of_response_monotone` names the two completions. Round
BG3 (BG3.6): no `0 < m`, which follows from the straddle. General in `F`.
This is `exists_both_signs_of_straddle` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem exists_both_signs_of_straddle_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hlo : (E.gapAtOf hTM) hmono C₀.K
      (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ < 0)
    (hhi : 0 < (E.gapAtOf hTM) hmono C₀.K
      (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀) :
    ∃ Cp Cm : E.toPlacableEconomyF.WelfareCompletion,
      Cp.HawkBounded Qbar m M ∧ Cm.HawkBounded Qbar m M ∧ Cp.K = C₀.K ∧ Cm.K = C₀.K ∧
      regimeValue β ((E.flow10 hTM) Cp x₀) < regimeValue β ((E.flow11Of hTM) hmono Cp x₀) ∧
      regimeValue β ((E.flow11Of hTM) hmono Cm x₀) < regimeValue β ((E.flow10 hTM) Cm x₀) := by
  obtain ⟨gp, hgp, gm, hgm, hCp, hCm, hp, hmm⟩ :=
    (E.exists_withSender_both_signs_of_straddle_of_response_monotone hInt hTM) hmono C₀ hQbar hM
        hx₀ hβ hlo hhi
  exact ⟨_, _, hCp, hCm, rfl, rfl, hp, hmm⟩

/-- **Not identified when the interval straddles zero**: both rankings occur
inside the class, with the state coefficient held fixed;
`exists_withSender_both_signs_of_straddle` names the two completions. Round
BG3 (BG3.6): no `0 < m`, which follows from the straddle. General in `F`.
The rally-margin form of `exists_both_signs_of_straddle_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem exists_both_signs_of_straddle (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hlo : (E.gapAt hTM) hmargin C₀.K
      (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ < 0)
    (hhi : 0 < (E.gapAt hTM) hmargin C₀.K
      (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀) :
    ∃ Cp Cm : E.toPlacableEconomyF.WelfareCompletion,
      Cp.HawkBounded Qbar m M ∧ Cm.HawkBounded Qbar m M ∧ Cp.K = C₀.K ∧ Cm.K = C₀.K ∧
      regimeValue β ((E.flow10 hTM) Cp x₀) < regimeValue β ((E.flow11 hTM) hmargin Cp x₀) ∧
      regimeValue β ((E.flow11 hTM) hmargin Cm x₀) < regimeValue β ((E.flow10 hTM) Cm x₀) :=
  exists_both_signs_of_straddle_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C₀ hQbar hM hx₀ hβ hlo hhi

/-! ## What the interval identifies, as equivalences (the reader's D3, 2026-09-21)

"Identified exactly when the interval excludes zero" is three statements, and
they differ at a zero endpoint. `hne` says the class is non-empty
(`hawkBounded_nonempty_iff`); without it the universal statements are vacuous. -/

/-- The endpoints are ordered on a non-empty class.
This is `gapAt_lo_le_hi` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`. General in `F`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem gapAt_lo_le_hi_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (K : ℝ) {Qbar m M : ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hne : PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M
      ≤ PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) :
    (E.gapAtOf hTM) hmono K
        (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀
      ≤ (E.gapAtOf hTM) hmono K
          (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀ := by
  have hpos := ((E.dS_pos_of_response_monotone hInt hTM) hmono hx₀ hβ).le
  have hmul := mul_le_mul_of_nonneg_right hne hpos
  unfold gapAtOf
  linarith

/-- The endpoints are ordered on a non-empty class.
The rally-margin form of `gapAt_lo_le_hi_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family).
General in `F`. -/
theorem gapAt_lo_le_hi (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (K : ℝ) {Qbar m M : ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hne : PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M
      ≤ PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) :
    (E.gapAt hTM) hmargin K
        (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀
      ≤ (E.gapAt hTM) hmargin K
          (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀ :=
  gapAt_lo_le_hi_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) K hx₀ hβ hne

/-- **A uniform strict ranking `11 ≻ 10`** over the class at the given state
coefficient holds exactly when the lower endpoint is positive. Round BG3
(BG3.6): no `0 < m`, which follows from `hne` (`pos_of_etaLo_le_etaHi`). General
in `F`.
This is `forall_gap_pos_iff` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family).
General in `F`. -/
theorem forall_gap_pos_iff_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hne : PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M
      ≤ PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) :
    (∀ C : E.toPlacableEconomyF.WelfareCompletion, C.HawkBounded Qbar m M → C.K = C₀.K →
        regimeValue β ((E.flow10 hTM) C x₀) < regimeValue β ((E.flow11Of hTM) hmono C x₀)) ↔
      0 < (E.gapAtOf hTM) hmono C₀.K
          (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ := by
  have hm : 0 < m := PlacableEconomyF.WelfareCompletion.pos_of_etaLo_le_etaHi hQbar.le hM hne
  constructor
  · intro h
    obtain ⟨gH, hgH, hC, hg⟩ :=
      (E.gap_attained_withSender_of_response_monotone hInt hTM) hmono C₀ hQbar
        hM hx₀ hβ
      (g := (E.gapAtOf hTM) hmono C₀.K
          (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀)
      le_rfl ((E.gapAt_lo_le_hi_of_response_monotone hInt hTM) hmono C₀.K hx₀ hβ hne)
    have hlt := h _ hC rfl
    unfold gapOf at hg
    linarith
  · intro h C hC hK
    exact (E.gap_pos_of_lower_pos_of_response_monotone hInt hTM) hmono C hm hC hx₀ hβ
        (by rw [hK]; exact h)

/-- **A uniform strict ranking `11 ≻ 10`** over the class at the given state
coefficient holds exactly when the lower endpoint is positive. Round BG3
(BG3.6): no `0 < m`, which follows from `hne` (`pos_of_etaLo_le_etaHi`). General
in `F`.
The rally-margin form of `forall_gap_pos_iff_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family).
General in `F`. -/
theorem forall_gap_pos_iff (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hne : PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M
      ≤ PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) :
    (∀ C : E.toPlacableEconomyF.WelfareCompletion, C.HawkBounded Qbar m M → C.K = C₀.K →
        regimeValue β ((E.flow10 hTM) C x₀) < regimeValue β ((E.flow11 hTM) hmargin C x₀)) ↔
      0 < (E.gapAt hTM) hmargin C₀.K
          (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ :=
  forall_gap_pos_iff_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C₀ hQbar hM hx₀ hβ hne

/-- **A uniform strict ranking `10 ≻ 11`** holds exactly when the upper endpoint
is negative. Round BG3 (BG3.6): no `0 < m`, which follows from `hne`
(`pos_of_etaLo_le_etaHi`). General in `F`.
This is `forall_gap_neg_iff` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem forall_gap_neg_iff_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hne : PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M
      ≤ PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) :
    (∀ C : E.toPlacableEconomyF.WelfareCompletion, C.HawkBounded Qbar m M → C.K = C₀.K →
        regimeValue β ((E.flow11Of hTM) hmono C x₀) < regimeValue β ((E.flow10 hTM) C x₀)) ↔
      (E.gapAtOf hTM) hmono C₀.K
          (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀ < 0 := by
  have hm : 0 < m := PlacableEconomyF.WelfareCompletion.pos_of_etaLo_le_etaHi hQbar.le hM hne
  constructor
  · intro h
    obtain ⟨gH, hgH, hC, hg⟩ :=
      (E.gap_attained_withSender_of_response_monotone hInt hTM) hmono C₀ hQbar
        hM hx₀ hβ
      (g := (E.gapAtOf hTM) hmono C₀.K
          (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀)
      ((E.gapAt_lo_le_hi_of_response_monotone hInt hTM) hmono C₀.K hx₀ hβ hne) le_rfl
    have hlt := h _ hC rfl
    unfold gapOf at hg
    linarith
  · intro h C hC hK
    exact (E.gap_neg_of_upper_neg_of_response_monotone hInt hTM) hmono C hm hC hx₀ hβ
        (by rw [hK]; exact h)

/-- **A uniform strict ranking `10 ≻ 11`** holds exactly when the upper endpoint
is negative. Round BG3 (BG3.6): no `0 < m`, which follows from `hne`
(`pos_of_etaLo_le_etaHi`). General in `F`.
The rally-margin form of `forall_gap_neg_iff_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem forall_gap_neg_iff (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (hne : PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M
      ≤ PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) :
    (∀ C : E.toPlacableEconomyF.WelfareCompletion, C.HawkBounded Qbar m M → C.K = C₀.K →
        regimeValue β ((E.flow11 hTM) hmargin C x₀) < regimeValue β ((E.flow10 hTM) C x₀)) ↔
      (E.gapAt hTM) hmargin C₀.K
          (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀ < 0 :=
  forall_gap_neg_iff_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C₀ hQbar hM hx₀ hβ hne

/-- **Both strict rankings occur** inside the class at the given state
coefficient exactly when the endpoints have opposite strict signs. An endpoint
at zero therefore leaves a weak ordering, and `[0,0]` a tie. Unlike its
neighbours this keeps `0 < m` and `0 < M` (round BG3, BG3.6): the forward
direction reads `η_U`, and at `M ≤ 0` the class is empty while the endpoint
condition can still hold. General in `F`.
This is `exists_both_signs_iff` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem exists_both_signs_iff_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hm : 0 < m) (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    (∃ Cp Cm : E.toPlacableEconomyF.WelfareCompletion,
      Cp.HawkBounded Qbar m M ∧ Cm.HawkBounded Qbar m M ∧ Cp.K = C₀.K ∧ Cm.K = C₀.K ∧
      regimeValue β ((E.flow10 hTM) Cp x₀) < regimeValue β ((E.flow11Of hTM) hmono Cp x₀) ∧
      regimeValue β ((E.flow11Of hTM) hmono Cm x₀) < regimeValue β ((E.flow10 hTM) Cm x₀)) ↔
      (E.gapAtOf hTM) hmono C₀.K
          (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ < 0 ∧
      0 < (E.gapAtOf hTM) hmono C₀.K
          (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀ := by
  constructor
  · rintro ⟨Cp, Cm, hCp, hCm, hKp, hKm, hp, hmm⟩
    have hip := ((E.gap_mem_interval_of_response_monotone hInt hTM) hmono Cp hm hCp hx₀ hβ).2
    have him := ((E.gap_mem_interval_of_response_monotone hInt hTM) hmono Cm hm hCm hx₀ hβ).1
    rw [hKp] at hip
    rw [hKm] at him
    unfold gapOf at hip him
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    exact (E.exists_both_signs_of_straddle_of_response_monotone hInt hTM) hmono C₀ hQbar hM hx₀ hβ
      hlo
        hhi

/-- **Both strict rankings occur** inside the class at the given state
coefficient exactly when the endpoints have opposite strict signs. An endpoint
at zero therefore leaves a weak ordering, and `[0,0]` a tie. Unlike its
neighbours this keeps `0 < m` and `0 < M` (round BG3, BG3.6): the forward
direction reads `η_U`, and at `M ≤ 0` the class is empty while the endpoint
condition can still hold. General in `F`.
The rally-margin form of `exists_both_signs_iff_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem exists_both_signs_iff (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {Qbar m M : ℝ} (hQbar : 0 < Qbar)
    (hm : 0 < m) (hM : 0 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    (∃ Cp Cm : E.toPlacableEconomyF.WelfareCompletion,
      Cp.HawkBounded Qbar m M ∧ Cm.HawkBounded Qbar m M ∧ Cp.K = C₀.K ∧ Cm.K = C₀.K ∧
      regimeValue β ((E.flow10 hTM) Cp x₀) < regimeValue β ((E.flow11 hTM) hmargin Cp x₀) ∧
      regimeValue β ((E.flow11 hTM) hmargin Cm x₀) < regimeValue β ((E.flow10 hTM) Cm x₀)) ↔
      (E.gapAt hTM) hmargin C₀.K
          (PlacableEconomyF.WelfareCompletion.etaLo E.toPlacableEconomyF Qbar M) β x₀ < 0 ∧
      0 < (E.gapAt hTM) hmargin C₀.K
          (PlacableEconomyF.WelfareCompletion.etaHi E.toPlacableEconomyF Qbar m) β x₀ :=
  exists_both_signs_iff_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C₀ hQbar hm hM hx₀ hβ

/-! ## Weight bounds alone identify nothing (Rule 11) -/

/-- With a weight band that straddles one and no bound on exposure, the net
sanction coefficient is unbounded above inside the band. -/
theorem exists_withSender_weightBounded_eta_gt
    (C₀ : E.toPlacableEconomyF.WelfareCompletion)
    {m M : ℝ} (hm : 0 < m) (hm1 : m < 1) (hM1 : 1 < M) (N : ℝ) :
    ∃ (gH Q : ℝ) (hgH : 0 < gH) (hQ : 0 < Q),
      (C₀.withSender gH Q hgH hQ).WeightBounded m M ∧ N < (C₀.withSender gH Q hgH hQ).η := by
  have hM : 0 < M := by linarith
  have hMm : 0 < M - m := by linarith
  have h1m : 0 < 1 - m := by linarith
  set Q := 1 + m * E.r / (M - m) + |N + E.c| * m / (1 - m) with hQdef
  have hQ1 : 0 ≤ m * E.r / (M - m) := div_nonneg (mul_nonneg hm.le E.hr) hMm.le
  have hQ2 : 0 ≤ |N + E.c| * m / (1 - m) := div_nonneg (mul_nonneg (abs_nonneg _) hm.le) h1m.le
  have hQpos : 0 < Q := by rw [hQdef]; linarith
  have hnum : 0 < E.u₀ + Q := by linarith [E.hu₀]
  have hg : 0 < (E.u₀ + Q) / m := div_pos hnum hm
  refine ⟨(E.u₀ + Q) / m, Q, hg, hQpos, ?_, ?_⟩
  · rw [PlacableEconomyF.WelfareCompletion.weightBounded_iff _ hm hM]
    refine ⟨?_, le_rfl⟩
    change (E.u₀ + Q + E.r) / M ≤ (E.u₀ + Q) / m
    rw [div_le_div_iff₀ hM hm]
    -- `(M − m)(u₀ + Q) ≥ m r`
    have hQge : m * E.r / (M - m) ≤ E.u₀ + Q := by rw [hQdef]; linarith [E.hu₀]
    have := (div_le_iff₀ hMm).mp hQge
    nlinarith
  · change N < (E.u₀ + Q) / m - Q - E.c
    have hQge : |N + E.c| * m / (1 - m) ≤ Q := by rw [hQdef]; linarith
    have hQmul : |N + E.c| * m ≤ Q * (1 - m) := (div_le_iff₀ h1m).mp hQge
    have habs : N + E.c ≤ |N + E.c| := le_abs_self _
    have key : (N + E.c) * m < E.u₀ + Q - Q * m := by
      have h1 : (N + E.c) * m ≤ |N + E.c| * m := mul_le_mul_of_nonneg_right habs hm.le
      nlinarith [E.hu₀]
    have : N + E.c + Q < (E.u₀ + Q) / m := by
      rw [lt_div_iff₀ hm]
      nlinarith
    linarith

/-- The same with the state coefficient in the statement;
`exists_withSender_weightBounded_eta_gt` names the completion. -/
theorem exists_weightBounded_eta_gt (C₀ : E.toPlacableEconomyF.WelfareCompletion)
    {m M : ℝ} (hm : 0 < m) (hm1 : m < 1) (hM1 : 1 < M) (N : ℝ) :
    ∃ C : E.toPlacableEconomyF.WelfareCompletion,
      C.WeightBounded m M ∧ C.K = C₀.K ∧ N < C.η := by
  obtain ⟨gH, Q, hgH, hQ, hW, hη⟩ := E.exists_withSender_weightBounded_eta_gt C₀ hm hm1 hM1 N
  exact ⟨_, hW, rfl, hη⟩

/-- … and unbounded below. -/
theorem exists_withSender_weightBounded_eta_lt
    (C₀ : E.toPlacableEconomyF.WelfareCompletion)
    {m M : ℝ} (hm : 0 < m) (hm1 : m < 1) (hM1 : 1 < M) (N : ℝ) :
    ∃ (gH Q : ℝ) (hgH : 0 < gH) (hQ : 0 < Q),
      (C₀.withSender gH Q hgH hQ).WeightBounded m M ∧ (C₀.withSender gH Q hgH hQ).η < -N := by
  have hM : 0 < M := by linarith
  have hMm : 0 < M - m := by linarith
  have hM1' : 0 < M - 1 := by linarith
  set Q := 1 + m * E.r / (M - m) + (|N| * M + E.u₀ + E.r) / (M - 1) with hQdef
  have hQ1 : 0 ≤ m * E.r / (M - m) := div_nonneg (mul_nonneg hm.le E.hr) hMm.le
  have hQ2 : 0 ≤ (|N| * M + E.u₀ + E.r) / (M - 1) :=
    div_nonneg (by have := mul_nonneg (abs_nonneg N) hM.le; linarith [E.hu₀, E.hr]) hM1'.le
  have hQpos : 0 < Q := by rw [hQdef]; linarith
  have hnum : 0 < E.u₀ + Q + E.r := by linarith [E.hu₀, E.hr]
  have hg : 0 < (E.u₀ + Q + E.r) / M := div_pos hnum hM
  refine ⟨(E.u₀ + Q + E.r) / M, Q, hg, hQpos, ?_, ?_⟩
  · rw [PlacableEconomyF.WelfareCompletion.weightBounded_iff _ hm hM]
    refine ⟨le_rfl, ?_⟩
    change (E.u₀ + Q + E.r) / M ≤ (E.u₀ + Q) / m
    rw [div_le_div_iff₀ hM hm]
    have hQge : m * E.r / (M - m) ≤ E.u₀ + Q := by rw [hQdef]; linarith [E.hu₀]
    have := (div_le_iff₀ hMm).mp hQge
    nlinarith
  · change (E.u₀ + Q + E.r) / M - Q - E.c < -N
    have hQge : (|N| * M + E.u₀ + E.r) / (M - 1) ≤ Q := by rw [hQdef]; linarith
    have hQmul : |N| * M + E.u₀ + E.r ≤ Q * (M - 1) := (div_le_iff₀ hM1').mp hQge
    have habs : N ≤ |N| := le_abs_self _
    have hNM : N * M ≤ |N| * M := mul_le_mul_of_nonneg_right habs hM.le
    have : (E.u₀ + Q + E.r) / M < Q + E.c - N := by
      rw [div_lt_iff₀ hM]
      nlinarith [(show (0:ℝ) < E.c from E.toChordCs.c_pos)]
    linarith

/-- The same with the state coefficient in the statement;
`exists_withSender_weightBounded_eta_lt` names the completion. -/
theorem exists_weightBounded_eta_lt (C₀ : E.toPlacableEconomyF.WelfareCompletion)
    {m M : ℝ} (hm : 0 < m) (hm1 : m < 1) (hM1 : 1 < M) (N : ℝ) :
    ∃ C : E.toPlacableEconomyF.WelfareCompletion,
      C.WeightBounded m M ∧ C.K = C₀.K ∧ C.η < -N := by
  obtain ⟨gH, Q, hgH, hQ, hW, hη⟩ := E.exists_withSender_weightBounded_eta_lt C₀ hm hm1 hM1 N
  exact ⟨_, hW, rfl, hη⟩

/-- **A weight band that straddles one does not identify the ranking.** With
`m < 1 < M` on the hawks' weight, exposure unrestricted and the Target side of
`C₀` kept field for field, one completion inside the band ranks the
forward-looking regime above the Target-only regime and another ranks it
below, at any given start and planner discount. This refutes identification
from such a band; it says nothing about a band that does not straddle one.
Round BG3 (BG3.6): no `0 < m`. The band condition only gets easier as `m` falls,
so the proof works at `max m ½ ∈ (0, 1)` and widens the band
(`WeightBounded.mono_lower`). General in `F`.
This is `exists_withSender_weightBounded_reversal` with the rally margin replaced by a
response `responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item
BH4.1, 2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem exists_withSender_weightBounded_reversal_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {m M : ℝ} (hm1 : m < 1)
    (hM1 : 1 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    ∃ (gp Qp : ℝ) (hgp : 0 < gp) (hQp : 0 < Qp) (gm Qm : ℝ) (hgm : 0 < gm) (hQm : 0 < Qm),
      (C₀.withSender gp Qp hgp hQp).WeightBounded m M ∧
      (C₀.withSender gm Qm hgm hQm).WeightBounded m M ∧
      regimeValue β ((E.flow10 hTM) (C₀.withSender gp Qp hgp hQp) x₀)
        < regimeValue β ((E.flow11Of hTM) hmono (C₀.withSender gp Qp hgp hQp) x₀) ∧
      regimeValue β ((E.flow11Of hTM) hmono (C₀.withSender gm Qm hgm hQm) x₀)
        < regimeValue β ((E.flow10 hTM) (C₀.withSender gm Qm hgm hQm) x₀) := by
  -- work at the lower bound `m' = max m ½`, which lies in `(0, 1)`
  have hm'0 : 0 < max m (1 / 2) := lt_max_of_lt_right (by norm_num)
  have hm'1 : max m (1 / 2) < 1 := max_lt hm1 (by norm_num)
  have hmm' : m ≤ max m (1 / 2) := le_max_left _ _
  have hpos := (E.dS_pos_of_response_monotone hInt hTM) hmono hx₀ hβ
  set R := C₀.K * (E.dXOf hTM) hmono β x₀ - E.q / 2 * (E.dS2Of hTM) hmono β x₀ with hR
  obtain ⟨gp, Qp, hgp, hQp, hWp, hηp⟩ := E.exists_withSender_weightBounded_eta_gt C₀ hm'0 hm'1 hM1
    (|R| / (E.dSOf hTM) hmono β x₀)
  obtain ⟨gm, Qm, hgm, hQm, hWm, hηm⟩ := E.exists_withSender_weightBounded_eta_lt C₀ hm'0 hm'1 hM1
    (|R| / (E.dSOf hTM) hmono β x₀)
  refine ⟨gp, Qp, hgp, hQp, gm, Qm, hgm, hQm, hWp.mono_lower _ hmm', hWm.mono_lower _ hmm', ?_, ?_⟩
  · have hg := regimeValue11_sub_10_eq_of_response_monotone hTM hmono
      (C₀.withSender gp Qp hgp hQp) hx₀ hβ
    rw [PlacableEconomyF.WelfareCompletion.withSender_K] at hg
    have h1 : |R| < (C₀.withSender gp Qp hgp hQp).η * (E.dSOf hTM) hmono β x₀ := by
      have := (div_lt_iff₀ hpos).mp hηp
      linarith
    have h2 : -|R| ≤ R := neg_abs_le R
    linarith
  · have hg := regimeValue11_sub_10_eq_of_response_monotone hTM hmono
      (C₀.withSender gm Qm hgm hQm) hx₀ hβ
    rw [PlacableEconomyF.WelfareCompletion.withSender_K] at hg
    have h1 : (C₀.withSender gm Qm hgm hQm).η * (E.dSOf hTM) hmono β x₀ < -|R| := by
      have hmul := mul_lt_mul_of_pos_right hηm hpos
      have e : -(|R| / (E.dSOf hTM) hmono β x₀) * (E.dSOf hTM) hmono β x₀ = -|R| := by
        rw [neg_mul, div_mul_cancel₀ _ hpos.ne']
      linarith
    have h2 : R ≤ |R| := le_abs_self R
    linarith

/-- **A weight band that straddles one does not identify the ranking.** With
`m < 1 < M` on the hawks' weight, exposure unrestricted and the Target side of
`C₀` kept field for field, one completion inside the band ranks the
forward-looking regime above the Target-only regime and another ranks it
below, at any given start and planner discount. This refutes identification
from such a band; it says nothing about a band that does not straddle one.
Round BG3 (BG3.6): no `0 < m`. The band condition only gets easier as `m` falls,
so the proof works at `max m ½ ∈ (0, 1)` and widens the band
(`WeightBounded.mono_lower`). General in `F`.
The rally-margin form of `exists_withSender_weightBounded_reversal_of_response_monotone`
(BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem exists_withSender_weightBounded_reversal (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {m M : ℝ} (hm1 : m < 1)
    (hM1 : 1 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    ∃ (gp Qp : ℝ) (hgp : 0 < gp) (hQp : 0 < Qp) (gm Qm : ℝ) (hgm : 0 < gm) (hQm : 0 < Qm),
      (C₀.withSender gp Qp hgp hQp).WeightBounded m M ∧
      (C₀.withSender gm Qm hgm hQm).WeightBounded m M ∧
      regimeValue β ((E.flow10 hTM) (C₀.withSender gp Qp hgp hQp) x₀)
        < regimeValue β ((E.flow11 hTM) hmargin (C₀.withSender gp Qp hgp hQp) x₀) ∧
      regimeValue β ((E.flow11 hTM) hmargin (C₀.withSender gm Qm hgm hQm) x₀)
        < regimeValue β ((E.flow10 hTM) (C₀.withSender gm Qm hgm hQm) x₀) :=
  exists_withSender_weightBounded_reversal_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C₀ hm1 hM1 hx₀ hβ

/-- **Weight bounds alone do not identify the ranking**, with the state
coefficient in the statement; `exists_withSender_weightBounded_reversal_of_response_monotone` names
the two completions. Round BG3 (BG3.6): no `0 < m`, as in
`exists_withSender_weightBounded_reversal_of_response_monotone`. General in `F`.
This is `exists_weightBounded_reversal` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`.
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem exists_weightBounded_reversal_of_response_monotone (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {m M : ℝ} (hm1 : m < 1)
    (hM1 : 1 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Cp Cm : E.toPlacableEconomyF.WelfareCompletion,
      Cp.WeightBounded m M ∧ Cm.WeightBounded m M ∧ Cp.K = C₀.K ∧ Cm.K = C₀.K ∧
      regimeValue β ((E.flow10 hTM) Cp x₀) < regimeValue β ((E.flow11Of hTM) hmono Cp x₀) ∧
      regimeValue β ((E.flow11Of hTM) hmono Cm x₀) < regimeValue β ((E.flow10 hTM) Cm x₀) := by
  obtain ⟨gp, Qp, hgp, hQp, gm, Qm, hgm, hQm, hWp, hWm, hp, hmm⟩ :=
    (E.exists_withSender_weightBounded_reversal_of_response_monotone hInt hTM) hmono C₀ hm1 hM1
      hx₀ hβ
  exact ⟨_, _, hWp, hWm, rfl, rfl, hp, hmm⟩

/-- **Weight bounds alone do not identify the ranking**, with the state
coefficient in the statement; `exists_withSender_weightBounded_reversal` names
the two completions. Round BG3 (BG3.6): no `0 < m`, as in
`exists_withSender_weightBounded_reversal`. General in `F`.
The rally-margin form of `exists_weightBounded_reversal_of_response_monotone` (BH4.1).
Interiority `hInt` is a hypothesis since renovation item BJ2.3 (it was a field of the family). -/
theorem exists_weightBounded_reversal (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C₀ : E.toPlacableEconomyF.WelfareCompletion) {m M : ℝ} (hm1 : m < 1)
    (hM1 : 1 < M) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) {β : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Cp Cm : E.toPlacableEconomyF.WelfareCompletion,
      Cp.WeightBounded m M ∧ Cm.WeightBounded m M ∧ Cp.K = C₀.K ∧ Cm.K = C₀.K ∧
      regimeValue β ((E.flow10 hTM) Cp x₀) < regimeValue β ((E.flow11 hTM) hmargin Cp x₀) ∧
      regimeValue β ((E.flow11 hTM) hmargin Cm x₀) < regimeValue β ((E.flow10 hTM) Cm x₀) :=
  exists_weightBounded_reversal_of_response_monotone (E := E) hInt hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C₀ hm1 hM1 hx₀ hβ

end PlacableEconomyFcs

end

#print axioms PlacableEconomyF.WelfareCompletion.hawkBounded_iff
#print axioms PlacableEconomyF.WelfareCompletion.exists_withSender_hawkBounded_eta
#print axioms PlacableEconomyF.WelfareCompletion.exists_hawkBounded_eta
#print axioms PlacableEconomyF.hawkBounded_nonempty_iff
#print axioms PlacableEconomyFcs.regimeValue11_sub_10_eq
#print axioms PlacableEconomyFcs.dS_ge
#print axioms PlacableEconomyFcs.gap_mem_interval
#print axioms PlacableEconomyFcs.gap_attained_withSender
#print axioms PlacableEconomyFcs.gap_attained
#print axioms PlacableEconomyFcs.exists_withSender_both_signs_of_straddle
#print axioms PlacableEconomyFcs.exists_both_signs_of_straddle
#print axioms PlacableEconomyFcs.forall_gap_pos_iff
#print axioms PlacableEconomyFcs.forall_gap_neg_iff
#print axioms PlacableEconomyFcs.exists_both_signs_iff
#print axioms PlacableEconomyFcs.exists_withSender_weightBounded_reversal
#print axioms PlacableEconomyFcs.exists_weightBounded_reversal
#print axioms PlacableEconomyFcs.regimeValue11_sub_10_eq_of_response_monotone
#print axioms PlacableEconomyFcs.dS_ge_of_response_monotone
#print axioms PlacableEconomyFcs.gap_mem_interval_of_response_monotone
#print axioms PlacableEconomyFcs.gap_attained_withSender_of_response_monotone
#print axioms PlacableEconomyFcs.gap_attained_of_response_monotone
#print axioms PlacableEconomyFcs.exists_withSender_both_signs_of_straddle_of_response_monotone
#print axioms PlacableEconomyFcs.exists_both_signs_of_straddle_of_response_monotone
#print axioms PlacableEconomyFcs.forall_gap_pos_iff_of_response_monotone
#print axioms PlacableEconomyFcs.forall_gap_neg_iff_of_response_monotone
#print axioms PlacableEconomyFcs.exists_both_signs_iff_of_response_monotone
#print axioms PlacableEconomyFcs.exists_withSender_weightBounded_reversal_of_response_monotone
#print axioms PlacableEconomyFcs.exists_weightBounded_reversal_of_response_monotone

end Examples
end Sanctions
