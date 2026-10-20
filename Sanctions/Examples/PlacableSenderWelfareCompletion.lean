/-
Sanctions/Examples/PlacableSenderWelfareCompletion.lean

**Welfare completions of the placable family, and the family-wide
non-identification of the four-regime welfare ranking** (round AB,
2026-09-19; the reader's family-welfare challenge of 2026-09-19, nodes W0–W6;
Lean first, on the user's word; in the manuscript since round AC as the
family-wide welfare statements of Appendix E; the boundary bridge of §"at the
constructed equilibrium" added in round AE, 2026-09-20).

STATUS OF THE MODELLING CHOICE. A `WelfareCompletion` is a *new accounting
object*, not a hypothesis on the game: two organised groups per country with
strictly positive political weights whose politically weighted sums reproduce
the family's government payoffs `U_S`, `U_T` **at every state and action**
(`govS_eq`, `govT_eq`), so the government game — hence every constructed
equilibrium — is literally the economy's own, untouched. Three accounting
choices are built in and are the reader's "economic gate":

1. the direct state benefit `w·x`, the sanctioning cost `(q/2)s²` and the
   placation term `k·a·s` are kept at unit weight (common Sender resource
   terms), as is the Target's sanction cost `c·s`;
2. compliance is a pure transfer of size `κ·a` between the two Target groups,
   so it cancels in the unit-weight sum (this is what makes the two
   zero-sanction cells tie);
3. cardinal group benefits are unrestricted in size, compensated by the
   inverse political weight (the hawk-scaling mechanism of
   `FourGroupWelfareSign.lean`, made parametric).

The existing `FourGroup` structure is left untouched: it has no `w·x` term and
excludes the boundaries `r = 0`, `n = 0` that this family allows; a completion
covers both (`νT = 0` when `n = 0`).

WHAT IS PROVED.
* Unit-weight welfare is `W = K·x + η·s − (q/2)s² − k·a·s` with
  `K = w + (b_J − b_K)` and `η = g_H − Q − c` (`welfare_eq`), and the wedge
  between the governments' summed objectives and welfare is exactly the
  `(θ_g − 1)·w_g` sum (`govS_add_govT_eq`).
* Every member has a completion with any prescribed `η` and any `B > 0`
  (`exists_welfareCompletion`).
* **Family-wide non-identification** (`exists_completions_reversing_regime_ranking`):
  for every member of the four-cell domain there are two completions such that,
  at every start and every planner discount, the constructed regimes are ranked
  `11 > 10 > 00 = 01` by one and `00 = 01 > 10 > 11` by the other. The
  quantifier order is `∀ E, ∃ C₊ C₋, ∀ x₀ β`. Every path and action is the
  constructed equilibrium's own (Rule 1). Rule 9: an existence statement; it
  licenses "the government game does not identify the ranking", not any
  magnitude, and not a statement about planner optimality (a regime ranking is
  not an efficiency verdict).
* For a fixed completion the flow difference of two regime paths is the
  accounting identity `flow_sub_eq`.

The four constructed regimes are read at the member's chord economy
(`E.toChordCs`, round AV, 2026-09-25, doc 104); the completion itself stays on the
quadratic–linear family, where it represents the payoff (sign-off M5).

Rule 22: general in `F`. No affine rewrite is used anywhere.

Renovation item BH4.1 (2026-10-06): the forward-looking regime's flow `flow11` is indexed
by the rally margin, but the margin is read only to make the forward-looking response
nondecreasing. `flow11Of` and the `_of_response_monotone` theorems take that nondecreasing
response `hmono` in its place (at `equilibriumTop` and its path `dynamicPathOf`), and
`exists_completions_reversing_regime_ranking_of_response_monotone` is the
non-identification result on that wider domain. The margin forms keep their statements
and are corollaries at `hmono := responsePath_monotoneOn_of_margin hmargin`
(`flow11_eq_flow11Of` is `rfl`).

Renovation item BJ2.3 (2026-10-07): the family no longer carries the interiority and stage
relief fields, so the zero-sanction regimes' flows and facts take the member's interiority
`hInt : E.toChordCs.Interior` (and the myopic flow its stage relief margin `hSR`) as
hypotheses. The non-identification theorems take `hInt` as a new hypothesis and read the
stage relief margin from the sharp relief margin they already assume
(`stageRelief_of_reliefSharp`, BG3.2). The planner-efficient completion at the constructed
equilibrium reads no part of interiority: on its boundary `n = 0` the family's loss-offset
margin reaches the chord economy with no floor condition (`toChord_lossOffset_of_n_eq_zero`),
so those statements change only in that proof term. General in `F`.
-/
import Sanctions.Examples.PlacableSenderWedge
import Sanctions.Examples.PlacableSenderBoundaryMember
import Sanctions.Foundations.InfiniteHorizonVerification

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace PlacableEconomyF

variable (E : PlacableEconomyF)

/-- A positive-weight, two-groups-per-country completion of the government
payoffs of `E`. Target groups: a regime bloc valuing the state at `bJ` and an
opposition losing `bK`, with a compliance transfer `κ·a` between them; baseline
political weights `tJ`, `tK` and a common sanction slope `νT`. Sender groups:
hawks gaining `gH` per unit of sanction with state-dependent weight
`(u₀ + Q + r·x)/gH`, and a commercial lobby losing `Q` per unit at weight one.
The three `rep_` fields are equations among the structure's own data and the
economy's primitives (Rule 14: no opaque `Prop`). -/
structure WelfareCompletion where
  bJ : ℝ
  bK : ℝ
  κ : ℝ
  tJ : ℝ
  tK : ℝ
  νT : ℝ
  gH : ℝ
  Q : ℝ
  hbJ : 0 < bJ
  hbK : 0 < bK
  hκ : 0 < κ
  htJ : 0 < tJ
  htK : 0 < tK
  hνT : 0 ≤ νT
  hgH : 0 < gH
  hQ : 0 < Q
  rep_v : tJ * bJ - tK * bK = E.v
  rep_n : νT * (bJ - bK) = E.n
  rep_ℓ : κ * (tJ - tK) = E.ℓ

namespace WelfareCompletion

variable {E}
variable (C : E.WelfareCompletion)

/-- Political weight of the Sender's hawks. -/
def thetaJS (x : ℝ) : ℝ := (E.u₀ + C.Q + E.r * x) / C.gH

/-- Political weights of the two Target groups. -/
def thetaJT (s : ℝ) : ℝ := C.tJ + C.νT * s
def thetaKT (s : ℝ) : ℝ := C.tK + C.νT * s

theorem thetaJS_pos {x : ℝ} (hx : 0 ≤ x) : 0 < C.thetaJS x :=
  div_pos (by nlinarith [E.hu₀, C.hQ, E.hr, mul_nonneg E.hr hx]) C.hgH

theorem thetaJT_pos {s : ℝ} (hs : 0 ≤ s) : 0 < C.thetaJT s := by
  unfold thetaJT; nlinarith [C.htJ, mul_nonneg C.hνT hs]

theorem thetaKT_pos {s : ℝ} (hs : 0 ≤ s) : 0 < C.thetaKT s := by
  unfold thetaKT; nlinarith [C.htK, mul_nonneg C.hνT hs]

/-- The Sender government's politically weighted objective. -/
def govS (x a s : ℝ) : ℝ :=
  C.thetaJS x * (C.gH * s) + 1 * (-(C.Q * s))
    + (E.w * x - E.q / 2 * s ^ 2 - E.k * a * s)

/-- The Target government's politically weighted objective. -/
def govT (x a s : ℝ) : ℝ :=
  C.thetaJT s * (C.bJ * x - C.κ * a) + C.thetaKT s * (-(C.bK * x) + C.κ * a) - E.c * s

/-- **The completion represents the Sender's payoff exactly**, at every state and
action, on and off the equilibrium path. -/
theorem govS_eq (x a s : ℝ) : C.govS x a s = E.toParams.U_S x a s := by
  have hg : C.gH ≠ 0 := C.hgH.ne'
  rw [toParams_U_S]
  unfold govS thetaJS symU_S
  field_simp
  ring

/-- **The completion represents the Target's payoff exactly.** -/
theorem govT_eq (x a s : ℝ) : C.govT x a s = E.toParams.U_T x a s := by
  rw [toParams_U_T]
  unfold govT thetaJT thetaKT symU_T
  linear_combination x * C.rep_v + s * x * C.rep_n - a * C.rep_ℓ

/-- Unit-weight (utilitarian) welfare: every group at weight one, the common
resource terms kept. -/
def welfare (x a s : ℝ) : ℝ :=
  C.gH * s - C.Q * s + (E.w * x - E.q / 2 * s ^ 2 - E.k * a * s)
    + (C.bJ * x - C.κ * a) + (-(C.bK * x) + C.κ * a) - E.c * s

/-- The state coefficient of welfare, `w + (b_J − b_K)`. -/
def K : ℝ := E.w + (C.bJ - C.bK)

/-- The net social sanction coefficient, `g_H − Q − c`. -/
def η : ℝ := C.gH - C.Q - E.c

theorem welfare_eq (x a s : ℝ) :
    C.welfare x a s = C.K * x + C.η * s - E.q / 2 * s ^ 2 - E.k * a * s := by
  unfold welfare K η; ring

/-- At a zero sanction welfare does not depend on compliance. -/
theorem welfare_zero_sanction (x a : ℝ) : C.welfare x a 0 = C.K * x := by
  rw [welfare_eq]; ring

/-- **The political-weight wedge**: the governments' summed objectives equal
welfare plus the `(θ_g − 1)`-weighted group payoffs. -/
theorem govS_add_govT_eq (x a s : ℝ) :
    C.govS x a s + C.govT x a s = C.welfare x a s
      + (C.thetaJS x - 1) * (C.gH * s)
      + (C.thetaJT s - 1) * (C.bJ * x - C.κ * a)
      + (C.thetaKT s - 1) * (-(C.bK * x) + C.κ * a) := by
  unfold govS govT welfare; ring

/-- **Accounting identity for a fixed completion**: the flow difference between
two state–action–sanction triples. -/
theorem flow_sub_eq (x₁ a₁ s₁ x₂ a₂ s₂ : ℝ) :
    C.welfare x₂ a₂ s₂ - C.welfare x₁ a₁ s₁
      = C.K * (x₂ - x₁) + C.η * (s₂ - s₁) - E.q / 2 * (s₂ ^ 2 - s₁ ^ 2)
        - E.k * (a₂ * s₂ - a₁ * s₁) := by
  rw [welfare_eq, welfare_eq]; ring

end WelfareCompletion

/-- **Every member has a completion with any net sanction coefficient and any
positive state wedge.** The construction: `b_K = 1`, `b_J = 1 + B`,
`κ = 2ℓ·b_J/v`, `t_K = v/(2B)`, `t_J = t_K + ℓ/κ`, `ν_T = n/B`,
`Q = |c + η| + 1`, `g_H = Q + c + η`. Valid at `r = 0` and at `n = 0`. -/
theorem exists_welfareCompletion (η : ℝ) {B : ℝ} (hB : 0 < B) :
    ∃ C : E.WelfareCompletion, C.bJ - C.bK = B ∧ C.η = η := by
  have hv := E.hv
  have hℓ := E.hℓ
  have hbJ : (0 : ℝ) < 1 + B := by linarith
  have hκ : 0 < 2 * E.ℓ * (1 + B) / E.v := div_pos (by positivity) hv
  have hQ : 0 < |E.c + η| + 1 := by positivity
  have hg : 0 < |E.c + η| + 1 + E.c + η := by
    have := neg_abs_le (E.c + η)
    linarith
  refine ⟨{ bJ := 1 + B, bK := 1, κ := 2 * E.ℓ * (1 + B) / E.v,
            tJ := E.v / (2 * B) + E.ℓ / (2 * E.ℓ * (1 + B) / E.v),
            tK := E.v / (2 * B), νT := E.n / B,
            gH := |E.c + η| + 1 + E.c + η, Q := |E.c + η| + 1,
            hbJ := hbJ, hbK := one_pos, hκ := hκ,
            htJ := by positivity, htK := by positivity,
            hνT := div_nonneg E.hn hB.le, hgH := hg, hQ := hQ,
            rep_v := ?_, rep_n := ?_, rep_ℓ := ?_ }, by ring, ?_⟩
  · field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring
  · unfold WelfareCompletion.η
    ring

/-- **Equal Target valuations force `n = 0`.** With `b_J = b_K` the left side of
the representation equation `ν_T (b_J − b_K) = n` vanishes. -/
theorem WelfareCompletion.n_eq_zero_of_bJ_eq_bK {E : PlacableEconomyF}
    (C : E.WelfareCompletion) (h : C.bJ = C.bK) : E.n = 0 := by
  have hrep := C.rep_n
  rw [h, sub_self, mul_zero] at hrep
  exact hrep.symm

/-- **And `n = 0` suffices, at every net sanction coefficient.** The record:
`b_J = b_K = 1`, `t_K = 1`, `t_J = 1 + v`, `κ = ℓ/v`, `ν_T = 0`,
`Q = |c + η| + 1`, `g_H = Q + c + η`. Neither the transition nor the rally
slope `r` enters, so this is available off the flat boundary of
`exists_planner_efficient_completion` as well. -/
theorem exists_equalValuation_completion (hn : E.n = 0) (η : ℝ) :
    ∃ C : E.WelfareCompletion, C.bJ = C.bK ∧ C.η = η := by
  have hv := E.hv
  have hℓ := E.hℓ
  have hQ : 0 < |E.c + η| + 1 := by positivity
  have hg : 0 < |E.c + η| + 1 + E.c + η := by
    have := neg_abs_le (E.c + η)
    linarith
  refine ⟨{ bJ := 1, bK := 1, κ := E.ℓ / E.v, tJ := 1 + E.v, tK := 1, νT := 0,
            gH := |E.c + η| + 1 + E.c + η, Q := |E.c + η| + 1,
            hbJ := one_pos, hbK := one_pos, hκ := div_pos hℓ hv,
            htJ := by linarith, htK := one_pos, hνT := le_rfl, hgH := hg, hQ := hQ,
            rep_v := by ring, rep_n := by rw [hn]; ring, rep_ℓ := ?_ }, rfl, ?_⟩
  · have hv0 : E.v ≠ 0 := hv.ne'
    field_simp
    ring
  · unfold WelfareCompletion.η
    ring

/-- **Equal Target valuations are available exactly at the members without a
rally softening.** The manuscript's completion lemma once said "completions
with `b_J = b_K` exist as well" under an every-member quantifier; that is false
whenever `n > 0` (the reader's D2, 2026-09-21). -/
theorem exists_completion_bJ_eq_bK_iff :
    (∃ C : E.WelfareCompletion, C.bJ = C.bK) ↔ E.n = 0 :=
  ⟨fun ⟨C, h⟩ => C.n_eq_zero_of_bJ_eq_bK h,
    fun hn => let ⟨C, h, _⟩ := E.exists_equalValuation_completion hn 0; ⟨C, h⟩⟩

end PlacableEconomyF

/-! ## Discounted comparison of bounded flows -/

/-- A termwise strict inequality between bounded flows survives discounting, at
every discount factor in `[0,1)` (at `β = 0` only the date-zero term counts, and
it is strict). -/
theorem tsum_geometric_lt_of_forall_lt {β M : ℝ} (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    {f g : ℕ → ℝ} (hf : ∀ t, |f t| ≤ M) (hg : ∀ t, |g t| ≤ M) (hlt : ∀ t, f t < g t) :
    ∑' t : ℕ, β ^ t * f t < ∑' t : ℕ, β ^ t * g t := by
  have hsum : ∀ h : ℕ → ℝ, (∀ t, |h t| ≤ M) → Summable (fun t : ℕ => β ^ t * h t) := by
    intro h hh
    refine Summable.of_norm_bounded (g := fun t : ℕ => M * β ^ t)
      ((summable_geometric_of_lt_one hβ.1 hβ.2).mul_left _) ?_
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ.1, mul_comm]
    exact mul_le_mul_of_nonneg_right (hh t) (pow_nonneg hβ.1 t)
  refine Summable.tsum_lt_tsum (i := 0) (fun t => ?_) ?_ (hsum f hf) (hsum g hg)
  · exact mul_le_mul_of_nonneg_left (hlt t).le (pow_nonneg hβ.1 t)
  · simpa using hlt 0

namespace PlacableEconomyFcs

variable (E : PlacableEconomyFcs)

/-! The four regimes are read at the member's chord economy `E.toChordCs` (the
constructed equilibria are the chord economy's); the welfare completion is the
family's own (sign-off M5). The hypotheses are those of the four-cell theorem at
`E.toChordCs`; zero-sanction neutrality holds on the family and is supplied
internally. Since renovation item BJ2.3 (2026-10-07) interiority `hInt` and, for the
myopic regime, the stage relief margin `hSR` are hypotheses here, no longer fields of the
family. -/

/-- Welfare flows along the four constructed regimes: each is the completion's
welfare at the regime's own realised state, the equilibrium's own Target action
and its own realised sanction. The myopic regime's flow takes the member's interiority
`hInt` and stage relief margin `hSR` (renovation item BJ2.3: no longer fields of the
family). General in `F`. -/
def flow00 (hInt : E.toChordCs.Interior) (hSR : E.toChordCs.StageRelief)
    (hP : E.toChordCs.Placable) (C : E.toPlacableEconomyF.WelfareCompletion) (x₀ : ℝ)
    (t : ℕ) : ℝ :=
  C.welfare ((E.toChordCs.myopicPath hInt hSR hP) x₀ t)
    ((E.toChordCs.myopicEquilibriumTop hInt hSR hP).α
        ((E.toChordCs.myopicPath hInt hSR hP) x₀ t))
    (E.toChordCs.pM.dynamicEquilibriumRule (E.toChordCs.myopicEquilibriumTop hInt hSR hP)
      ((E.toChordCs.myopicPath hInt hSR hP) x₀ t))

/-- The Sender-only regime's welfare flow; it takes the member's interiority `hInt`
(renovation item BJ2.3: no longer a field of the family). General in `F`. -/
def flow01 (hInt : E.toChordCs.Interior) (hP : E.toChordCs.Placable)
    (hrelief : E.toChordCs.ℓhi * E.toChordCs.Mtot < E.toChordCs.klo * E.toChordCs.plo)
    (C : E.toPlacableEconomyF.WelfareCompletion) (x₀ : ℝ) (t : ℕ) : ℝ :=
  C.welfare ((E.toChordCs.senderOnlyPath' hInt hP) hrelief
      E.toPlacableEconomyF.toChord_zeroSanctionNeutral
      x₀ t)
    (((E.toChordCs.senderOnlyEquilibriumTop' hInt hP) hrelief
      E.toPlacableEconomyF.toChord_zeroSanctionNeutral).α
      ((E.toChordCs.senderOnlyPath' hInt hP) hrelief
          E.toPlacableEconomyF.toChord_zeroSanctionNeutral
        x₀ t))
    (E.toChordCs.pS.dynamicEquilibriumRule
      ((E.toChordCs.senderOnlyEquilibriumTop' hInt hP) hrelief
        E.toPlacableEconomyF.toChord_zeroSanctionNeutral)
      ((E.toChordCs.senderOnlyPath' hInt hP) hrelief
          E.toPlacableEconomyF.toChord_zeroSanctionNeutral
        x₀ t))

def flow10 (hTM : E.toChordCs.LossOffset) (C : E.toPlacableEconomyF.WelfareCompletion) (x₀ : ℝ)
    (t : ℕ) : ℝ :=
  C.welfare ((E.toChordCs.targetOnlyPath hTM) x₀ t)
    ((E.toChordCs.targetOnlyEquilibriumTop hTM).α ((E.toChordCs.targetOnlyPath hTM) x₀ t))
    (E.toChordCs.pT.dynamicEquilibriumRule (E.toChordCs.targetOnlyEquilibriumTop hTM)
      ((E.toChordCs.targetOnlyPath hTM) x₀ t))

/-- This is `flow11` with the rally margin replaced by a response `responsePath VSstar` that
is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`. General in `F`. -/
def flow11Of (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C : E.toPlacableEconomyF.WelfareCompletion) (x₀ : ℝ) (t : ℕ) : ℝ :=
  C.welfare ((E.toChordCs.dynamicPathOf hTM) hmono x₀ t)
    (((E.toChordCs.equilibriumTop hTM) hmono).α ((E.toChordCs.dynamicPathOf hTM) hmono
        x₀ t))
    (E.toChordCs.toParams.dynamicEquilibriumRule ((E.toChordCs.equilibriumTop hTM) hmono)
      ((E.toChordCs.dynamicPathOf hTM) hmono x₀ t))

def flow11 (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C : E.toPlacableEconomyF.WelfareCompletion) (x₀ : ℝ) (t : ℕ) : ℝ :=
  C.welfare ((E.toChordCs.dynamicPath hTM) hmargin x₀ t)
    (((E.toChordCs.equilibriumTop_of_margin hTM) hmargin).α ((E.toChordCs.dynamicPath hTM) hmargin
        x₀ t))
    (E.toChordCs.toParams.dynamicEquilibriumRule ((E.toChordCs.equilibriumTop_of_margin hTM)
        hmargin)
      ((E.toChordCs.dynamicPath hTM) hmargin x₀ t))

/-- The bridge (BH4.1): `flow11` is `flow11Of` at the nondecreasing
response that the rally margin gives. Definitional. General in `F`. -/
theorem flow11_eq_flow11Of (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C : E.toPlacableEconomyF.WelfareCompletion) (x₀ : ℝ) (t : ℕ) :
    (E.flow11 hTM) hmargin C x₀ t
      = (E.flow11Of hTM) (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C x₀ t := rfl

/-- Discounted regime welfare at planner discount `β`. -/
def regimeValue (β : ℝ) (f : ℕ → ℝ) : ℝ := ∑' t : ℕ, β ^ t * f t

variable {E}

/-- The myopic path stays feasible. Interiority `hInt` and the stage relief margin `hSR`
are hypotheses since renovation item BJ2.3 (they were fields of the family). General in
`F`. -/
theorem myopicPath_mem (hInt : E.toChordCs.Interior) (hSR : E.toChordCs.StageRelief)
    (hP : E.toChordCs.Placable) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    (E.toChordCs.myopicPath hInt hSR hP) x₀ t ∈ Sanctions.I :=
  E.toChordCs.toParams.rulePathF_mem_I
    (fun x hx => by
      rw [(E.toChordCs.myopicRule_eq_zero hInt hSR hP) hx]
      exact ⟨le_rfl, zero_le_one⟩)
    hx₀ t

theorem targetOnlyPath_mem (hTM : E.toChordCs.LossOffset) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    (t : ℕ) : (E.toChordCs.targetOnlyPath hTM) x₀ t ∈ Sanctions.I :=
  E.toChordCs.toParams.rulePathF_mem_I (fun _ hx => (E.toChordCs.targetOnlyRule_mem hTM) hx) hx₀ t

/-- This is `dynamicPath_mem` with the rally margin replaced by a response
`responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1,
2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`. General in `F`. -/
theorem dynamicPath_mem_of_response_monotone (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    (E.toChordCs.dynamicPathOf hTM) hmono x₀ t ∈ Sanctions.I :=
  E.toChordCs.toParams.rulePathF_mem_I
      ((E.toChordCs.dynamicRule_mem_of_response_monotone hTM) hmono) hx₀ t

/-- The rally-margin form of `dynamicPath_mem_of_response_monotone` (BH4.1). -/
theorem dynamicPath_mem (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    (E.toChordCs.dynamicPath hTM) hmargin x₀ t ∈ Sanctions.I :=
  dynamicPath_mem_of_response_monotone (E := E) hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) hx₀ t

/-- The zero-sanction path is dominated by the Target-only path. Interiority `hInt` and
the stage relief margin `hSR` are hypotheses since renovation item BJ2.3 (they were fields
of the family). General in `F`. -/
theorem myopicPath_le_targetOnlyPath (hInt : E.toChordCs.Interior)
    (hSR : E.toChordCs.StageRelief) (hTM : E.toChordCs.LossOffset) (hP : E.toChordCs.Placable)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    (E.toChordCs.myopicPath hInt hSR hP) x₀ t ≤ (E.toChordCs.targetOnlyPath hTM) x₀ t := by
  refine E.toChordCs.toParams.rulePathF_le_of_rule_le_and_upper_mono
    (fun x hx => by
      rw [(E.toChordCs.myopicRule_eq_zero hInt hSR hP) hx]
      exact ⟨le_rfl, zero_le_one⟩)
    (fun _ hx => (E.toChordCs.targetOnlyRule_mem hTM) hx)
    (E.toChordCs.targetOnlyRule_monotoneOn hTM) ?_ hx₀ t
  intro x hx
  change E.toChordCs.pM.dynamicEquilibriumRule (E.toChordCs.myopicEquilibriumTop
      hInt hSR hP) x
    ≤ E.toChordCs.pT.dynamicEquilibriumRule (E.toChordCs.targetOnlyEquilibriumTop hTM) x
  rw [(E.toChordCs.myopicRule_eq_zero hInt hSR hP) hx,
      (E.toChordCs.targetOnlyRule_eq_stage hTM) hx]
  exact (E.toChordCs.σ_mem x 0).1

/-- The myopic flow in closed form. `hInt` and `hSR` are hypotheses since renovation item
BJ2.3. General in `F`. -/
theorem flow00_eq (hInt : E.toChordCs.Interior) (hSR : E.toChordCs.StageRelief)
    (hP : E.toChordCs.Placable) (C : E.toPlacableEconomyF.WelfareCompletion)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    (E.flow00 hInt hSR hP) C x₀ t = C.K * (E.toChordCs.myopicPath hInt hSR hP) x₀ t := by
  unfold flow00
  rw [(E.toChordCs.myopicRule_eq_zero hInt hSR hP)
      (myopicPath_mem hInt hSR hP hx₀ t), C.welfare_zero_sanction]

/-- The Sender-only flow is the myopic flow, along the common zero-sanction path. `hInt`
is a hypothesis since renovation item BJ2.3; the myopic path's stage relief margin comes
from the sharp relief margin `hrelief` (`stageRelief_of_reliefSharp`, BG3.2). General in
`F`. -/
theorem flow01_eq (hInt : E.toChordCs.Interior) (hP : E.toChordCs.Placable)
    (hrelief : E.toChordCs.ℓhi * E.toChordCs.Mtot < E.toChordCs.klo * E.toChordCs.plo)
    (C : E.toPlacableEconomyF.WelfareCompletion) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    (E.flow01 hInt hP) hrelief C x₀ t = C.K * (E.toChordCs.myopicPath hInt
        (E.toChordCs.stageRelief_of_reliefSharp hrelief) hP) x₀ t := by
  unfold flow01
  have heq := E.toChordCs.myopicPath_eq_senderOnlyPath_of_reliefSharp hInt hP hrelief
    E.toPlacableEconomyF.toChord_zeroSanctionNeutral hx₀ t
  have hmem : (E.toChordCs.senderOnlyPath' hInt hP) hrelief
      E.toPlacableEconomyF.toChord_zeroSanctionNeutral x₀ t ∈ Sanctions.I := by
    rw [← heq]; exact myopicPath_mem hInt (E.toChordCs.stageRelief_of_reliefSharp hrelief) hP
      hx₀ t
  rw [(E.toChordCs.senderOnlyRule_eq_zero' hInt hP) hrelief _ hmem,
      C.welfare_zero_sanction, ← heq]

theorem flow10_eq (hTM : E.toChordCs.LossOffset) (C : E.toPlacableEconomyF.WelfareCompletion)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    (E.flow10 hTM) C x₀ t = C.K * (E.toChordCs.targetOnlyPath hTM) x₀ t
      + C.η * E.toChordCs.σ ((E.toChordCs.targetOnlyPath hTM) x₀ t) 0
      - E.q / 2 * E.toChordCs.σ ((E.toChordCs.targetOnlyPath hTM) x₀ t) 0 ^ 2 := by
  unfold flow10
  rw [(E.toChordCs.targetOnlyRule_eq_stage hTM) (targetOnlyPath_mem hTM hx₀ t), C.welfare_eq]
  have hα : (E.toChordCs.targetOnlyEquilibriumTop hTM).α ((E.toChordCs.targetOnlyPath hTM) x₀ t)
      = 0 := rfl
  rw [hα]; ring

/-- This is `flow11_eq` with the rally margin replaced by a response `responsePath VSstar`
that is nondecreasing on `[0, 1]` (`hmono`; renovation item BH4.1, 2026-10-06), read at
`equilibriumTop` and its path `dynamicPathOf`. General in `F`. -/
theorem flow11_eq_of_response_monotone (hTM : E.toChordCs.LossOffset)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (C : E.toPlacableEconomyF.WelfareCompletion) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    (E.flow11Of hTM) hmono C x₀ t = C.K * (E.toChordCs.dynamicPathOf hTM) hmono x₀ t
      + C.η * E.toChordCs.responsePath E.toChordCs.VSstar ((E.toChordCs.dynamicPathOf hTM) hmono x₀
          t)
      - E.q / 2 * E.toChordCs.responsePath E.toChordCs.VSstar
          ((E.toChordCs.dynamicPathOf hTM) hmono x₀ t) ^ 2 := by
  unfold flow11Of
  rw [(E.toChordCs.dynamicRule_eq_responsePath_of_response_monotone hTM) hmono
      (dynamicPath_mem_of_response_monotone hTM hmono hx₀ t),
    C.welfare_eq]
  have hα : ((E.toChordCs.equilibriumTop hTM) hmono).α
      ((E.toChordCs.dynamicPathOf hTM) hmono x₀ t) = 0 := rfl
  rw [hα]; ring

/-- The rally-margin form of `flow11_eq_of_response_monotone` (BH4.1). -/
theorem flow11_eq (hTM : E.toChordCs.LossOffset)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (C : E.toPlacableEconomyF.WelfareCompletion) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    (E.flow11 hTM) hmargin C x₀ t = C.K * (E.toChordCs.dynamicPath hTM) hmargin x₀ t
      + C.η * E.toChordCs.responsePath E.toChordCs.VSstar ((E.toChordCs.dynamicPath hTM) hmargin x₀
          t)
      - E.q / 2 * E.toChordCs.responsePath E.toChordCs.VSstar
          ((E.toChordCs.dynamicPath hTM) hmargin x₀ t) ^ 2 :=
  flow11_eq_of_response_monotone (E := E) hTM
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) C hx₀ t

/-- **Family-wide non-identification of the four-regime welfare ranking.** For
every member of the four-cell domain there are two welfare completions — same
government payoffs at every state and action, hence the same four constructed
equilibria — such that, for every feasible start and every planner discount in
`[0,1)`, one ranks the regimes `11 > 10 > 00 = 01` and the other
`00 = 01 > 10 > 11`.
This is `exists_completions_reversing_regime_ranking` with the rally margin replaced by a
response `responsePath VSstar` that is nondecreasing on `[0, 1]` (`hmono`; renovation item
BH4.1, 2026-10-06), read at `equilibriumTop` and its path `dynamicPathOf`. General in `F`.
Renovation item BJ2.3 (2026-10-07): the member's interiority `hInt` is a hypothesis (it was
a field of the family); the myopic regime's stage relief margin, also no longer a field,
comes from the sharp relief margin `hrelief` (`stageRelief_of_reliefSharp`, BG3.2). -/
theorem exists_completions_reversing_regime_ranking_of_response_monotone
    (hInt : E.toChordCs.Interior) (hTM : E.toChordCs.LossOffset) (hP : E.toChordCs.Placable)
    (hmono : MonotoneOn (E.toChordCs.responsePath E.toChordCs.VSstar) (Icc (0 : ℝ) 1))
    (hrelief : E.toChordCs.ℓhi * E.toChordCs.Mtot < E.toChordCs.klo * E.toChordCs.plo) :
    ∃ Cp Cm : E.toPlacableEconomyF.WelfareCompletion,
      ∀ x₀ ∈ Sanctions.I, ∀ β ∈ Set.Ico (0 : ℝ) 1,
        (regimeValue β ((E.flow10 hTM) Cp x₀) < regimeValue β ((E.flow11Of hTM) hmono Cp x₀)
          ∧ regimeValue β
              ((E.flow00 hInt (E.toChordCs.stageRelief_of_reliefSharp hrelief) hP) Cp x₀)
            < regimeValue β ((E.flow10 hTM) Cp x₀)
          ∧ regimeValue β
              ((E.flow00 hInt (E.toChordCs.stageRelief_of_reliefSharp hrelief) hP) Cp x₀)
            = regimeValue β ((E.flow01 hInt hP) hrelief Cp x₀))
        ∧ (regimeValue β ((E.flow11Of hTM) hmono Cm x₀) < regimeValue β ((E.flow10 hTM) Cm x₀)
          ∧ regimeValue β ((E.flow10 hTM) Cm x₀)
            < regimeValue β
              ((E.flow00 hInt (E.toChordCs.stageRelief_of_reliefSharp hrelief) hP) Cm x₀)
          ∧ regimeValue β
              ((E.flow00 hInt (E.toChordCs.stageRelief_of_reliefSharp hrelief) hP) Cm x₀)
            = regimeValue β ((E.flow01 hInt hP) hrelief Cm x₀)) := by
  have hSR : E.toChordCs.StageRelief := E.toChordCs.stageRelief_of_reliefSharp hrelief
  -- the two floors: the sanction floor b = σ(0,0) and the foresight wedge m
  set b := E.toChordCs.sfloor with hb
  have hb0 : 0 < b := E.toChordCs.sfloor_pos
  have hm0 : 0 < E.toChordCs.wedge := E.toChordCs.wedge_pos
  set μ := min b E.toChordCs.wedge with hμ
  have hμ0 : 0 < μ := lt_min hb0 hm0
  have hμb : μ ≤ b := min_le_left _ _
  have hμm : μ ≤ E.toChordCs.wedge := min_le_right _ _
  obtain ⟨Cp, hCpB, hCpη⟩ := E.toPlacableEconomyF.exists_welfareCompletion (E.q + 1) one_pos
  obtain ⟨Cm, hCmB, hCmη⟩ :=
    E.toPlacableEconomyF.exists_welfareCompletion (-((E.w + 1) / μ) - 1) one_pos
  have hKp : Cp.K = E.w + 1 := by unfold PlacableEconomyF.WelfareCompletion.K; rw [hCpB]
  have hKm : Cm.K = E.w + 1 := by unfold PlacableEconomyF.WelfareCompletion.K; rw [hCmB]
  have hK0 : 0 < E.w + 1 := by linarith [E.hw]
  refine ⟨Cp, Cm, fun x₀ hx₀ β hβ => ?_⟩
  -- path facts
  have hy := fun t => myopicPath_mem (E := E) hInt hSR hP hx₀ t
  have h10 := fun t => targetOnlyPath_mem (E := E) hTM hx₀ t
  have h11 := fun t => dynamicPath_mem_of_response_monotone (E := E) hTM hmono hx₀ t
  have hy10 := fun t => myopicPath_le_targetOnlyPath (E := E) hInt hSR hTM hP hx₀ t
  have h1011 := fun t => (E.toChordCs.targetOnlyPath_le_dynamicPath_of_response_monotone
      hInt hTM) hmono hx₀ t
  -- sanction facts
  have hs10b : ∀ t, b ≤ E.toChordCs.σ ((E.toChordCs.targetOnlyPath hTM) x₀ t) 0 :=
    fun t => E.toChordCs.sfloor_le (h10 t)
  have hs10mem : ∀ t, E.toChordCs.σ ((E.toChordCs.targetOnlyPath hTM) x₀ t) 0 ∈ Sanctions.I :=
    fun t => E.toChordCs.σ_mem _ 0
  have hs11mem : ∀ t, E.toChordCs.responsePath E.toChordCs.VSstar
      ((E.toChordCs.dynamicPathOf hTM) hmono x₀ t) ∈ Sanctions.I :=
    fun t => E.toChordCs.responsePath_mem _ _
  have hgap : ∀ t, E.toChordCs.σ ((E.toChordCs.targetOnlyPath hTM) x₀ t) 0 + E.toChordCs.wedge
      ≤ E.toChordCs.responsePath E.toChordCs.VSstar ((E.toChordCs.dynamicPathOf hTM) hmono x₀ t) :=
          by
    intro t
    have h := E.toChordCs.targetOnlySanction_add_wedge_le_dynamicSanction_of_response_monotone
        hInt hTM hmono hx₀ t
    rwa [(E.toChordCs.targetOnlyRule_eq_stage hTM) (h10 t),
      (E.toChordCs.dynamicRule_eq_responsePath_of_response_monotone hTM) hmono (h11 t)] at h
  -- a common bound on every flow
  have hbound : ∀ (C : E.toPlacableEconomyF.WelfareCompletion) (x s : ℝ),
      x ∈ Sanctions.I → s ∈ Sanctions.I →
      |C.K * x + C.η * s - E.q / 2 * s ^ 2| ≤ |C.K| + |C.η| + E.q / 2 := by
    intro C x s hx hs
    have h1 : |C.K * x| ≤ |C.K| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _)
        (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)
    have h2 : |C.η * s| ≤ |C.η| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _)
        (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩)
    have h3 : |E.q / 2 * s ^ 2| ≤ E.q / 2 := by
      rw [abs_of_nonneg (by have := E.hq; positivity)]
      have : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
      nlinarith [E.hq]
    calc |C.K * x + C.η * s - E.q / 2 * s ^ 2|
        ≤ |C.K * x + C.η * s| + |E.q / 2 * s ^ 2| := abs_sub _ _
      _ ≤ |C.K * x| + |C.η * s| + |E.q / 2 * s ^ 2| := by
          linarith [abs_add_le (C.K * x) (C.η * s)]
      _ ≤ |C.K| + |C.η| + E.q / 2 := by linarith
  have hB00 : ∀ (C : E.toPlacableEconomyF.WelfareCompletion) t,
      |(E.flow00 hInt hSR hP) C x₀ t| ≤ |C.K| + |C.η| + E.q / 2 := by
    intro C t
    rw [flow00_eq hInt hSR hP C hx₀ t]
    have := hbound C ((E.toChordCs.myopicPath hInt hSR hP) x₀ t) 0 (hy t) ⟨le_rfl, zero_le_one⟩
    simpa using this
  have hB10 : ∀ (C : E.toPlacableEconomyF.WelfareCompletion) t,
      |(E.flow10 hTM) C x₀ t| ≤ |C.K| + |C.η| + E.q / 2 := by
    intro C t
    rw [flow10_eq hTM C hx₀ t]
    exact hbound C _ _ (h10 t) (hs10mem t)
  have hB11 : ∀ (C : E.toPlacableEconomyF.WelfareCompletion) t,
      |(E.flow11Of hTM) hmono C x₀ t| ≤ |C.K| + |C.η| + E.q / 2 := by
    intro C t
    rw [flow11_eq_of_response_monotone hTM hmono C hx₀ t]
    exact hbound C _ _ (h11 t) (hs11mem t)
  have h0001 : ∀ (C : E.toPlacableEconomyF.WelfareCompletion),
      regimeValue β ((E.flow00 hInt hSR hP) C x₀)
        = regimeValue β ((E.flow01 hInt hP) hrelief C x₀) := by
    intro C
    unfold regimeValue
    congr 1
    funext t
    rw [flow00_eq hInt hSR hP C hx₀ t, flow01_eq hInt hP hrelief C hx₀ t]
  -- the four flow comparisons, as inequalities among reals
  have hplus : ∀ {K y x s₀ s₁ : ℝ}, 0 ≤ K → y ≤ x → 0 ≤ s₀ → s₀ < s₁ → s₁ ≤ 1 →
      K * y + (E.q + 1) * s₀ - E.q / 2 * s₀ ^ 2
        < K * x + (E.q + 1) * s₁ - E.q / 2 * s₁ ^ 2 := by
    intro K y x s₀ s₁ hK hyx hs₀ hlt hs₁
    have hd : 0 < s₁ - s₀ := by linarith
    have hsum : s₁ + s₀ ≤ 2 := by linarith
    have hprod : E.q / 2 * ((s₁ - s₀) * (s₁ + s₀)) ≤ E.q / 2 * ((s₁ - s₀) * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hd.le)
        (by have := E.hq; positivity)
    have hKx : 0 ≤ K * (x - y) := mul_nonneg hK (by linarith)
    nlinarith [hprod, hKx, hd]
  have hminus : ∀ {K c₀ y x s₀ s₁ : ℝ}, 0 ≤ K → x - y ≤ 1 → 0 ≤ c₀ → K ≤ c₀ * (s₁ - s₀) →
      0 ≤ s₀ → s₀ < s₁ →
      K * x + (-c₀ - 1) * s₁ - E.q / 2 * s₁ ^ 2
        < K * y + (-c₀ - 1) * s₀ - E.q / 2 * s₀ ^ 2 := by
    intro K c₀ y x s₀ s₁ hK hxy hc₀ hKc hs₀ hlt
    have hd : 0 < s₁ - s₀ := by linarith
    have hsq : 0 ≤ E.q / 2 * ((s₁ - s₀) * (s₁ + s₀)) :=
      mul_nonneg (by have := E.hq; positivity) (mul_nonneg hd.le (by linarith))
    have hKx : K * (x - y) ≤ K * 1 := mul_le_mul_of_nonneg_left hxy hK
    nlinarith [hsq, hKx, hKc, hd]
  set c₀ := (E.w + 1) / μ with hc₀
  have hc₀0 : 0 ≤ c₀ := div_nonneg hK0.le hμ0.le
  have hc₀μ : c₀ * μ = E.w + 1 := div_mul_cancel₀ _ hμ0.ne'
  refine ⟨⟨?_, ?_, h0001 Cp⟩, ⟨?_, ?_, h0001 Cm⟩⟩
  · -- (+) 11 above 10
    refine tsum_geometric_lt_of_forall_lt hβ (hB10 Cp) (hB11 Cp) (fun t => ?_)
    rw [flow10_eq hTM Cp hx₀ t, flow11_eq_of_response_monotone hTM hmono Cp hx₀ t, hKp, hCpη]
    exact hplus hK0.le (h1011 t) (hs10mem t).1 (by linarith [hgap t]) (hs11mem t).2
  · -- (+) 10 above 00
    refine tsum_geometric_lt_of_forall_lt hβ (hB00 Cp) (hB10 Cp) (fun t => ?_)
    rw [flow00_eq hInt hSR hP Cp hx₀ t, flow10_eq hTM Cp hx₀ t, hKp, hCpη]
    have h := hplus (K := E.w + 1) (y := (E.toChordCs.myopicPath hInt hSR hP) x₀ t)
      (x := (E.toChordCs.targetOnlyPath hTM) x₀ t)
      (s₀ := 0) (s₁ := E.toChordCs.σ ((E.toChordCs.targetOnlyPath hTM) x₀ t) 0) hK0.le (hy10 t)
      le_rfl (by linarith [hs10b t]) (hs10mem t).2
    simpa using h
  · -- (−) 10 above 11
    refine tsum_geometric_lt_of_forall_lt hβ (hB11 Cm) (hB10 Cm) (fun t => ?_)
    rw [flow10_eq hTM Cm hx₀ t, flow11_eq_of_response_monotone hTM hmono Cm hx₀ t, hKm, hCmη]
    refine hminus hK0.le (by linarith [(h11 t).2, (h10 t).1]) hc₀0 ?_
      (hs10mem t).1 (by linarith [hgap t])
    calc E.w + 1 = c₀ * μ := hc₀μ.symm
      _ ≤ c₀ * (E.toChordCs.responsePath E.toChordCs.VSstar
              ((E.toChordCs.dynamicPathOf hTM) hmono x₀ t)
            - E.toChordCs.σ ((E.toChordCs.targetOnlyPath hTM) x₀ t) 0) :=
          mul_le_mul_of_nonneg_left (by linarith [hgap t]) hc₀0
  · -- (−) 00 above 10
    refine tsum_geometric_lt_of_forall_lt hβ (hB10 Cm) (hB00 Cm) (fun t => ?_)
    rw [flow00_eq hInt hSR hP Cm hx₀ t, flow10_eq hTM Cm hx₀ t, hKm, hCmη]
    have h := hminus (K := E.w + 1) (c₀ := c₀) (y := (E.toChordCs.myopicPath hInt hSR hP) x₀ t)
      (x := (E.toChordCs.targetOnlyPath hTM) x₀ t) (s₀ := 0)
      (s₁ := E.toChordCs.σ ((E.toChordCs.targetOnlyPath hTM) x₀ t) 0)
      hK0.le (by linarith [(h10 t).2, (hy t).1]) hc₀0
      (by
        calc E.w + 1 = c₀ * μ := hc₀μ.symm
          _ ≤ c₀ * (E.toChordCs.σ ((E.toChordCs.targetOnlyPath hTM) x₀ t) 0 - 0) :=
              mul_le_mul_of_nonneg_left (by linarith [hs10b t]) hc₀0)
      le_rfl (by linarith [hs10b t])
    simpa using h

/-- **Family-wide non-identification of the four-regime welfare ranking.** For
every member of the four-cell domain there are two welfare completions — same
government payoffs at every state and action, hence the same four constructed
equilibria — such that, for every feasible start and every planner discount in
`[0,1)`, one ranks the regimes `11 > 10 > 00 = 01` and the other
`00 = 01 > 10 > 11`.
The rally-margin form of
`exists_completions_reversing_regime_ranking_of_response_monotone` (BH4.1). A pinned
headline; renovation item BJ2.3 (2026-10-07, user-approved re-pin): the member's
interiority `hInt` is a new hypothesis (it was a field of the family), and the myopic
regime's stage relief margin, also no longer a field, comes from `hrelief`
(`stageRelief_of_reliefSharp`, BG3.2). General in `F`. -/
theorem exists_completions_reversing_regime_ranking (hInt : E.toChordCs.Interior)
    (hTM : E.toChordCs.LossOffset) (hP : E.toChordCs.Placable)
    (hmargin : E.toChordCs.β_S * (E.toChordCs.SigC * E.toChordCs.ghi * E.toChordCs.dhi
      + (E.toChordCs.KS + 2 * E.toChordCs.SigC) * E.toChordCs.Mmix) ≤ E.toChordCs.rlo)
    (hrelief : E.toChordCs.ℓhi * E.toChordCs.Mtot < E.toChordCs.klo * E.toChordCs.plo) :
    ∃ Cp Cm : E.toPlacableEconomyF.WelfareCompletion,
      ∀ x₀ ∈ Sanctions.I, ∀ β ∈ Set.Ico (0 : ℝ) 1,
        (regimeValue β ((E.flow10 hTM) Cp x₀) < regimeValue β ((E.flow11 hTM) hmargin Cp x₀)
          ∧ regimeValue β
              ((E.flow00 hInt (E.toChordCs.stageRelief_of_reliefSharp hrelief) hP) Cp x₀)
            < regimeValue β ((E.flow10 hTM) Cp x₀)
          ∧ regimeValue β
              ((E.flow00 hInt (E.toChordCs.stageRelief_of_reliefSharp hrelief) hP) Cp x₀)
            = regimeValue β ((E.flow01 hInt hP) hrelief Cp x₀))
        ∧ (regimeValue β ((E.flow11 hTM) hmargin Cm x₀) < regimeValue β ((E.flow10 hTM) Cm x₀)
          ∧ regimeValue β ((E.flow10 hTM) Cm x₀)
            < regimeValue β
              ((E.flow00 hInt (E.toChordCs.stageRelief_of_reliefSharp hrelief) hP) Cm x₀)
          ∧ regimeValue β
              ((E.flow00 hInt (E.toChordCs.stageRelief_of_reliefSharp hrelief) hP) Cm x₀)
            = regimeValue β ((E.flow01 hInt hP) hrelief Cm x₀)) :=
  exists_completions_reversing_regime_ranking_of_response_monotone (E := E) hInt hTM hP
    (E.toChordCs.responsePath_monotoneOn_of_margin hmargin) hrelief

end PlacableEconomyFcs

/-! ## A planner-efficient completion on the boundary `r = n = 0` (node W5)

A Rule 11 boundary for any future "strictly inefficient under every completion"
sentence. On the family's boundary `r = 0`, `n = 0` there is a positive-weight
completion whose unit-weight welfare **is** the Sender's stage payoff; at the
planner discount `β_P = β_S` the Sender's constructed value is then a Bellman
supersolution of the planner's problem over *both* actions (compliance only
lowers `U_S`), with equality at the equilibrium's own play, and the Foundations
verification theorem makes that play optimal against every time-dependent plan.
One completion, one discount: it refutes a universal strict-loss claim and
nothing more; efficiency at other discounts is not asserted. The constructed
values are the member's chord economy's (`E.toChord`). -/

namespace ChordEconomy

variable (E : ChordEconomy)

/-- The Sender's constructed value is the supremum of its dynamic objective at
defiance, state by state (the fixed-point identity, unfolded). General in the
chord economy (round AV). -/
theorem VSstar_apply_eq_sSup (y : ↥(Sanctions.S : Set ℝ)) :
    E.VSstar y = sSup ((fun s => E.senderObj E.VSstar y.1 0 s) '' Sanctions.I) := by
  have h := congrArg (fun V : Val => V y) E.VSstar_fix
  simp only at h
  rw [← h]
  rfl

theorem senderObj_bddAbove (y : ↥(Sanctions.S : Set ℝ)) :
    BddAbove ((fun s => E.senderObj E.VSstar y.1 0 s) '' Sanctions.I) := by
  have hcont : Continuous (fun s => E.senderObj E.VSstar y.1 0 s) :=
    E.toParams.integrandS_at_continuous (α := fun _ => 0) continuous_const
      (V := fun z => E.VSstar z) E.VSstar.continuous y.1
  exact (isCompact_Icc.image hcont).bddAbove

/-- Bellman inequality of the Sender's value, at every feasible sanction. -/
theorem senderObj_le_VSstar (y : ↥(Sanctions.S : Set ℝ)) {s : ℝ} (hs : s ∈ Sanctions.I) :
    E.senderObj E.VSstar y.1 0 s ≤ E.VSstar y := by
  rw [E.VSstar_apply_eq_sSup y]
  exact le_csSup (E.senderObj_bddAbove y) ⟨s, hs, rfl⟩

/-- Bellman equality at the realised response. -/
theorem senderObj_responsePath_eq_VSstar (y : ↥(Sanctions.S : Set ℝ)) :
    E.senderObj E.VSstar y.1 0 (E.responsePath E.VSstar y.1) = E.VSstar y := by
  rw [E.VSstar_apply_eq_sSup y]
  refine le_antisymm (le_csSup (E.senderObj_bddAbove y)
    ⟨_, E.responsePath_mem _ _, rfl⟩) (csSup_le ⟨_, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩ ?_)
  rintro _ ⟨s, hs, rfl⟩
  exact E.response_isMaxOn E.VSstar y.1 0 hs

end ChordEconomy

namespace PlacableEconomyF

variable (E : PlacableEconomyF)

/-- The planner's state transition and flow on the cube, for a completion. -/
def plannerStep (x : ↥(Sanctions.S : Set ℝ))
    (p : ↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)) : ↥(Sanctions.S : Set ℝ) :=
  Sanctions.clipS' (E.F x.1 p.2.1)

def plannerStage (C : E.WelfareCompletion) (x : ↥(Sanctions.S : Set ℝ))
    (p : ↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)) : ℝ :=
  C.welfare x.1 p.1.1 p.2.1

/-- The constructed forward-looking equilibrium's own play, as a stationary plan:
defiance and the realised response. -/
def equilibriumPlan (x : ↥(Sanctions.S : Set ℝ)) :
    ↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ) :=
  (⟨0, le_rfl, zero_le_one⟩,
    ⟨E.toChord.responsePath E.toChord.VSstar x.1, E.toChord.responsePath_mem _ _⟩)

/-- **A planner-efficient completion on the boundary.** If `r = 0` and `n = 0`
there is a positive-weight completion whose welfare is the Sender's stage
payoff at every state and action, and at planner discount `β_S` the
equilibrium's play (defiance, the realised response) is optimal against every
time-dependent plan over both actions, from every feasible start. -/
theorem exists_planner_efficient_completion (hr : E.r = 0) (hn : E.n = 0) :
    ∃ C : E.WelfareCompletion,
      (∀ x a s, C.welfare x a s = E.toParams.U_S x a s) ∧
      ∀ (π : InfiniteHorizonVerification.MarkovPlan ↥(Sanctions.S : Set ℝ)
            (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
        (x₀ : ↥(Sanctions.S : Set ℝ)),
        InfiniteHorizonVerification.discountedPayoff (E.plannerStage C) E.plannerStep E.βS π x₀
          ≤ InfiniteHorizonVerification.discountedPayoff (E.plannerStage C) E.plannerStep E.βS
              (InfiniteHorizonVerification.stationaryPlan E.equilibriumPlan) x₀ := by
  have hv := E.hv
  have hℓ := E.hℓ
  have hc := E.toChord.c_pos
  change 0 < E.c at hc
  -- equal state magnitudes (B = 0), weights 1 + v and 1, compliance transfer ℓ/v
  let C : E.WelfareCompletion :=
    { bJ := 1, bK := 1, κ := E.ℓ / E.v, tJ := 1 + E.v, tK := 1, νT := 0,
      gH := 1 + E.c + E.u₀, Q := 1,
      hbJ := one_pos, hbK := one_pos, hκ := div_pos hℓ hv,
      htJ := by linarith, htK := one_pos, hνT := le_rfl,
      hgH := by linarith [E.hu₀], hQ := one_pos,
      rep_v := by ring, rep_n := by rw [hn]; ring,
      rep_ℓ := by
        have hv0 : E.v ≠ 0 := hv.ne'
        field_simp
        ring }
  have hW : ∀ x a s, C.welfare x a s = E.toParams.U_S x a s := by
    intro x a s
    rw [C.welfare_eq, toParams_U_S]
    simp only [WelfareCompletion.K, WelfareCompletion.η, symU_S, hr, C]
    ring
  refine ⟨C, hW, fun π x₀ => ?_⟩
  have hβ0 : 0 ≤ E.βS := E.hβS0.le
  refine InfiniteHorizonVerification.stationary_optimal_against_markov_deviation_of_global_bounds
    (E.plannerStage C) E.plannerStep E.βS (fun x => E.toChord.VSstar x) E.equilibriumPlan
    hβ0 E.hβS1 ?_ ?_ (E.q / 2 + E.u₀ + E.k + E.w) E.toChord.MS ?_ ?_ π x₀
  · -- Bellman inequality over both actions
    intro x p
    have hle : E.toParams.U_S x.1 p.1.1 p.2.1 ≤ E.toParams.U_S x.1 0 p.2.1 := by
      rw [toParams_U_S]; unfold symU_S
      nlinarith [mul_nonneg (mul_nonneg E.k_pos.le p.1.2.1) p.2.2.1]
    have h : E.toParams.U_S x.1 0 p.2.1 + E.βS * E.toChord.VSstar (Sanctions.clipS' (E.F x.1 p.2.1))
        ≤ E.toChord.VSstar x := E.toChord.senderObj_le_VSstar x p.2.2
    change C.welfare x.1 p.1.1 p.2.1 + E.βS * E.toChord.VSstar (Sanctions.clipS' (E.F x.1 p.2.1))
      ≤ _
    rw [hW]
    linarith
  · -- equality at the equilibrium's play
    intro x
    have h : E.toParams.U_S x.1 0 (E.toChord.responsePath E.toChord.VSstar x.1)
        + E.βS * E.toChord.VSstar
            (Sanctions.clipS' (E.F x.1 (E.toChord.responsePath E.toChord.VSstar x.1)))
        = E.toChord.VSstar x := E.toChord.senderObj_responsePath_eq_VSstar x
    change C.welfare x.1 0 (E.toChord.responsePath E.toChord.VSstar x.1)
      + E.βS * E.toChord.VSstar
          (Sanctions.clipS' (E.F x.1 (E.toChord.responsePath E.toChord.VSstar x.1))) = _
    rw [hW]
    exact h
  · -- flow bound
    intro x p
    change |C.welfare x.1 p.1.1 p.2.1| ≤ _
    rw [hW, toParams_U_S]; unfold symU_S
    rw [hr]
    have hx := x.2; have ha := p.1.2; have hs := p.2.2
    have hs2 : p.2.1 ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    have has : p.1.1 * p.2.1 ≤ 1 := by nlinarith [ha.1, ha.2, hs.1, hs.2]
    have has0 : 0 ≤ p.1.1 * p.2.1 := mul_nonneg ha.1 hs.1
    rw [abs_le]
    constructor
    · nlinarith [E.hq, E.hu₀, E.k_pos, E.hw, hx.1, hs.1, mul_nonneg E.hu₀.le hs.1,
        mul_nonneg E.hw.le hx.1, mul_le_mul_of_nonneg_left hs2 (half_pos E.hq).le,
        mul_le_mul_of_nonneg_left has E.k_pos.le]
    · nlinarith [E.hq, E.hu₀, E.k_pos, E.hw, hx.2, hs.2, mul_le_mul_of_nonneg_left hs.2 E.hu₀.le,
        mul_le_mul_of_nonneg_left hx.2 E.hw.le, mul_nonneg (half_pos E.hq).le (sq_nonneg p.2.1),
        mul_nonneg E.k_pos.le has0]
  · -- value bound, from carrier membership
    intro x
    exact (E.toChord.VSstar.norm_coe_le_norm x).trans E.toChord.VSstar_mem.1.1

/-! ### The boundary clause at the constructed equilibrium (round AE, doc 94 T1)

`exists_planner_efficient_completion` compares every dated plan with the plan
*named* `equilibriumPlan` — defiance and the Sender's constructed response — and
takes only `r = 0`, `n = 0`. That the named plan is the play of a government
equilibrium is a separate fact, supplied by `equilibriumTop_of_margin`. The
bridge below states the two together (the outside reader's scope finding,
2026-09-20). On this boundary the rally margin is restrictive: with `r = 0` it
reads `β_S·(Σ_C·g_hi·d_hi + (K_S + 2Σ_C)·M_mix) ≤ 0`, every term is nonnegative
and `β_S, K_S, d_hi > 0`, so it forces the mixed-curvature bound `M_mix` to
vanish and either the state-section curvature bound `M_cx` or the upper state
chord `g_hi` to vanish (`flat_of_margin_of_r_eq_zero`). The boundary clause is
therefore a statement about **flat transitions** — the affine law, every
additively separable transition with convex state sections
(`familyMargin_of_flat`) — and the paper says so.

Renovation item BH3.4 (2026-10-06): the flatness belongs to this existence route, not
to the boundary clause itself. At every full-defiance equilibrium the clause holds with
neither the loss-offset margin nor the rally margin
(`exists_planner_efficient_completion_of_policy_zero`, in
`PlacableSenderDefianceEquilibriaWelfare.lean`), and
`exists_planner_efficient_completion_at_equilibrium` is re-derived from it there. -/

/-- **At `r = 0` the rally margin forces a flat transition certificate**: no
mixed curvature, and either no state-section curvature or no state dependence
in the upper chord. -/
theorem flat_of_margin_of_r_eq_zero (hr : E.r = 0)
    (hmargin : E.βS * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.r) :
    E.Mmix = 0 ∧ (E.Mcx = 0 ∨ E.ghi = 0) := by
  rw [hr] at hmargin
  have hdhi : 0 < E.dhi := lt_of_lt_of_le E.hdlo0 E.hdlo_dhi
  have hA : 0 ≤ E.SigC * E.ghi * E.dhi :=
    mul_nonneg (mul_nonneg E.SigC_nonneg E.ghi_nonneg) hdhi.le
  have hK : 0 < E.KS + 2 * E.SigC := by linarith [E.KS_pos, E.SigC_nonneg]
  have hB : 0 ≤ (E.KS + 2 * E.SigC) * E.Mmix := mul_nonneg hK.le E.hMmix0
  have hsum : E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix ≤ 0 := by
    by_contra hpos
    have := mul_pos E.hβS0 (not_le.mp hpos)
    linarith
  have hB0 : (E.KS + 2 * E.SigC) * E.Mmix = 0 := le_antisymm (by linarith) hB
  have hA0 : E.SigC * E.ghi * E.dhi = 0 := le_antisymm (by linarith) hA
  refine ⟨(mul_eq_zero.mp hB0).resolve_left hK.ne', ?_⟩
  have hSg : E.SigC * E.ghi = 0 := (mul_eq_zero.mp hA0).resolve_right hdhi.ne'
  rcases mul_eq_zero.mp hSg with hS | hg
  · left
    have hden : 0 < 1 - E.βS * E.ghi ^ 2 := by
      have := E.βS_ghi_lt_one
      have h1 := E.hghi1
      have h0 := E.ghi_nonneg
      have : E.βS * E.ghi ^ 2 ≤ E.βS * E.ghi := by
        have : E.ghi ^ 2 ≤ E.ghi := by nlinarith
        exact mul_le_mul_of_nonneg_left this E.hβS0.le
      linarith
    unfold SigC plSigC at hS
    rw [div_eq_zero_iff] at hS
    rcases hS with hnum | hden0
    · have hβK : E.βS * E.KS ≠ 0 := (mul_pos E.hβS0 E.KS_pos).ne'
      exact (mul_eq_zero.mp hnum).resolve_left hβK
    · exact absurd hden0 hden.ne'
  · exact Or.inr hg

/-- **The planner-efficient completion at the constructed forward-looking
equilibrium.** On the boundary `r = n = 0`, under the rally margin, there is a
positive-weight completion whose welfare is the Sender's stage payoff; the plan
`equilibriumPlan` **is** the play of the constructed equilibrium
`equilibriumTop_of_margin` — its Target policy and its realised sanction rule, at
every feasible state — and at planner discount `β_S` that play is optimal
against every time-dependent plan over both actions, from every feasible
start. The form at every full-defiance equilibrium, with neither the loss-offset
margin nor the rally margin, is `exists_planner_efficient_completion_of_policy_zero`
(renovation item BH3.4). Renovation item BJ2.3 (2026-10-07): the family's interiority
field is gone and this statement reads no part of it. The family's loss-offset margin
reaches the chord economy through `toChord_lossOffset_of_n_eq_zero` (at `n = 0` the
two Target value slopes agree with no floor condition), so the binders are unchanged.
General in `F`. -/
theorem exists_planner_efficient_completion_at_equilibrium
    (hTM : E.LossOffset) (hr : E.r = 0) (hn : E.n = 0)
    (hmargin : E.βS * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.r) :
    ∃ C : E.WelfareCompletion,
      (∀ x a s, C.welfare x a s = E.toParams.U_S x a s) ∧
      (∀ x : ↥(Sanctions.S : Set ℝ),
        (E.equilibriumPlan x).1.1
          = ((E.toChord.equilibriumTop_of_margin (E.toChord_lossOffset_of_n_eq_zero hn hTM))
              (E.toChord_margin hmargin)).α x.1 ∧
        (E.equilibriumPlan x).2.1
          = E.toChord.toParams.dynamicEquilibriumRule
              ((E.toChord.equilibriumTop_of_margin (E.toChord_lossOffset_of_n_eq_zero hn hTM))
                (E.toChord_margin hmargin)) x.1) ∧
      ∀ (π : InfiniteHorizonVerification.MarkovPlan ↥(Sanctions.S : Set ℝ)
            (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
        (x₀ : ↥(Sanctions.S : Set ℝ)),
        InfiniteHorizonVerification.discountedPayoff (E.plannerStage C) E.plannerStep E.βS π x₀
          ≤ InfiniteHorizonVerification.discountedPayoff (E.plannerStage C) E.plannerStep E.βS
              (InfiniteHorizonVerification.stationaryPlan E.equilibriumPlan) x₀ := by
  obtain ⟨C, hW, hopt⟩ := E.exists_planner_efficient_completion hr hn
  refine ⟨C, hW, fun x => ⟨rfl, ?_⟩, hopt⟩
  exact ((E.toChord.dynamicRule_eq_responsePath (E.toChord_lossOffset_of_n_eq_zero hn hTM))
    (E.toChord_margin hmargin) x.property).symm

/-- The same at a flat transition, where the margin is discharged
(`familyMargin_of_flat`). General in `F` under the flatness certificate
`M_cx = M_mix = 0` (convex state sections, no mixed curvature). The affine law
meets it, and so does every additively separable transition with convex state
sections; the certificate is weaker than assuming the affine law. Renovation item BJ2.3:
no part of interiority is read, as in `exists_planner_efficient_completion_at_equilibrium`
(the loss-offset margin reaches the chord economy through
`toChord_lossOffset_of_n_eq_zero`). -/
theorem exists_planner_efficient_completion_of_flat (hTM : E.LossOffset)
    (hr : E.r = 0) (hn : E.n = 0) (hMcx : E.Mcx = 0) (hMmix : E.Mmix = 0) :
    ∃ C : E.WelfareCompletion,
      (∀ x a s, C.welfare x a s = E.toParams.U_S x a s) ∧
      (∀ x : ↥(Sanctions.S : Set ℝ),
        (E.equilibriumPlan x).1.1
          = ((E.toChord.equilibriumTop_of_flat (E.toChord_lossOffset_of_n_eq_zero hn hTM)) rfl
              hMcx hMmix).α x.1 ∧
        (E.equilibriumPlan x).2.1
          = E.toChord.toParams.dynamicEquilibriumRule
              ((E.toChord.equilibriumTop_of_flat (E.toChord_lossOffset_of_n_eq_zero hn hTM)) rfl
                hMcx hMmix) x.1) ∧
      ∀ (π : InfiniteHorizonVerification.MarkovPlan ↥(Sanctions.S : Set ℝ)
            (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
        (x₀ : ↥(Sanctions.S : Set ℝ)),
        InfiniteHorizonVerification.discountedPayoff (E.plannerStage C) E.plannerStep E.βS π x₀
          ≤ InfiniteHorizonVerification.discountedPayoff (E.plannerStage C) E.plannerStep E.βS
              (InfiniteHorizonVerification.stationaryPlan E.equilibriumPlan) x₀ :=
  (E.exists_planner_efficient_completion_at_equilibrium hTM) hr hn
    (E.familyMargin_of_flat hMcx hMmix)

end PlacableEconomyF

/-- **The boundary is inhabited**: the constructed member `placableBoundary` has
`r = n = 0`, so it carries a planner-efficient completion (Rule 9: an existence
certificate, refuting universal strict inefficiency across completions). -/
theorem placableBoundary_planner_efficient_completion :
    ∃ C : placableBoundary.toPlacableEconomyF.WelfareCompletion,
      (∀ x a s, C.welfare x a s = placableBoundary.toParams.U_S x a s) ∧
      ∀ (π : InfiniteHorizonVerification.MarkovPlan ↥(Sanctions.S : Set ℝ)
            (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
        (x₀ : ↥(Sanctions.S : Set ℝ)),
        InfiniteHorizonVerification.discountedPayoff
            (placableBoundary.toPlacableEconomyF.plannerStage C)
            placableBoundary.toPlacableEconomyF.plannerStep placableBoundary.βS π x₀
          ≤ InfiniteHorizonVerification.discountedPayoff
              (placableBoundary.toPlacableEconomyF.plannerStage C)
              placableBoundary.toPlacableEconomyF.plannerStep placableBoundary.βS
              (InfiniteHorizonVerification.stationaryPlan
                placableBoundary.toPlacableEconomyF.equilibriumPlan) x₀ :=
  placableBoundary.toPlacableEconomyF.exists_planner_efficient_completion rfl rfl

/-- **The bridge is inhabited**: `placableBoundary` is affine (flat) with
`r = n = 0`, so its constructed forward-looking equilibrium's own play attains
the planner optimum of a positive-weight completion at `β_P = β_S` (Rule 9:
existence; Rule 22: affine, marked). Renovation item BJ2.3 (2026-10-07): the loss-offset
proof term is `toChord_lossOffset_of_n_eq_zero` at `n = 0`, read without interiority. -/
theorem placableBoundary_planner_efficient_at_equilibrium :
    ∃ C : placableBoundary.toPlacableEconomyF.WelfareCompletion,
      (∀ x a s, C.welfare x a s = placableBoundary.toParams.U_S x a s) ∧
      (∀ x : ↥(Sanctions.S : Set ℝ),
        (placableBoundary.toPlacableEconomyF.equilibriumPlan x).1.1
          = ((placableBoundaryBase.toChord.equilibriumTop_of_flat
              (placableBoundaryBase.toChord_lossOffset_of_n_eq_zero rfl
                placableBoundaryBase_margin)) rfl rfl rfl).α
              x.1 ∧
        (placableBoundary.toPlacableEconomyF.equilibriumPlan x).2.1
          = placableBoundaryBase.toChord.toParams.dynamicEquilibriumRule
              ((placableBoundaryBase.toChord.equilibriumTop_of_flat
                (placableBoundaryBase.toChord_lossOffset_of_n_eq_zero rfl
                  placableBoundaryBase_margin)) rfl rfl rfl)
              x.1) ∧
      ∀ (π : InfiniteHorizonVerification.MarkovPlan ↥(Sanctions.S : Set ℝ)
            (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
        (x₀ : ↥(Sanctions.S : Set ℝ)),
        InfiniteHorizonVerification.discountedPayoff
            (placableBoundary.toPlacableEconomyF.plannerStage C)
            placableBoundary.toPlacableEconomyF.plannerStep placableBoundary.βS π x₀
          ≤ InfiniteHorizonVerification.discountedPayoff
              (placableBoundary.toPlacableEconomyF.plannerStage C)
              placableBoundary.toPlacableEconomyF.plannerStep placableBoundary.βS
              (InfiniteHorizonVerification.stationaryPlan
                placableBoundary.toPlacableEconomyF.equilibriumPlan) x₀ :=
  placableBoundaryBase.exists_planner_efficient_completion_of_flat
    placableBoundaryBase_margin rfl rfl rfl rfl

end

#print axioms PlacableEconomyF.exists_planner_efficient_completion
#print axioms placableBoundary_planner_efficient_completion
#print axioms PlacableEconomyF.flat_of_margin_of_r_eq_zero
#print axioms PlacableEconomyF.exists_planner_efficient_completion_at_equilibrium
#print axioms placableBoundary_planner_efficient_at_equilibrium
#print axioms PlacableEconomyF.WelfareCompletion.govS_eq
#print axioms PlacableEconomyF.WelfareCompletion.govT_eq
#print axioms PlacableEconomyF.WelfareCompletion.welfare_eq
#print axioms PlacableEconomyF.WelfareCompletion.govS_add_govT_eq
#print axioms PlacableEconomyF.exists_welfareCompletion
#print axioms PlacableEconomyF.exists_equalValuation_completion
#print axioms PlacableEconomyF.exists_completion_bJ_eq_bK_iff
#print axioms tsum_geometric_lt_of_forall_lt
#print axioms ChordEconomy.senderObj_le_VSstar
#print axioms ChordEconomy.senderObj_responsePath_eq_VSstar
#print axioms PlacableEconomyFcs.exists_completions_reversing_regime_ranking
#print axioms PlacableEconomyFcs.exists_completions_reversing_regime_ranking_of_response_monotone

end Examples
end Sanctions
