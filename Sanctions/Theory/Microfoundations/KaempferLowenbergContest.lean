/-
Sanctions/Theory/Microfoundations/KaempferLowenbergContest.lean

**P10 contest layer: the Kaempfer-Lowenberg pressure schedules DERIVED from a
Becker (1983) two-group pressure contest (user-approved Rule-3 addition,
2026-07-11).**

`KaempferLowenbergPolity.Polity` carries the three sanction channels (`rally`,
`incid`, `empower`) and the clearing schedule `xstar` as structure *fields* —
assumed pressure schedules.  This file derives them as **Nash-equilibrium
objects**: at each sanction level `s`, the target polity's two groups (`J_T`
regime supporters, `K_T` opposition) play the Becker additive-influence
quadratic-cost contest of `Foundations/BeckerContest.lean`; their stakes are
the sanction-exposed marginal benefits of entrenchment **already present in
`FourGroup`** (the `∂U_T/∂x` coefficients `(th0_JT + ρ·s)·b_J` and
`(th0_KT + μ·s)·b_K`), minus incidence erosion; and the closed-form
dominant-strategy pressures `p_J*(s), p_K*(s)` reproduce the K-L channel
schedules exactly.  Lock-in is then obtained **by applying** the existing
sufficient condition `lockIn_of_rally_dominates` — consumed, not restated.

The ONLY new primitives (user-approved) are the four contest scalars
`cp_J, cp_K > 0` and `iota_J, iota_K ≥ 0` on the new `ContestPolity`
structure.  The stakes reuse `th0_JT, rho, b_J, th0_KT, mu, b_K`; the clearing
slope/intercept `beta1, beta0` are *derived* closed forms, not fields; and the
two dominance conditions are strict inequalities among existing + approved
primitives with no named gap scalar (symbol economy).  At equal contest costs
`cp_J = cp_K` the cost-adjusted rally dominance degenerates *literally* to the
existing `FourGroup.rally_dom` (see `contestRally_dom_degenerate`).

Since 2026-10-07 (BH6.2) `ContestPolity` extends the bare coefficients
`FourGroupCoeffs`, not `FourGroup`: it no longer carries `rally_dom`
(`μ·b_K < ρ·b_J`) or the other three region-(R) fields, none of which any proof
here read. The contest layer's lock-in condition is therefore the cost-adjusted
inequality `contestRally_dom` alone, which is what "strictly generalizes region
(R)" claims; before, it was that inequality on top of `rally_dom`.

Naming note: `FourGroup.c_J / c_K` are the *welfare compliance* coefficients
in `U_T`, so the contest cost coefficients must be `cp_J / cp_K` to avoid the
clash.

Concrete non-vacuity is kept in
`Examples/KaempferLowenbergContestWitness.lean`, so this parametric Theory
module does not depend on the Examples layer.
-/

import Sanctions.Foundations.BeckerContest
import Sanctions.Theory.Microfoundations.KaempferLowenbergPolity
import Sanctions.Theory.Microfoundations.FourGroupPolity

namespace Sanctions
namespace KaempferLowenberg

/-- **A four-group polity equipped with a Becker pressure contest** (the P10
contest layer).  Extends the eighteen four-group coefficients `FourGroupCoeffs`
with the four user-approved contest primitives and the region conditions
(endpoint stake inequalities + the two cost-adjusted dominance conditions), all
strict/weak inequalities among existing + approved primitives — no named gap
scalars.  It does not carry the four-group region (R) (BH6.2, 2026-10-07): in
particular not `FourGroup.rally_dom`, whose role here is played by the
cost-adjusted `contestRally_dom`.  The structure itself fixes no transition
(Rule 22); its induced transition `toPolity.inducedF` is the partial-adjustment
law of `KaempferLowenbergPolity`, which under the diagonal clearing `x* = id` is
the affine law (`toPolity_inducedF_eq_affineF`). -/
structure ContestPolity extends FourGroupCoeffs where
  /-- **New primitive (Rule 3, user-approved 2026-07-11).**  Becker (1983,
  QJE 98(3), §III eqs. 11, 15–16) quadratic pressure-production cost
  coefficient of the regime-supporter group `J_T`: producing pressure `p`
  costs `cp_J·p²`.  Prices political pressure — no existing parameter does.
  The ratio `cp_K/cp_J` is Becker's relative-efficiency comparative static. -/
  cp_J : ℝ
  /-- **New primitive (Rule 3, user-approved 2026-07-11).**  Quadratic
  pressure-production cost coefficient of the opposition group `K_T`
  (Becker 1983, eqs. 11, 15–16): producing pressure `q` costs `cp_K·q²`. -/
  cp_K : ℝ
  /-- **New primitive (Rule 3, user-approved 2026-07-11).**  Kaempfer-Lowenberg
  income-incidence exposure slope of `J_T`: each unit of sanction erodes the
  regime supporters' contestable stake by `iota_J` (K-L eq. 7 incidence
  channel; the aggregate sanction cost `d_s·s` hits `U_T`, not group stakes,
  so this has no existing representative). -/
  iota_J : ℝ
  /-- **New primitive (Rule 3, user-approved 2026-07-11).**  Income-incidence
  exposure slope of the opposition `K_T`: each unit of sanction erodes the
  opposition's contestable stake by `iota_K`.  Sanctions eroding `K`'s stake
  more than `J`'s raise net pro-entrenchment pressure. -/
  iota_K : ℝ
  /-- Pressure is costly for `J_T` (strict convexity of the contest cost). -/
  cp_J_pos : 0 < cp_J
  /-- Pressure is costly for `K_T`. -/
  cp_K_pos : 0 < cp_K
  /-- Interior contest at `s = 0`: `J`'s baseline stake `th0_JT·b_J` is
  nonnegative (endpoint inequality over existing parameters). -/
  stakeJ_nn0 : 0 ≤ th0_JT * b_J
  /-- Interior contest at `s = 1`: incidence erosion does not exhaust `J`'s
  rallied stake (endpoint inequality; with `stakeJ_nn0`, affinity keeps the
  `pStar` clip inactive on all of `[0,1]`). -/
  stakeJ_nn1 : iota_J ≤ (th0_JT + rho) * b_J
  /-- Interior contest at `s = 0`: `K`'s baseline stake is nonnegative. -/
  stakeK_nn0 : 0 ≤ th0_KT * b_K
  /-- Interior contest at `s = 1`: incidence erosion does not exhaust `K`'s
  empowered stake. -/
  stakeK_nn1 : iota_K ≤ (th0_KT + mu) * b_K
  /-- **Cost-adjusted rally dominance (h1)**: the rally channel outweighs the
  empowerment channel after adjusting for the groups' lobbying efficiencies.
  At `cp_J = cp_K` this is *literally* `FourGroup.rally_dom`
  (`μ·b_K < ρ·b_J`) — see `contestRally_dom_degenerate`. -/
  contestRally_dom : cp_J * (mu * b_K) < cp_K * (rho * b_J)
  /-- **Cost-adjusted incidence burden (h2)**: the incidence burden falls on
  the opposition (sanctions erode `K`'s stake at least as fast as `J`'s,
  efficiency-adjusted), so the derived incidence channel is monotone. -/
  incid_favors_J : cp_K * iota_J ≤ cp_J * iota_K

namespace ContestPolity

variable (G : ContestPolity)

/-! ### Stakes: microfounded from sanction exposure, reusing `FourGroup`

`S_J(s)` is exactly the `∂U_T/∂x` coefficient of the `J_T` term of
`FourGroup.U_T` (the effectiveness-weighted marginal benefit of entrenchment
`(th0_JT + ρ·s)·b_J`), minus the incidence erosion `iota_J·s`; symmetrically
for the opposition. -/

/-- `J_T`'s contested stake at sanction level `s`:
`S_J(s) = (th0_JT + ρ·s)·b_J − iota_J·s`. -/
def stakeJ (s : ℝ) : ℝ := (G.th0_JT + G.rho * s) * G.b_J - G.iota_J * s

/-- `K_T`'s contested stake at sanction level `s`:
`S_K(s) = (th0_KT + μ·s)·b_K − iota_K·s`. -/
def stakeK (s : ℝ) : ℝ := (G.th0_KT + G.mu * s) * G.b_K - G.iota_K * s

/-- The `J` stake is nonnegative on `[0,1]` (affine ⟹ endpoint checks). -/
theorem stakeJ_nonneg {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ G.stakeJ s := by
  obtain ⟨hs0, hs1⟩ := hs
  have h0 := G.stakeJ_nn0
  have h1 := sub_nonneg.mpr G.stakeJ_nn1
  simp only [stakeJ]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) h0, mul_nonneg hs0 h1]

/-- The `K` stake is nonnegative on `[0,1]`. -/
theorem stakeK_nonneg {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ G.stakeK s := by
  obtain ⟨hs0, hs1⟩ := hs
  have h0 := G.stakeK_nn0
  have h1 := sub_nonneg.mpr G.stakeK_nn1
  simp only [stakeK]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) h0, mul_nonneg hs0 h1]

/-! ### Equilibrium pressures (Rule 1: derived argmaxes, not assumptions) -/

/-- `J_T`'s equilibrium pressure: the dominant-strategy Nash closed form
`p_J*(s) = max 0 (S_J(s)/(2·cp_J))`. -/
noncomputable def pJ (s : ℝ) : ℝ := BeckerContest.pStar (G.stakeJ s) G.cp_J

/-- `K_T`'s equilibrium pressure. -/
noncomputable def pK (s : ℝ) : ℝ := BeckerContest.pStar (G.stakeK s) G.cp_K

/-- **Rule-1 certificate: `(p_J*(s), p_K*(s)) is a Nash equilibrium** of the
Becker pressure contest at sanction level `s` — each group's pressure is a
best response (a dominant strategy) to the other's, certified by the
completed-square argmax identity.  The pressure schedules the polity carries
are *derived optimizers*, not hand-chosen strategies. -/
theorem pJ_pK_isNash (s : ℝ) :
    IsMaxOn (fun p => G.stakeJ s * (p - G.pK s) - G.cp_J * p ^ 2)
        (Set.Ici 0) (G.pJ s) ∧
      IsMaxOn (fun q => G.stakeK s * (q - G.pJ s) - G.cp_K * q ^ 2)
        (Set.Ici 0) (G.pK s) :=
  BeckerContest.contest_nash G.cp_J_pos G.cp_K_pos (G.stakeJ s) (G.stakeK s)

/-- On `[0,1]` the clip is inactive: `p_J*(s) = S_J(s)/(2·cp_J)` (interior
contest, from the endpoint stake inequalities). -/
theorem pJ_eq {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    G.pJ s = G.stakeJ s / (2 * G.cp_J) :=
  BeckerContest.pStar_eq_of_nonneg G.cp_J_pos (G.stakeJ_nonneg hs)

/-- On `[0,1]` the clip is inactive: `p_K*(s) = S_K(s)/(2·cp_K)`. -/
theorem pK_eq {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    G.pK s = G.stakeK s / (2 * G.cp_K) :=
  BeckerContest.pStar_eq_of_nonneg G.cp_K_pos (G.stakeK_nonneg hs)

/-! ### The derived K-L channel schedules (definitions, no longer fields) -/

/-- **Derived rally schedule**: `J`'s equilibrium pressure from the `E^J`
effectiveness channel, `rally(s) = (th0_JT + ρ·s)·b_J/(2·cp_J)`. -/
noncomputable def rallyC (s : ℝ) : ℝ :=
  (G.th0_JT + G.rho * s) * G.b_J / (2 * G.cp_J)

/-- **Derived empowerment schedule**: `K`'s equilibrium pressure from the
`E^K` channel, `empower(s) = (th0_KT + μ·s)·b_K/(2·cp_K)`. -/
noncomputable def empowerC (s : ℝ) : ℝ :=
  (G.th0_KT + G.mu * s) * G.b_K / (2 * G.cp_K)

/-- **Derived income-incidence schedule**: the net incidence pressure
`incid(s) = (iota_K/(2·cp_K) − iota_J/(2·cp_J))·s` — sanctions eroding the
opposition's contestable stake more than the regime's raise net
pro-entrenchment pressure. -/
noncomputable def incidC (s : ℝ) : ℝ :=
  (G.iota_K / (2 * G.cp_K) - G.iota_J / (2 * G.cp_J)) * s

/-- **Channel decomposition (interior identity)**: on `[0,1]` the three
derived K-L channels recompose the equilibrium pressure difference exactly:
`rally(s) + incid(s) − empower(s) = p_J*(s) − p_K*(s)`. -/
theorem channel_decomp {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    G.rallyC s + G.incidC s - G.empowerC s = G.pJ s - G.pK s := by
  rw [G.pJ_eq hs, G.pK_eq hs]
  simp only [rallyC, incidC, empowerC, stakeJ, stakeK]
  ring

/-! ### Derived market clearing: `beta1`, `beta0`, and the diagonal `x*` -/

/-- **Derived clearing slope** (not a primitive): the slope of the net
sanction channel, `beta1 = ρ·b_J/(2·cp_J) − μ·b_K/(2·cp_K) +
(iota_K/(2·cp_K) − iota_J/(2·cp_J))` — the sum of the rally-dominance slope
and the incidence slope. -/
noncomputable def beta1 : ℝ :=
  G.rho * G.b_J / (2 * G.cp_J) - G.mu * G.b_K / (2 * G.cp_K)
    + (G.iota_K / (2 * G.cp_K) - G.iota_J / (2 * G.cp_J))

/-- **Derived clearing intercept** (not a primitive):
`beta0 = −(th0_JT·b_J/(2·cp_J) − th0_KT·b_K/(2·cp_K))`, i.e. minus the net
channel at `s = 0`. -/
noncomputable def beta0 : ℝ :=
  -(G.th0_JT * G.b_J / (2 * G.cp_J) - G.th0_KT * G.b_K / (2 * G.cp_K))

/-- The rally-dominance slope is strictly positive: cost-adjusted (h1),
cross-divided. -/
theorem rally_slope_pos :
    G.mu * G.b_K / (2 * G.cp_K) < G.rho * G.b_J / (2 * G.cp_J) := by
  rw [div_lt_div_iff₀ (mul_pos two_pos G.cp_K_pos) (mul_pos two_pos G.cp_J_pos)]
  nlinarith [G.contestRally_dom]

/-- The incidence slope is nonnegative: cost-adjusted (h2), cross-divided. -/
theorem incid_slope_nonneg :
    G.iota_J / (2 * G.cp_J) ≤ G.iota_K / (2 * G.cp_K) := by
  rw [div_le_div_iff₀ (mul_pos two_pos G.cp_J_pos) (mul_pos two_pos G.cp_K_pos)]
  linarith [G.incid_favors_J]

/-- **Strict clearing slope** (`beta1 > 0`): under strict (h1) + (h2) the net
channel is strictly increasing, so the clearing pressure `b(x) = beta0 −
beta1·x` is strictly decreasing — exactly the strict lock-in region.  (This
is also why the diagonal normalization `x* = id` exists here and *cannot*
exist on the wash-out mirror: an antitone `x*` cannot be the identity.) -/
theorem beta1_pos : 0 < G.beta1 := by
  have hA := G.rally_slope_pos
  have hB := G.incid_slope_nonneg
  simp only [beta1]
  linarith

/-! ### The constructed polity: schedules ARE the derived definitions -/

/-- **The Becker-contest-microfounded K-L polity.**  The channel fields are
*the derived Nash-equilibrium schedules* (`rallyC`, `incidC`, `empowerC`),
the baseline pressure is the derived affine clearing `b(x) = beta0 −
beta1·x` (strictly decreasing by `beta1_pos`), and the clearing schedule is
the diagonal normalization `x*(s) = s`, whose market-clearing identity
`hroot` is an exact polynomial identity in the primitives (by `ring`). -/
noncomputable def toPolity : Polity where
  b := fun x => G.beta0 - G.beta1 * x
  hb := by
    intro x y hxy
    dsimp only
    have h := mul_lt_mul_of_pos_left hxy G.beta1_pos
    linarith
  rally := G.rallyC
  incid := G.incidC
  empower := G.empowerC
  xstar := fun s => s
  hroot := by
    intro s
    simp only [rallyC, incidC, empowerC, beta0, beta1]
    ring

/-- The constructed polity's clearing schedule is the identity — this is the
`hdiag` input of `inducedF_diag` (`F_diag`), definitionally. -/
theorem toPolity_xstar_eq_id : ∀ s, G.toPolity.xstar s = s := fun _ => rfl

/-- The derived rally − empowerment difference is monotone: slope
`ρ·b_J/(2·cp_J) − μ·b_K/(2·cp_K) > 0` from cost-adjusted (h1). -/
theorem rallyC_sub_empowerC_mono :
    Monotone fun s => G.rallyC s - G.empowerC s := by
  intro s s' hss'
  have key : (G.rallyC s' - G.empowerC s') - (G.rallyC s - G.empowerC s)
      = (G.rho * G.b_J / (2 * G.cp_J) - G.mu * G.b_K / (2 * G.cp_K))
          * (s' - s) := by
    simp only [rallyC, empowerC]
    ring
  have hprod : 0 ≤ (G.rho * G.b_J / (2 * G.cp_J)
      - G.mu * G.b_K / (2 * G.cp_K)) * (s' - s) :=
    mul_nonneg (sub_nonneg.mpr G.rally_slope_pos.le) (sub_nonneg.mpr hss')
  dsimp only
  linarith [key, hprod]

/-- The derived incidence schedule is monotone: slope
`iota_K/(2·cp_K) − iota_J/(2·cp_J) ≥ 0` from cost-adjusted (h2). -/
theorem incidC_mono : Monotone G.incidC := by
  intro s s' hss'
  have hB := G.incid_slope_nonneg
  simp only [incidC]
  nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hss')]

/-- **Lock-in, by CONSUMING the existing sufficient condition**: the derived
schedules satisfy the exact hypotheses of `lockIn_of_rally_dominates`
(monotone `rally − empower`, monotone `incid`), so the contest polity is in
the high-basin lock-in regime.  The existing theorem is applied, not
restated. -/
theorem toPolity_lockIn : G.toPolity.LockIn :=
  G.toPolity.lockIn_of_rally_dominates G.rallyC_sub_empowerC_mono G.incidC_mono

/-! ### The five `inducedF` discharges, through the constructor

Exactly the transition obligations an `AbstractGame.Params` consumes
(cf. `EatonEngersWitness`): `F_mono_s` from the *derived* lock-in, `F_mono_x`,
`F_diag` from the diagonal clearing, `F_mem`, `F_continuous`. -/

/-- `F_mono_s` fires: the induced transition is monotone in the sanction —
sourced from the contest-derived lock-in, not assumed. -/
theorem toPolity_inducedF_mono_s {δ : ℝ} (hδ0 : 0 ≤ δ) :
    ∀ x, Monotone fun s => G.toPolity.inducedF δ x s :=
  G.toPolity.inducedF_mono_s G.toPolity_lockIn hδ0

/-- `F_mono_x` fires: monotone in the current state. -/
theorem toPolity_inducedF_mono_x {δ : ℝ} (hδ1 : δ ≤ 1) :
    ∀ s, Monotone fun x => G.toPolity.inducedF δ x s :=
  G.toPolity.inducedF_mono_x hδ1

/-- `F_diag` fires: a sanction equal to the current entrenchment reproduces
it (diagonal clearing `x* = id`). -/
theorem toPolity_inducedF_diag {δ : ℝ} : ∀ x, G.toPolity.inducedF δ x x = x :=
  G.toPolity.inducedF_diag G.toPolity_xstar_eq_id

/-- `F_mem` fires: the induced transition maps `[0,1]²` into `[0,1]`. -/
theorem toPolity_inducedF_mem {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
      G.toPolity.inducedF δ x s ∈ Set.Icc (0 : ℝ) 1 :=
  G.toPolity.inducedF_mem hδ (fun _ hs => hs)

/-- `F_continuous` fires: the induced transition is jointly continuous. -/
theorem toPolity_inducedF_continuous {δ : ℝ} :
    Continuous fun xs : ℝ × ℝ => G.toPolity.inducedF δ xs.1 xs.2 :=
  G.toPolity.inducedF_continuous continuous_id

end ContestPolity

/-! ### Degeneration to the existing region (R) -/

/-- **Degeneration lemma**: at equal contest costs `cp_J = cp_K = cp > 0`,
the cost-adjusted rally dominance (h1) is *literally* the existing
`FourGroup.rally_dom` inequality `μ·b_K < ρ·b_J` — the contest layer strictly
generalizes region (R), it does not replace it. -/
theorem contestRally_dom_degenerate (Gf : FourGroup) {cp : ℝ} (hcp : 0 < cp) :
    cp * (Gf.mu * Gf.b_K) < cp * (Gf.rho * Gf.b_J) ↔
      Gf.mu * Gf.b_K < Gf.rho * Gf.b_J :=
  mul_lt_mul_iff_right₀ hcp

/-- At equal costs (h1) holds *for free* from the `rally_dom` field of any
`FourGroup`: every region-(R) polity's coefficients support the contest layer
with symmetric lobbying technology. (`ContestPolity` extends `FourGroupCoeffs`
since BH6.2, so `FourGroup` is not its parent; the polity enters as `Gf`.) No
transition enters. -/
theorem contestRally_dom_of_eq_costs (Gf : FourGroup) {cp : ℝ} (hcp : 0 < cp) :
    cp * (Gf.mu * Gf.b_K) < cp * (Gf.rho * Gf.b_J) :=
  (contestRally_dom_degenerate Gf hcp).mpr Gf.rally_dom

end KaempferLowenberg
end Sanctions
