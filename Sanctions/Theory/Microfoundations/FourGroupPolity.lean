/-
Sanctions/Theory/Microfoundations/FourGroupPolity.lean

**Dynamic four-group (two-country, two-party-each) microfoundation of the stage
complementarities.**

Kaempfer-Lowenberg (1988) is a two-country, four-group model: §I the sender's two
groups (pro-sanction protectionist/expressive `J_S` vs anti-sanction
trade-dependent `K_S`) and §II the target's two groups (regime/hardline `J_T` vs
opposition `K_T`). Each group `g` has a welfare `w_g(x,a,s)` and a political
weight `θ_g(x,s)` (the K-L effectiveness, depending on the rally/empowerment
channels). Following Grossman-Helpman (1994, eq. 11), each country's stage payoff
is the **weighted sum of its groups' welfares** — *derived*, not posited:

  U_S = θ_{J_S}·w_{J_S} + θ_{K_S}·w_{K_S},   U_T = θ_{J_T}·w_{J_T} + θ_{K_T}·w_{K_T}.

This file uses clean LQ forms (linear welfares, linear weights, placation a
separate term) so each stage cross-partial is a single derived coefficient:

  ∂²U_S/∂s∂x = ν·g_J         (sender rally: hawks rise with target entrenchment)
  ∂²U_S/∂s∂a = −w_pl         (placation: pro-sanction value falls with compliance)
  ∂²U_T/∂s∂x = ρ·b_J − μ·b_K (target rally ρ vs opposition empowerment μ)

The project's stage primitives `SenderStageID` / `TargetStageID` / `SenderActionDD`
(the order-language forms of these cross-partial signs that drive the basin) are
therefore **derived** from the group-effectiveness primitives, holding exactly on
the rally-dominant region

  (R)   ν·g_J ≥ 0,   w_pl ≥ 0,   ρ·b_J ≥ μ·b_K.

(R) is not a new `Prop` on `U_S/U_T`; it is a sign region among the group
primitives, and what it delivers is exactly the stage-order signs: on (R) the
three cross-partials carry the displayed signs, so `SenderStageID`,
`SenderActionDD` and `TargetStageID` hold. It is not by itself a statement
about basins. Outside (R) — `ρ·b_J < μ·b_K`, the empowerment-dominant sign —
`TargetStageID` fails, which removes a stage input of the persistence theorem;
whether the state then washes out is a question about an equilibrium and its
level conditions, which the polity's signs alone do not settle (Rule 9A: a sign
region licenses no dynamic claim). The fields record the region in the strict
form the `Params` wiring needs (`kS_pos`, `senderRally_pos`, `rally_dom`) with
placation as a weak sign (`w_pl_nn`); the display above is the weak reading.
`docs/archive/workflow-scratch/fourgroup_solver.py` is a numerical exploration
of one calibration (Rule 9D: evidence of neither existence nor bistability);
the machine-checked content is the sign derivation below and the affine
welfare witness that consumes it.

The transition is supplied by the caller: `toParamsF` takes `F` and its five
structural obligations as arguments; the affine instance `toParams` lives in
`Examples/AffineInstance/Microfoundations.lean` and is definitionally its
`affineF δ` member (`toParamsF_affineF`). Every four-group economy currently in
the tree instantiates the affine one (Rule 22 axis 3), so nothing here yet
exhibits a non-affine interest-group polity. The genuine economic content of
the rally is in these derived stage complementarities, which the existing
persistence theorem consumes to deliver the long-run lock-in.

Two additions of 2026-10-07. `FourGroupCoeffs` is the eighteen coefficients
with no region field, and `FourGroup.toCoeffs` projects a polity onto them
(BH6.2): the welfare layer reads only coefficients, so it is stated there and
the `FourGroup` forms are `rfl` corollaries. `FourGroup.hawkRescale` multiplies
the hawks' per-unit benefit `g_J` by `k ≠ 0` and divides their weight schedule
by `k` (BH6.1): both stage payoffs, the static selector and therefore the
induced `Params` are unchanged for every transition (`hawkRescale_toParamsF`),
while the unit-weight planner sees `(k − 1)·g_J·s` more (`FourGroupPlanner.lean`).
-/

import Sanctions.Foundations.MilgromShannon
import Sanctions.Postulates.AbstractGame

namespace Sanctions
namespace KaempferLowenberg

open Sanctions.MilgromShannon

/-- **The eighteen four-group coefficients, with no region condition** (BH6.2,
2026-10-07). The numeric data of `FourGroup` alone — every weight, welfare and
cost coefficient, in the same order and with the same names — and none of the
four region-(R) fields (`w_pl_nn`, `kS_pos`, `senderRally_pos`, `rally_dom`).

The welfare layer of `FourGroupPlanner.lean` (the planner objective, the
stationary and path accounting, the affine and general-transition gap
identities and sign characterizations) reads only these coefficients, so it is
stated over this structure and holds for every coefficient vector, including
empowerment-dominant polities outside region (R). A `FourGroup` reaches it
through the projection `FourGroup.toCoeffs`; `FourGroup` itself is a pinned
contract root and is not re-based on this structure. No assumption is added:
this is a structure with fewer fields, not a new primitive. -/
structure FourGroupCoeffs where
  th0_JS : ℝ
  nu : ℝ
  g_J : ℝ
  th0_KS : ℝ
  q_K : ℝ
  kS : ℝ
  w_pl : ℝ
  base_S : ℝ
  th0_JT : ℝ
  rho : ℝ
  b_J : ℝ
  c_J : ℝ
  th0_KT : ℝ
  mu : ℝ
  b_K : ℝ
  c_K : ℝ
  kT : ℝ
  d_s : ℝ

namespace FourGroupCoeffs
variable (G : FourGroupCoeffs)

/-- The Grossman-Helpman Sender stage payoff over bare coefficients; the same
expression as `FourGroup.U_S`, which is its `toCoeffs` instance by `rfl`. -/
def U_S (x a s : ℝ) : ℝ :=
  G.base_S * a + (G.th0_JS + G.nu * x) * G.g_J * s
    - G.th0_KS * G.q_K * s - G.kS * s ^ 2 - G.w_pl * s * a

/-- The Grossman-Helpman Target stage payoff over bare coefficients; the same
expression as `FourGroup.U_T`. -/
def U_T (x a s : ℝ) : ℝ :=
  (G.th0_JT + G.rho * s) * (G.b_J * x - G.c_J * a)
    + (G.th0_KT + G.mu * s) * (-G.b_K * x + G.c_K * a)
    - G.kT * a ^ 2 - G.d_s * s

end FourGroupCoeffs

/-- Four-group interest-group primitives with the clean LQ Grossman-Helpman
aggregation. The `*_nn` and `rally_dom` fields are the rally-dominant region (R)
(strict inequalities among the group-effectiveness primitives), under which the
derived stage complementarities below hold. -/
structure FourGroup where
  -- sender (§I): hawk weight `θ_{J_S}(x) = th0_JS + nu·x`; pro-sanction benefit
  -- `g_J·s`; constant anti-sanction `K_S` with `q_K`; deadweight `kS·s²`;
  -- placation `w_pl·s·a`; direct compliance benefit `base_S·a`.
  th0_JS : ℝ
  nu : ℝ
  g_J : ℝ
  th0_KS : ℝ
  q_K : ℝ
  kS : ℝ
  w_pl : ℝ
  base_S : ℝ
  -- target (§II): weights `θ_{J_T}(s)=th0_JT+ρ·s`, `θ_{K_T}(s)=th0_KT+μ·s`;
  -- welfares linear in `x,a`; concavity `kT·a²`; sanction cost `d_s·s`.
  th0_JT : ℝ
  rho : ℝ
  b_J : ℝ
  c_J : ℝ
  th0_KT : ℝ
  mu : ℝ
  b_K : ℝ
  c_K : ℝ
  kT : ℝ
  d_s : ℝ
  -- strict region (R) — Rule-3 addition (user-confirmed 2026-06-24), the strict
  -- form needed to wire a valid Params: strict concavity in `s` (kS_pos, for the
  -- σ-argmax / SenderChordConcaveInS), strict sender rally (senderRally_pos, for
  -- SenderStageIDStrict), strict target rally dominance (rally_dom, for
  -- TargetStageIDStrict). Placation nonneg (w_pl_nn) for SenderActionDD.
  w_pl_nn : 0 ≤ w_pl
  kS_pos : 0 < kS
  senderRally_pos : 0 < nu * g_J
  rally_dom : mu * b_K < rho * b_J

/-! ### Symbolic non-vacuity of the rally-dominant region (R)

The two welfare headlines (`plannerW_distortion`, `plannerW_lockin_dominated_iff`)
are universally quantified over `FourGroup`, so they are only as informative as
the proof that `FourGroup` is inhabited. Before this section that proof went
through the numeric witness `fgcParams`, which is a Rule-9 existence certificate
and nothing more. The theorem below replaces it: region (R) is inhabited by an
inequality chain that names no point.

The statement is deliberately stronger than `Nonempty`: it is a *projection*
statement. Twelve of the eighteen group-effectiveness coefficients are
universally quantified and reproduced verbatim in the constructed polity, so
region (R) projects onto every value of those twelve — for each choice, the
remaining six (`kS`, `w_pl`, `nu`, `g_J`, `rho`, `b_J`) can be chosen to
satisfy the region's inequalities. That is joint feasibility, not independence:
`rally_dom` reads `mu` and `b_K`, two of the twelve, and the construction picks
`rho` above the threshold `mu·b_K/b_J` they set. What (R) is, honestly, is a
sign-and-dominance region, not a calibration (wording corrected 2026-09-11, the
reader's C08). -/
theorem exists_fourGroup_of_free
    (th0_JS th0_KS q_K base_S th0_JT c_J th0_KT c_K kT d_s b_K mu : ℝ) :
    ∃ G : FourGroup,
      G.th0_JS = th0_JS ∧ G.th0_KS = th0_KS ∧ G.q_K = q_K ∧ G.base_S = base_S
        ∧ G.th0_JT = th0_JT ∧ G.c_J = c_J ∧ G.th0_KT = th0_KT ∧ G.c_K = c_K
        ∧ G.kT = kT ∧ G.d_s = d_s ∧ G.b_K = b_K ∧ G.mu = mu := by
  -- Sanction deadweight, placation rate, and the two sender-rally factors:
  -- each obtained strictly above `0`, so no magnitude is chosen.
  obtain ⟨kS, hkS⟩ := exists_gt (0 : ℝ)
  obtain ⟨w_pl, hw_pl⟩ := exists_gt (0 : ℝ)
  obtain ⟨nu, hnu⟩ := exists_gt (0 : ℝ)
  obtain ⟨g_J, hg_J⟩ := exists_gt (0 : ℝ)
  -- Target rally: pick the hawk-welfare weight `b_J > 0` first, then take the
  -- rally slope `rho` above the threshold `mu·b_K / b_J` that rally dominance
  -- forces. The threshold is assembled from already-chosen coefficients.
  obtain ⟨b_J, hb_J⟩ := exists_gt (0 : ℝ)
  obtain ⟨rho, hrho⟩ := exists_gt (mu * b_K / b_J)
  exact ⟨{ th0_JS := th0_JS, nu := nu, g_J := g_J, th0_KS := th0_KS, q_K := q_K
           kS := kS, w_pl := w_pl, base_S := base_S
           th0_JT := th0_JT, rho := rho, b_J := b_J, c_J := c_J
           th0_KT := th0_KT, mu := mu, b_K := b_K, c_K := c_K
           kT := kT, d_s := d_s
           w_pl_nn := hw_pl.le
           kS_pos := hkS
           senderRally_pos := mul_pos hnu hg_J
           rally_dom := (div_lt_iff₀ hb_J).mp hrho },
         rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Region (R) is inhabited, with no parameter vector named.** One-line
corollary of `exists_fourGroup_of_free`. -/
instance : Nonempty FourGroup :=
  let ⟨G, _⟩ := exists_fourGroup_of_free 0 0 0 0 0 0 0 0 0 0 0 0
  ⟨G⟩

namespace FourGroup
variable (G : FourGroup)

/-- **Derived Sender stage payoff** (Grossman-Helpman weighted sum, clean LQ). -/
def U_S (x a s : ℝ) : ℝ :=
  G.base_S * a + (G.th0_JS + G.nu * x) * G.g_J * s
    - G.th0_KS * G.q_K * s - G.kS * s ^ 2 - G.w_pl * s * a

/-- **Derived Target stage payoff.** -/
def U_T (x a s : ℝ) : ℝ :=
  (G.th0_JT + G.rho * s) * (G.b_J * x - G.c_J * a)
    + (G.th0_KT + G.mu * s) * (-G.b_K * x + G.c_K * a)
    - G.kT * a ^ 2 - G.d_s * s

/-- **The coefficients of a polity** (BH6.2): forget the four region fields and
keep the eighteen numbers. Every coefficient-level definition and theorem
applies to `G.toCoeffs`, and agrees with its `FourGroup` form by `rfl`
(`toCoeffs_U_S`, `toCoeffs_U_T`, and the planner-layer bridges in
`FourGroupPlanner.lean`). The generated `@[simp]` projection lemmas
(`toCoeffs_g_J`, …) read each coefficient back. -/
@[simps]
def toCoeffs : FourGroupCoeffs where
  th0_JS := G.th0_JS
  nu := G.nu
  g_J := G.g_J
  th0_KS := G.th0_KS
  q_K := G.q_K
  kS := G.kS
  w_pl := G.w_pl
  base_S := G.base_S
  th0_JT := G.th0_JT
  rho := G.rho
  b_J := G.b_J
  c_J := G.c_J
  th0_KT := G.th0_KT
  mu := G.mu
  b_K := G.b_K
  c_K := G.c_K
  kT := G.kT
  d_s := G.d_s

/-- The polity's Sender payoff is its coefficients' Sender payoff (`rfl`). -/
theorem toCoeffs_U_S : G.toCoeffs.U_S = G.U_S := rfl

/-- The polity's Target payoff is its coefficients' Target payoff (`rfl`). -/
theorem toCoeffs_U_T : G.toCoeffs.U_T = G.U_T := rfl

/-- **Derived `SenderStageID`** (`∂²U_S/∂s∂x = ν·g_J ≥ 0`, the sender rally):
order-language increasing differences of `U_S` in `(s,x)`, derived from the
hawk-influence channel. This is the project's `SenderStageID` primitive, no longer
asserted as a hand-chosen coefficient. -/
theorem U_S_senderStageID (a : ℝ) :
    IncreasingDifferencesOn Sanctions.I Sanctions.I (fun s x => G.U_S x a s) := by
  intro s s' x x' _ _ hss' _ _ hxx'
  have h := mul_nonneg (le_of_lt G.senderRally_pos)
    (mul_nonneg (sub_nonneg.mpr hss') (sub_nonneg.mpr hxx'))
  simp only [U_S]
  nlinarith [h]

/-- **Derived `TargetStageID`** (`∂²U_T/∂s∂x = ρ·b_J − μ·b_K ≥ 0` on region (R)):
the target rally dominates the opposition empowerment. The opposite strict
cross-sign (`ρ·b_J < μ·b_K`) reverses this stage-order condition on the
coefficient expression; whether an equilibrium then washes out is a separate
question needing policy, transition and basin evidence (module header; wording
corrected 2026-09-11, the reader's C21). -/
theorem U_T_targetStageID (a : ℝ) :
    IncreasingDifferencesOn Sanctions.I Sanctions.I (fun s x => G.U_T x a s) := by
  intro s s' x x' _ _ hss' _ _ hxx'
  have h := mul_nonneg (sub_nonneg.mpr (le_of_lt G.rally_dom))
    (mul_nonneg (sub_nonneg.mpr hss') (sub_nonneg.mpr hxx'))
  simp only [U_T]
  nlinarith [h]

/-- **Derived `SenderActionDD`** (`∂²U_S/∂s∂a = −w_pl ≤ 0`, placation): the
sender's marginal value of sanctioning falls as the target complies — derived
from the placation channel `w_pl`, no longer asserted. -/
theorem U_S_senderActionDD (x : ℝ) :
    DecreasingDifferencesOn Sanctions.I Sanctions.I (fun s a => G.U_S x a s) := by
  intro s s' a a' _ _ hss' _ _ haa'
  have h := mul_nonneg G.w_pl_nn
    (mul_nonneg (sub_nonneg.mpr hss') (sub_nonneg.mpr haa'))
  simp only [U_S]
  nlinarith [h]

/-- `U_S` as a concave-in-`s` parabola `base_S·a + L·s − kS·s²` with linear
coefficient `L = (th0_JS+ν·x)·g_J − th0_KS·q_K − w_pl·a`. -/
theorem U_S_eq_quad (x a s : ℝ) :
    G.U_S x a s = G.base_S * a
      + ((G.th0_JS + G.nu * x) * G.g_J - G.th0_KS * G.q_K - G.w_pl * a) * s
      - G.kS * s ^ 2 := by
  simp only [U_S]; ring

/-- **Derived `SenderStageIDStrict`** (proper sanction chords of `U_S` are
*strictly* increasing in `x`): the chord's `x`-slope is `ν·g_J·(s₂−s₁) > 0` under
strict region (R). -/
theorem U_S_senderStageIDStrict (a s₁ s₂ : ℝ) (hs : s₁ < s₂) :
    StrictMonoOn (fun x => G.U_S x a s₂ - G.U_S x a s₁) Sanctions.I := by
  intro x _ x' _ hxx'
  simp only [U_S_eq_quad]
  nlinarith [mul_pos (mul_pos G.senderRally_pos (sub_pos.mpr hs)) (sub_pos.mpr hxx')]

/-- **Derived `TargetStageIDStrict`**: the target chord's `x`-slope is
`(ρ·b_J − μ·b_K)·(s₂−s₁) > 0` under strict rally dominance. -/
theorem U_T_targetStageIDStrict (a s₁ s₂ : ℝ) (hs : s₁ < s₂) :
    StrictMonoOn (fun x => G.U_T x a s₂ - G.U_T x a s₁) Sanctions.I := by
  intro x _ x' _ hxx'
  simp only [U_T]
  nlinarith [mul_pos (mul_pos (sub_pos.mpr G.rally_dom) (sub_pos.mpr hs)) (sub_pos.mpr hxx')]

/-- **Derived `SenderChordConcaveInS`**: shifting both sanction endpoints down by
`c ≥ 0` weakly raises the chord — the derivative-free form of strict concavity of
`U_S` in `s` (the double chord is `−2·c·kS·(s₂−s₁) ≤ 0`). -/
theorem U_S_senderChordConcaveInS (x a s₁ s₂ c : ℝ)
    (hc : 0 ≤ c) (_h1 : 0 ≤ s₁ - c) (hs : s₁ ≤ s₂) (_h2 : s₂ ≤ 1) :
    G.U_S x a s₂ - G.U_S x a s₁ ≤ G.U_S x a (s₂ - c) - G.U_S x a (s₁ - c) := by
  simp only [U_S_eq_quad]
  nlinarith [mul_nonneg (mul_nonneg hc (le_of_lt G.kS_pos)) (sub_nonneg.mpr hs)]

/-- **Static Sender stage selector** — the clipped vertex `L/(2·kS)` of the
concave parabola `U_S(x,a,·)`. -/
noncomputable def sigmaSel (x a : ℝ) : ℝ :=
  max 0 (min 1 (((G.th0_JS + G.nu * x) * G.g_J - G.th0_KS * G.q_K - G.w_pl * a)
                  / (2 * G.kS)))

theorem sigmaSel_mem (x a : ℝ) : G.sigmaSel x a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem sigmaSel_continuous :
    Continuous (fun xa : ℝ × ℝ => G.sigmaSel xa.1 xa.2) := by
  unfold sigmaSel; fun_prop

/-- **Rule-1 coupling (derived).** The clipped vertex maximizes `U_S(x,a,·)` on
`[0,1]`: the static Sender selector is the stage argmax (needs strict concavity
`kS > 0`). Mirrors `eeσ_isMaxOn`. -/
theorem sigmaSel_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => G.U_S x a s) (Set.Icc (0 : ℝ) 1) (G.sigmaSel x a) := by
  rw [isMaxOn_iff]
  intro s hs
  obtain ⟨hs0, hs1⟩ := hs
  simp only [U_S_eq_quad, sigmaSel]
  have hk : 0 < G.kS := G.kS_pos
  have h2k : (2 * G.kS) ≠ 0 := by positivity
  set L := (G.th0_JS + G.nu * x) * G.g_J - G.th0_KS * G.q_K - G.w_pl * a with hLdef
  set t := L / (2 * G.kS) with htdef
  have hLt : 2 * G.kS * t = L := by rw [htdef]; field_simp
  rcases le_total t 0 with ht | ht
  · rw [min_eq_right (le_trans ht (by norm_num : (0 : ℝ) ≤ 1)), max_eq_left ht]
    nlinarith [hs0, hs1, ht, hk, hLt, sq_nonneg s, mul_nonneg hs0 (le_of_lt hk)]
  · rcases le_total t 1 with ht1 | ht1
    · rw [min_eq_right ht1, max_eq_right ht]
      nlinarith [hs0, hs1, hk, hLt, sq_nonneg (s - t)]
    · rw [min_eq_left ht1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      nlinarith [hs0, hs1, ht1, hk, hLt, sq_nonneg (s - 1),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - s) (by linarith : (0 : ℝ) ≤ t - 1)]

/-- Continuity of the derived Sender payoff on `ℝ³` (polynomial). -/
theorem U_S_continuous_triple :
    Continuous (fun xas : ℝ × ℝ × ℝ => G.U_S xas.1 xas.2.1 xas.2.2) := by
  simp only [U_S]; fun_prop

/-- Continuity of the derived Target payoff on `ℝ³`. -/
theorem U_T_continuous_triple :
    Continuous (fun xas : ℝ × ℝ × ℝ => G.U_T xas.1 xas.2.1 xas.2.2) := by
  simp only [U_T]; fun_prop


/-- **Build an `AbstractGame.Params` from a four-group polity under a GENERAL
transition law.** The stage payoffs `U_S`, `U_T` are the group-derived
Grossman-Helpman weighted sums; the static Sender selector `σ` is the clipped
vertex (Rule-1 coupling, *derived* via `sigmaSel_isMaxOn`). The transition `F`
and its five structural obligations are supplied by the caller, so nothing in
this constructor commits the polity to a functional form (Rule 22).

Thirteen of the eighteen `Params` fields come from the four-group primitives or
are free numeric inputs; the five transition fields are the caller's. The
selector's continuity is not a field since round BJ5.1 (2026-10-07): it is the
instance `toParamsF_staticSelectorContinuous` below. No field
outside the transition block mentions `F`, so every declaration in this file
that reads only `U_S`, `U_T` or `σ` transfers verbatim — in particular all six
derived stage complementarities (`U_S_senderStageID`, `U_T_targetStageID`,
`U_S_senderActionDD`, the two strict variants, and
`U_S_senderChordConcaveInS`).

`δ` remains a `Params` field but is inert here: nothing in `Params` connects it
to a caller-supplied `F` (see the `Params.δ` docstring). The affine law is one
member of this family, exhibited as `toParams` in
`Examples/AffineInstance/Microfoundations.lean`; that it is the `affineF δ`
member is `toParamsF_affineF`. -/
noncomputable def toParamsF (δ β_T β_S : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hβT : β_T ∈ Set.Ico (0 : ℝ) 1)
    (hβS : β_S ∈ Set.Ico (0 : ℝ) 1)
    (F : ℝ → ℝ → ℝ)
    (hF_continuous : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x) :
    Sanctions.AbstractGame.Params where
  δ := δ
  δ_mem := hδ
  β_T := β_T
  β_T_mem := hβT
  β_S := β_S
  β_S_mem := hβS
  U_T := G.U_T
  U_S := G.U_S
  σ := G.sigmaSel
  σ_mem := G.sigmaSel_mem
  σ_isMaxOn_U_S := G.sigmaSel_isMaxOn
  U_T_continuous := G.U_T_continuous_triple
  U_S_continuous := G.U_S_continuous_triple
  F := F
  F_continuous := hF_continuous
  F_mono_x := hF_mono_x
  F_mono_s := hF_mono_s
  F_diag := hF_diag

/-- **The four-group economy's static Sender selector is continuous.** The
clipped vertex `sigmaSel` is jointly continuous in the state and the compliance
level (`sigmaSel_continuous`), so every economy `toParamsF` builds carries the
static-selector instance, whatever the transition. General in `F`. Until round
BJ5.1 (2026-10-07) this was the `σ_continuous` field of `toParamsF`. -/
instance toParamsF_staticSelectorContinuous (δ β_T β_S : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hβT : β_T ∈ Set.Ico (0 : ℝ) 1)
    (hβS : β_S ∈ Set.Ico (0 : ℝ) 1)
    (F : ℝ → ℝ → ℝ)
    (hF_continuous : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x) :
    (G.toParamsF δ β_T β_S hδ hβT hβS F hF_continuous hF_mono_x hF_mono_s
      hF_diag).StaticSelectorContinuous :=
  ⟨G.sigmaSel_continuous⟩

/-! ### The hawk-rescaling family (BH6.1, 2026-10-07)

Multiply the pro-sanction coalition's per-unit benefit by `k ≠ 0` and divide its
political-weight schedule by the same `k`: `g_J ↦ k·g_J`, `θ⁰_{J_S} ↦ θ⁰_{J_S}/k`,
`ν ↦ ν/k`. The hawks' effective weight times benefit, `(θ⁰_{J_S} + ν·x)·g_J`, is
unchanged, so both governments' stage payoffs, the static Sender selector and the
induced `Params` are the same for every transition; region (R) survives
(`ν·g_J` is unchanged and no other region field moves). Only the unit-weight
planner, who counts `g_J·s` at weight one, sees a difference
(`hawkRescale_plannerW` and the gap shift in `FourGroupPlanner.lean`). The
certificate polity's welfare refutation `fourGroupCertHawkScaled` is the member
`k = 5` (`Examples/FourGroupWelfareSign.lean`). General in `F`. -/

/-- **The hawk-rescaled polity** (BH6.1; general in `F`, the polity carries no
transition): `G` with `g_J := k·g_J`, `θ⁰_{J_S} := θ⁰_{J_S}/k`, `ν := ν/k`, every
other coefficient and every region field unchanged. The only hypothesis is
`k ≠ 0`, which the division needs; no sign of `k` is assumed. -/
noncomputable def hawkRescale (k : ℝ) (hk : k ≠ 0) : FourGroup :=
  { G with
    th0_JS := G.th0_JS / k
    nu := G.nu / k
    g_J := k * G.g_J
    senderRally_pos := by
      have h : G.nu / k * (k * G.g_J) = G.nu * G.g_J := by field_simp
      rw [h]
      exact G.senderRally_pos }

/-- The hawks' effective weight times benefit is invariant under the rescaling:
`(θ⁰_{J_S}/k + (ν/k)·x)·(k·g_J) = (θ⁰_{J_S} + ν·x)·g_J`. -/
theorem hawkRescale_weight (k : ℝ) (hk : k ≠ 0) (x : ℝ) :
    ((G.hawkRescale k hk).th0_JS + (G.hawkRescale k hk).nu * x) * (G.hawkRescale k hk).g_J
      = (G.th0_JS + G.nu * x) * G.g_J := by
  simp only [hawkRescale]
  field_simp

/-- **The rescaled polity's Sender payoff is unchanged** (general in `F`). -/
theorem hawkRescale_U_S (k : ℝ) (hk : k ≠ 0) : (G.hawkRescale k hk).U_S = G.U_S := by
  funext x a s
  simp only [U_S]
  rw [G.hawkRescale_weight k hk x]
  rfl

/-- **The rescaled polity's Target payoff is unchanged** (no Target coefficient
moves; general in `F`). -/
theorem hawkRescale_U_T (k : ℝ) (hk : k ≠ 0) : (G.hawkRescale k hk).U_T = G.U_T := rfl

/-- **The rescaled polity's static Sender selector is unchanged.** -/
theorem hawkRescale_sigmaSel (k : ℝ) (hk : k ≠ 0) :
    (G.hawkRescale k hk).sigmaSel = G.sigmaSel := by
  funext x a
  simp only [sigmaSel]
  rw [G.hawkRescale_weight k hk x]
  rfl

/-- **The rescaled polity induces the same game, under every transition**
(BH6.1; general in `F`): for every `δ`, discount pair and transition `F` with
its five structural obligations, `toParamsF` of the rescaled polity is
`toParamsF` of `G`. So every equilibrium of either game is an equilibrium of the
other, verbatim. -/
theorem hawkRescale_toParamsF (k : ℝ) (hk : k ≠ 0) (δ β_T β_S : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hβT : β_T ∈ Set.Ico (0 : ℝ) 1)
    (hβS : β_S ∈ Set.Ico (0 : ℝ) 1)
    (F : ℝ → ℝ → ℝ)
    (hF_continuous : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x) :
    (G.hawkRescale k hk).toParamsF δ β_T β_S hδ hβT hβS F hF_continuous hF_mono_x
        hF_mono_s hF_diag
      = G.toParamsF δ β_T β_S hδ hβT hβS F hF_continuous hF_mono_x hF_mono_s hF_diag := by
  unfold toParamsF
  congr 1
  · exact G.hawkRescale_U_S k hk
  · exact G.hawkRescale_sigmaSel k hk

end FourGroup
end KaempferLowenberg
end Sanctions
