/-
Sanctions/Examples/SymbolicCertifiedFamilyGeneralF.lean

**The certified family, carrying a general transition.**

`SymbolicEconomy` (`SymbolicCertifiedFamily.lean`) constructs its transition:
`F := affineF δ`. Because the family pins the Sender at the sanction corner,
its realised recursion is `x' = F(x,1)` — so that construction makes the
certified *dynamics* affine, whatever the incentive layer quantifies over.

`SymbolicEconomyF` below **carries** the transition instead. `F` and four of
its `Params` obligations are fields (`F_mem` is a theorem); the transition's regularity enters only
through chord predicates, never through a functional form. The realised
recursion is therefore as general as `F` is, and the family contains members
whose dynamics are provably non-affine.

`SymbolicEconomy` is untouched, and embeds
(`SymbolicCertifiedFamilyGeneralFEmbedding.lean`) as the degenerate member
with `glo = ghi = 1 − δ` and `dlo = δ`.

## The persistence core (plan item BJ4.4, 2026-10-07)

`SymbolicEconomyFPersist` is the same family with the Target's three
conditions `0 ≤ n`, `ℓ ≤ c − n` and the loss-offset margin `hTMargin`
replaced by the single sign condition `0 ≤ n + v`. The carriers, their
Bellman invariance and the compliance-local Sender argmax uniqueness read
nothing else on the Target side, so they are proved once, on the core (§2–§7),
and `SymbolicEconomyF` reads them through `SymbolicEconomyF.toPersist` (§7a).
The definitions `SymbolicEconomyF.carrierS`, `KS`, `toParams`, … keep their own
bodies, so the BJ4.4 split changed no statement about `SymbolicEconomyF`; plan
item BJ4.3 then removed the curvature block, which changed the carrier (the gain
ball alone) and the statements that named the removed fields.

## What the band costs, and why no curvature bound is needed

Removing the corner *equality* costs the slope pin, so the carrier becomes a
genuine cone (`g_S < K_S`) and the value is no longer determined. Sender argmax
uniqueness at physical compliance `a ∈ [0,1]` does not need the value: for every
carrier member the Sender's dynamic objective is strictly increasing in the
sanction (`senderObj_strictMonoOn`, from the carrier's lower slope `g_S`, the
sanction lower chord `dlo` and `hCorner`), so its unique maximiser is the full
sanction (`DAUOnI_on_cone`).

**The curvature block is gone (plan item BJ4.3, 2026-10-08).** Until then the
structure bought uniqueness at *every real* compliance level with an upper
sanction chord `dhi`, curvature ceilings `M_F` (sanction direction) and
`M_state` (corner section), the curvature margin `hCurv` and a Riccati
semiconcavity clause in the carrier; the price was the cap `M_F < dlo/2`, which
excluded the wobble file's own published transition. The value-class route
reads uniqueness only at `a ∈ [0,1]`, so the block, the clause and the cap are
deleted. The family now admits strongly curved transitions, including
`wobbleF (1/2) (1/10)` (§10). The semiconcavity conclusion survives as
`persistence_generalF_semiconcave`, with the state curvature supplied as a
hypothesis.

## Which band rate each margin is priced at

Once the corner equality becomes a two-sided band, `glo` and `ghi` are
different numbers and a margin priced at one is not the same condition as the
same margin priced at the other.  Each field is therefore stated at **its own
stronger rate**, and the other reading is derived:

| field | priced at | why that is the stronger reading | derived reading |
|---|---|---|---|
| `hCorner`  | `glo` | band rate multiplies a positive coefficient on the LEFT of `<` | `hCorner_ghi` |
| `hTMargin` | `glo` | band rate multiplies a positive coefficient on the LEFT of `≤` | `hTMargin_ghi` |

Economically, `glo` is the rate at which a carrier value's continuation gain
is guaranteed from **below** — `g_S = (r+w)/(1 − β_S·glo)` — so it is the rate
the corner argument may actually spend, whereas `ghi` gives the Lipschitz
constant `K_S`, an upper bound.  Pricing `hCorner` at `glo` is what makes
`corner_margin_lo` a theorem instead of an extra hypothesis, and it is why the
MS certificate no longer takes any margin argument.

**The Sender stage margin and the sanction floor are gone (plan item BJ4.1,
2026-10-07).** The structure used to carry a third margin, `hSMargin`
(`β_S·dlo·(r+w) < (u₀ + r·x̄ − q·s̄)(1 − β_S·ghi)`), with a floor parameter
`s̄` and `x̄ ≤ s̄`, `0 < s̄ < 1`. It fed only the strict stage monotonicity of
the Sender on the MS sanction range `[0, max x x̄] = [0, x]`, and that already
follows from `u₀ > 0` and `q ≤ r`. So `hSMargin`, `s̄`, `x̄ ≤ s̄` and `0 < s̄` are
deleted and `s̄ < 1` becomes `x̄ < 1`. The chain `m_S > 0`, `q + k − u₀ < m_S`,
`q < u₀` that the two Sender margins used to give is deleted with them. The
positive corner payoff (`cornerStagePayoff_pos`) survives: it now follows from
`hCorner` alone and the chord fact `dlo + glo ≤ 1` (`wedge_lt_stageSlope`).

**Three fields became theorems (plan item BJ4.2).** `F_mem` follows from
monotonicity and the diagonal, `glo ≤ ghi` from the band itself, and the field
`0 < dlo` is weakened to `0 ≤ dlo`, because strictness follows from `hCorner`
(`dlo_pos`).

## READ THIS BEFORE CLASSIFYING ANYTHING IN THIS FILE (audit note)

**The results here are universals over a family, not witness instances.** They
are quantified over the symbolic economy variable declared below -- every
admissible member -- so they license universal statements about the family, and
Rule 9's "a witness proves only existence" restriction does **not** apply to
them.

The file sits under `Examples/` because the family fixes a *functional form* for
the stage payoffs, not because its theorems are point checks. Rule 19 keeps
`Theory/` for statements over an arbitrary `Params`; a coefficient-parameterised
algebraic family is narrower than that, so `Examples/` is the correct home and
the file is deliberately not moved.

This banner exists because the filing has already misled an audit. A 2026-08-16
review classified `prop:equilibrium-patience-feedback` as a paper universal
backed only by a witness, having found the numeric `eeCertB_*` names cited in
the formalization map and not the `symbolic_*` siblings in this cluster. The
paper was right and the audit was wrong. If you are deciding what a paper claim
rests on, grep this cluster before concluding that a family-level claim has only
witness backing.
-/

import Sanctions.Examples.SymbolicCertifiedFamily
import Sanctions.Theory.Bellman.ChordInvariance
import Sanctions.Foundations.SemiconcaveRiccati
import Sanctions.Theory.Basin.TransitionChords
import Sanctions.Examples.WobbleCornerCertWitness
import Sanctions.Examples.AffineInstance.TransitionChords

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params Sanctions.TransitionChords Sanctions.Semiconcave

noncomputable section

/-! ## 0. The derived closed-form constants, as plain functions of the rates

Each is one of the project's own closed forms, evaluated at the family's own
primitives — nothing here is chosen. (The Riccati modulus `symSigV` of the
retired curvature margin was deleted with it, plan item BJ4.3.) -/

/-- Sender value Lipschitz constant, `K_S = (r + w)/(1 − β_S·ghi)`:
`StokeyLucas.bellmanLipConstant` at the corner band's UPPER rate. -/
def symKS (βS ghi r w : ℝ) : ℝ :=
  StokeyLucas.bellmanLipConstant βS ghi (r + w)

/-- Sender value lower state-slope, `g_S = (r + w)/(1 − β_S·glo)`:
`StokeyLucas.bellmanLowerSlopeConstant` at the band's LOWER rate.  With
`glo < ghi` this is strictly below `K_S`, so the carrier is a genuine cone. -/
def symGS (βS glo r w : ℝ) : ℝ :=
  StokeyLucas.bellmanLowerSlopeConstant βS glo (r + w)

/-! ## 1. The structure -/

/-- **An admissible member of the general-transition symbolic family.**

Deviations from `SymbolicEconomy`, and why:

* the transition `F` and four of its `Params` obligations are **carried**, not
  built from `δ` (`F_mem` is derived from monotonicity and the diagonal);
* three rate fields `glo ghi dlo` and two chord predicates: the two-sided corner
  band `CornerStateChord F glo ghi` and the sanction lower chord
  `SanctionLowerChord F dlo`;
* `δ` survives as a field only to fill the `Params.δ` slot (`Params` requires
  `δ ∈ (0,1)`).  It does **not** define the transition — exactly as
  `wobbleParams` keeps `eeCertParams.δ = 1/2` beside the wobble law.

Two of the affine family's three margins, implacability `hCorner` and the
Target loss offset `hTMargin`, are restated with a band rate in place of
`1 − δ` and `dlo` in place of `δ`. The third, the Sender
stage margin, is not carried, and neither is the sanction floor `s̄` (plan item
BJ4.1, 2026-10-07): the basin bottom only has to lie below the top state,
`hxb1 : x̄ < 1`.

**Deleted fields (plan item BJ4.3, 2026-10-08).** The upper sanction chord rate
`dhi` with `hShi : SanctionUpperChord F dhi`, the sanction curvature ceiling
`MF` with `hFsc : SanctionSemiconcave F MF`, the corner-section curvature
ceiling `Mstate` with `hGsc`, their signs `hMF0`, `hMstate0`, and the curvature
margin `hCurv`. They fed only the all-real-compliance argmax uniqueness
`DAU_on_cone` and the carrier's semiconcavity clause; Sender uniqueness at
physical compliance follows from strict monotonicity in the sanction
(`DAUOnI_on_cone`). Economically: there is no bound on how curved the
transition is; a marginal sanction must only move the state by at least `dlo`
per unit, and the corner section must stay in its band.

Three conditions are theorems rather than fields (plan item BJ4.2): `F_mem`
(the transition maps the square into `[0,1]`, from monotonicity and the
diagonal), `hglo_ghi` (`glo ≤ ghi`, from the band), and `dlo_pos` (`0 < dlo`,
from `hCorner`; the field is the weaker `0 ≤ dlo`). General in `F`. -/
structure SymbolicEconomyF where
  /-- The transition law, carried. -/
  F : ℝ → ℝ → ℝ
  F_continuous : Continuous (fun (xs : ℝ × ℝ) => F xs.1 xs.2)
  F_mono_x : ∀ s, Monotone (fun x => F x s)
  F_mono_s : ∀ x, Monotone (fun s => F x s)
  F_diag : ∀ x, F x x = x
  /-- Corner-section state band, lower rate. -/
  glo : ℝ
  /-- Corner-section state band, upper rate. -/
  ghi : ℝ
  /-- Sanction-direction lower chord rate. -/
  dlo : ℝ
  hband : CornerStateChord F glo ghi
  hSlo : SanctionLowerChord F dlo
  hglo0 : 0 ≤ glo
  hghi1 : ghi ≤ 1
  /-- The sanction chord's lower rate is nonnegative. Weakened from `0 < dlo`
  (plan item BJ4.2): strict positivity is the theorem `dlo_pos`, forced by
  `hCorner`. -/
  hdlo0 : 0 ≤ dlo
  /-- Legacy `Params.δ` slot; the realised law is `F`, not `affineF δ`. -/
  δ : ℝ
  βS : ℝ
  βT : ℝ
  q : ℝ
  u₀ : ℝ
  k : ℝ
  r : ℝ
  w : ℝ
  ℓ : ℝ
  c : ℝ
  n : ℝ
  v : ℝ
  xb : ℝ
  hδ0 : 0 < δ
  hδ1 : δ < 1
  hβS0 : 0 ≤ βS
  hβS1 : βS < 1
  hβT0 : 0 ≤ βT
  hβT1 : βT < 1
  hq : 0 < q
  hqr : q ≤ r
  hu₀ : 0 < u₀
  hk : u₀ + r ≤ k
  hn : 0 ≤ n
  hℓ : 0 < ℓ
  hcn : ℓ ≤ c - n
  hxb0 : 0 ≤ xb
  /-- The basin bottom lies strictly below the top state. Replaces the floor
  block `x̄ ≤ s̄`, `0 < s̄`, `s̄ < 1` (plan item BJ4.1), which it is implied
  by. -/
  hxb1 : xb < 1
  /-- **Implacability**, priced against the band's **lower** rate `glo` and the
  sanction chord's lower rate `dlo`.

  `glo` is the rate at which a carrier value's continuation gain is guaranteed
  from *below*, so it is the rate the corner argument may actually spend.
  Since `glo ≤ ghi` makes `1 − β_S·glo ≥ 1 − β_S·ghi`, this is the **stronger**
  of the two readings; the `ghi` reading is derived as `hCorner_ghi`. -/
  hCorner : (q + k - u₀) * (1 - βS * glo) < βS * dlo * (r + w)
  /-- **Target loss offset**, priced against the band's **lower** rate `glo`.

  As with `hCorner` the band rate sits on the left of a `≤`, so `glo` is the
  stronger reading; `hTMargin_ghi` derives the `ghi` one. -/
  hTMargin : (c - n * xb) * (1 - βT * glo) ≤ βT * dlo * (n + v)

/-! ## 1a. The persistence core -/

/-- **The persistence core of the general-transition family** (plan item BJ4.4,
2026-10-07).

Every field of `SymbolicEconomyF` except the Target's three conditions, which
are replaced by one sign condition. Dropped: `hn : 0 ≤ n` (the Target's
sanction pain does not grow as the state rises), `hcn : ℓ ≤ c − n` (a unit of
compliance costs no more than the sanction pain) and the loss-offset margin
`hTMargin` (the Target's stage sanction loss is covered by its discounted
continuation gain). Added: `hnv : 0 ≤ n + v`, the Target's corner stage payoff
`U_T(y, 0, 1) = −c + (n + v)·y` does not fall as the state rises. General in
`F`: the transition enters only through the same chord fields. Like
`SymbolicEconomyF`, it carries no curvature block since plan item BJ4.3.

Persistence reads nothing else on the Target side. Under the corner sanction
the Target's compliance only costs `ℓ` per unit and buys nothing, so full
defiance is its unique argmax once `ℓ > 0`; and the Target carrier is a
nonempty invariant cone once its lower slope `(n + v)/(1 − β_T·glo)` is
nonnegative. Every `SymbolicEconomyF` is a member (`SymbolicEconomyF.toPersist`,
which derives `hnv` from the three dropped conditions). The converse fails: a
Target whose sanction pain is too large for the loss offset is a core member
(`wobbleEconPersist`, in the persistence file). -/
structure SymbolicEconomyFPersist where
  /-- The transition law, carried. -/
  F : ℝ → ℝ → ℝ
  F_continuous : Continuous (fun (xs : ℝ × ℝ) => F xs.1 xs.2)
  F_mono_x : ∀ s, Monotone (fun x => F x s)
  F_mono_s : ∀ x, Monotone (fun s => F x s)
  F_diag : ∀ x, F x x = x
  /-- Corner-section state band, lower rate. -/
  glo : ℝ
  /-- Corner-section state band, upper rate. -/
  ghi : ℝ
  /-- Sanction-direction lower chord rate. -/
  dlo : ℝ
  hband : CornerStateChord F glo ghi
  hSlo : SanctionLowerChord F dlo
  hglo0 : 0 ≤ glo
  hghi1 : ghi ≤ 1
  hdlo0 : 0 ≤ dlo
  /-- Legacy `Params.δ` slot; the realised law is `F`, not `affineF δ`. -/
  δ : ℝ
  βS : ℝ
  βT : ℝ
  q : ℝ
  u₀ : ℝ
  k : ℝ
  r : ℝ
  w : ℝ
  ℓ : ℝ
  c : ℝ
  n : ℝ
  v : ℝ
  xb : ℝ
  hδ0 : 0 < δ
  hδ1 : δ < 1
  hβS0 : 0 ≤ βS
  hβS1 : βS < 1
  hβT0 : 0 ≤ βT
  hβT1 : βT < 1
  hq : 0 < q
  hqr : q ≤ r
  hu₀ : 0 < u₀
  hk : u₀ + r ≤ k
  hℓ : 0 < ℓ
  /-- **The core's only Target-side sign condition**: the Target's corner stage
  payoff does not fall as the state rises. It replaces `hn`, `hcn` and
  `hTMargin` of `SymbolicEconomyF`, which imply it
  (`SymbolicEconomyF.stageSlopeT_pos`). -/
  hnv : 0 ≤ n + v
  hxb0 : 0 ≤ xb
  hxb1 : xb < 1
  /-- **Implacability**, priced at the band's lower rate `glo`, exactly as in
  `SymbolicEconomyF`. -/
  hCorner : (q + k - u₀) * (1 - βS * glo) < βS * dlo * (r + w)

namespace SymbolicEconomyF

variable (E : SymbolicEconomyF)

/-! ### 1b. Two former fields, now theorems, and the map into the core -/

/-- **The transition maps the square into `[0,1]`.** A field until plan item
BJ4.2 (2026-10-07). A map nondecreasing in each argument that fixes the
diagonal sends the unit square into `[0,1]`, because `F x s` lies between `x`
and `s`. General in `F`. -/
theorem F_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
    E.F x s ∈ Set.Icc (0 : ℝ) 1 :=
  fun _ _ hx hs => Sanctions.mem_Icc_of_mono_of_diag E.F_mono_x E.F_mono_s E.F_diag hx hs

/-- **The corner band's rates are ordered**, `glo ≤ ghi`. A field until plan
item BJ4.2 (2026-10-07). Between the states `0` and `1` the band reads
`glo ≤ F(1,1) − F(0,1) ≤ ghi`. General in `F`. -/
theorem hglo_ghi : E.glo ≤ E.ghi := E.hband.rates_le

/-- **Derived**: the Target's corner stage payoff has positive state slope,
`0 < n + v`. The left side of the loss offset `hTMargin`,
`(c − n·x̄)(1 − β_T·glo)`, is positive (`ℓ ≤ c − n`, `0 ≤ n`, `x̄ < 1`), so
`β_T·dlo·(n + v) > 0`, while `β_T·dlo ≥ 0`. Proved straight from the fields,
because the map `toPersist` below needs it. -/
theorem stageSlopeT_pos : 0 < E.n + E.v := by
  have hΛ : 0 < 1 - E.βT * E.glo := by
    nlinarith [mul_le_mul_of_nonneg_left (le_trans E.hglo_ghi E.hghi1) E.hβT0, E.hβT1]
  have hcT : 0 < E.c - E.n * E.xb := by
    nlinarith [mul_nonneg E.hn (sub_nonneg.mpr E.hxb1.le), E.hcn, E.hℓ]
  have hpos : 0 < E.βT * E.dlo * (E.n + E.v) :=
    lt_of_lt_of_le (mul_pos hcT hΛ) E.hTMargin
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [mul_nonneg E.hβT0 E.hdlo0]

/-- **Every member of the family is a member of its persistence core** (plan
item BJ4.4). The map forgets the Target's three conditions `hn` (`0 ≤ n`), `hcn`
(`ℓ ≤ c − n`) and `hTMargin` (the loss offset) and keeps their consequence
`0 ≤ n + v`; every other field is copied. So the core's `Params`, carriers and
certificates at `E.toPersist` are definitionally those of `E`
(`toPersist_toParams`, `toPersist_carrierS`). General in `F`. -/
def toPersist : SymbolicEconomyFPersist where
  F := E.F
  F_continuous := E.F_continuous
  F_mono_x := E.F_mono_x
  F_mono_s := E.F_mono_s
  F_diag := E.F_diag
  glo := E.glo
  ghi := E.ghi
  dlo := E.dlo
  hband := E.hband
  hSlo := E.hSlo
  hglo0 := E.hglo0
  hghi1 := E.hghi1
  hdlo0 := E.hdlo0
  δ := E.δ
  βS := E.βS
  βT := E.βT
  q := E.q
  u₀ := E.u₀
  k := E.k
  r := E.r
  w := E.w
  ℓ := E.ℓ
  c := E.c
  n := E.n
  v := E.v
  xb := E.xb
  hδ0 := E.hδ0
  hδ1 := E.hδ1
  hβS0 := E.hβS0
  hβS1 := E.hβS1
  hβT0 := E.hβT0
  hβT1 := E.hβT1
  hq := E.hq
  hqr := E.hqr
  hu₀ := E.hu₀
  hk := E.hk
  hℓ := E.hℓ
  hnv := E.stageSlopeT_pos.le
  hxb0 := E.hxb0
  hxb1 := E.hxb1
  hCorner := E.hCorner

/-! ### Carrier helpers that do not depend on the economy

Shared by the core and the family, and cited by name from the placable and
chord families. -/

/-- `affineBCF c ∈ valLipGainBall M K c 0` for `0 ≤ c ≤ K`, `c ≤ M`.  The
cone version of `affineBCF_mem_gainBall`, which pins `g = K`. -/
theorem affineBCF_mem_gainBall_cone {c K M : ℝ}
    (hc : 0 ≤ c) (hcK : c ≤ K) (hcM : c ≤ M) :
    affineBCF c ∈ valLipGainBall M K c 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BoundedContinuousFunction.norm_le (le_trans hc hcM)]
    intro y
    rw [affineBCF_apply, Real.norm_eq_abs, abs_le]
    exact ⟨by nlinarith [y.property.1, y.property.2],
      by nlinarith [y.property.1, y.property.2]⟩
  · intro y₁ y₂
    rw [affineBCF_apply, affineBCF_apply, Subtype.dist_eq, Real.dist_eq]
    rcases le_total y₁.val y₂.val with h | h
    · rw [abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ c * y₂.val - c * y₁.val),
        abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
      nlinarith
    · rw [abs_of_nonpos (by nlinarith : c * y₂.val - c * y₁.val ≤ 0),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ y₁.val - y₂.val)]
      nlinarith
  · intro y₁ y₂ _ _ hle
    have hle' : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
    rw [affineBCF_apply, affineBCF_apply, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
    nlinarith [hle']

/-- A linear value is semiconcave through the clip with any nonnegative
modulus (its chord defect on `[0,1]` is exactly zero). -/
theorem affineBCF_clip_semiconcave {c σ : ℝ} (hσ : 0 ≤ σ) :
    SemiconcaveOnSet (fun z => affineBCF c (Sanctions.clipS' z))
      (Set.Icc (0 : ℝ) 1) σ := by
  intro z₁ hz₁ z₂ hz₂ t ht0 ht1
  have hm : t * z₁ + (1 - t) * z₂ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hz₁.1, hz₂.1], by nlinarith [hz₁.2, hz₂.2]⟩
  have hP : (0 : ℝ) ≤ t * (1 - t) * (z₁ - z₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  show t * (affineBCF c (Sanctions.clipS' z₁))
      + (1 - t) * (affineBCF c (Sanctions.clipS' z₂))
      - affineBCF c (Sanctions.clipS' (t * z₁ + (1 - t) * z₂))
    ≤ σ / 2 * (t * (1 - t) * (z₁ - z₂) ^ 2)
  rw [affineBCF_apply, affineBCF_apply, affineBCF_apply,
    Sanctions.clipS'_val_eq_of_mem hz₁, Sanctions.clipS'_val_eq_of_mem hz₂,
    Sanctions.clipS'_val_eq_of_mem hm]
  nlinarith [mul_nonneg hσ hP]

end SymbolicEconomyF

namespace SymbolicEconomyFPersist

variable (E : SymbolicEconomyFPersist)

/-! ## 2. Elementary derived facts (on the persistence core)

From here to the end of §7 every declaration is stated for the core
`SymbolicEconomyFPersist`, and §7a reads each one back for `SymbolicEconomyF`
through `toPersist`. Nothing in §2–§7 reads the Target beyond `0 ≤ n + v` and
`0 < ℓ`. General in `F` throughout. -/

/-- The transition maps the square into `[0,1]`: monotonicity in each argument
and the fixed diagonal. -/
theorem F_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
    E.F x s ∈ Set.Icc (0 : ℝ) 1 :=
  fun _ _ hx hs => Sanctions.mem_Icc_of_mono_of_diag E.F_mono_x E.F_mono_s E.F_diag hx hs

/-- `glo ≤ ghi`, read off the band between the states `0` and `1`. -/
theorem hglo_ghi : E.glo ≤ E.ghi := E.hband.rates_le

theorem ghi_nn : 0 ≤ E.ghi := le_trans E.hglo0 E.hglo_ghi

theorem ΛS_pos : 0 < 1 - E.βS * E.ghi := by
  have h := mul_le_mul_of_nonneg_left E.hghi1 E.hβS0
  rw [mul_one] at h
  linarith [E.hβS1]

theorem ΛT_pos : 0 < 1 - E.βT * E.ghi := by
  have h := mul_le_mul_of_nonneg_left E.hghi1 E.hβT0
  rw [mul_one] at h
  linarith [E.hβT1]

theorem ΛgloS_pos : 0 < 1 - E.βS * E.glo := by
  have h := mul_le_mul_of_nonneg_left E.hglo_ghi E.hβS0
  linarith [E.ΛS_pos]

theorem ΛgloT_pos : 0 < 1 - E.βT * E.glo := by
  have h := mul_le_mul_of_nonneg_left E.hglo_ghi E.hβT0
  linarith [E.ΛT_pos]

/-- The band's two discount wedges are ordered: `1 − β_S·ghi ≤ 1 − β_S·glo`. -/
theorem ΛS_le_ΛgloS : 1 - E.βS * E.ghi ≤ 1 - E.βS * E.glo := by
  linarith [mul_le_mul_of_nonneg_left E.hglo_ghi E.hβS0]

theorem ΛT_le_ΛgloT : 1 - E.βT * E.ghi ≤ 1 - E.βT * E.glo := by
  linarith [mul_le_mul_of_nonneg_left E.hglo_ghi E.hβT0]

theorem Θ_pos : 0 < 1 - E.βS * E.ghi ^ 2 := by
  have h := semiconcave_contract_of_le_one E.hβS0 E.hβS1 E.ghi_nn E.hghi1
  linarith

theorem r_pos : 0 < E.r := lt_of_lt_of_le E.hq E.hqr

theorem k_pos : 0 < E.k := by linarith [E.hk, E.hu₀, E.r_pos]

theorem xb_le_one : E.xb ≤ 1 := E.hxb1.le

/-- The worst stage disincentive the Sender can face is strictly positive. -/
theorem wedge_pos : 0 < E.q + E.k - E.u₀ := by linarith [E.hk, E.hq, E.r_pos]

/-! ### The two readings of implacability

`hCorner` carries the band rate on the *left* of the inequality against a
positive coefficient, so lowering the rate (to `glo`) enlarges the left side
and strengthens the claim. The weaker `ghi` reading is a theorem. -/

/-- **Implacability at the band's UPPER rate** — the weaker reading, derived
from the field's `glo` reading. -/
theorem hCorner_ghi :
    (E.q + E.k - E.u₀) * (1 - E.βS * E.ghi) < E.βS * E.dlo * (E.r + E.w) :=
  lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left E.ΛS_le_ΛgloS E.wedge_pos.le) E.hCorner

theorem βS_dlo_pos : 0 < E.βS * E.dlo := by
  rcases (mul_nonneg E.hβS0 E.hdlo0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hC := E.hCorner_ghi
    rw [← h, zero_mul] at hC
    linarith [mul_pos E.wedge_pos E.ΛS_pos]

/-- **Derived**: the sanction chord's lower rate is strictly positive. Since
`β_S·dlo > 0` and `β_S ≥ 0`, the field `hdlo0 : 0 ≤ dlo` loses nothing against
the old `0 < dlo` (plan item BJ4.2). -/
theorem dlo_pos : 0 < E.dlo := by
  by_contra h
  rw [not_lt] at h
  nlinarith [E.βS_dlo_pos, E.hβS0]

/-- **Derived, not assumed**: the Sender's corner stage payoff has strictly
positive state slope `r + w`.  Falls out of `hCorner`. -/
theorem stageSlope_pos : 0 < E.r + E.w := by
  have h2 : 0 < E.βS * E.dlo * (E.r + E.w) :=
    lt_trans (mul_pos E.wedge_pos E.ΛS_pos) E.hCorner_ghi
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [E.βS_dlo_pos]

/-! ### Implacability caps the stage disincentive by the state slope

Plan items BJ4.1 and BJ4.6. These replace the chain `m_S > 0`,
`q + k − u₀ < m_S`, `q < u₀` that the deleted Sender stage margin used to give:
the positive corner payoff now follows from `hCorner` alone. -/

/-- **The sanction responsiveness and the corner band split one unit of
adjustment**: `dlo + glo ≤ 1`. At the state `0` a full sanction moves the state
by at least `dlo` (`F(0,1) − F(0,0) ≥ dlo`, and `F(0,0) = 0`), and along the
corner section the gap between the states `0` and `1` closes by at least `glo`
(`F(1,1) − F(0,1) ≥ glo`, and `F(1,1) = 1`). The band analogue of
`sanctionLowerChord_le_of_cornerTop`. General in `F`. -/
theorem dlo_add_glo_le_one : E.dlo + E.glo ≤ 1 := by
  have h1 := E.hSlo (x := 0) (s₁ := 0) (s₂ := 1) ⟨le_rfl, zero_le_one⟩
    ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  have h2 := (E.hband (y₁ := 0) (y₂ := 1) ⟨le_rfl, zero_le_one⟩
    ⟨zero_le_one, le_rfl⟩ zero_le_one).1
  have h00 : E.F 0 0 = 0 := E.F_diag 0
  have h11 : E.F 1 1 = 1 := E.F_diag 1
  linarith

/-- The continuation multiplier of a marginal sanction is at most one:
`β_S·dlo ≤ 1 − β_S·glo`, from `dlo + glo ≤ 1` and `β_S < 1`. -/
theorem βS_dlo_le_ΛgloS : E.βS * E.dlo ≤ 1 - E.βS * E.glo := by
  have h := mul_le_mul_of_nonneg_left E.dlo_add_glo_le_one E.hβS0
  linarith [E.hβS1]

/-- **Implacability caps the worst stage disincentive by the corner state
slope**: `q + k − u₀ < r + w`. `hCorner` prices the disincentive against the
discounted continuation gain `β_S·dlo·(r + w)/(1 − β_S·glo)`, and the
multiplier `β_S·dlo/(1 − β_S·glo)` is at most one (`βS_dlo_le_ΛgloS`).
Economically: a marginal sanction moves next period's state by less than one
unit of the corner band, so its discounted continuation gain cannot exceed one
period's state benefit `r + w`, and implacability needs that benefit above the
worst stage disincentive. General in `F`. -/
theorem wedge_lt_stageSlope : E.q + E.k - E.u₀ < E.r + E.w := by
  have hle : E.βS * E.dlo * (E.r + E.w) ≤ (1 - E.βS * E.glo) * (E.r + E.w) :=
    mul_le_mul_of_nonneg_right E.βS_dlo_le_ΛgloS E.stageSlope_pos.le
  have h : (E.q + E.k - E.u₀) * (1 - E.βS * E.glo)
      < (E.r + E.w) * (1 - E.βS * E.glo) := by
    linarith [E.hCorner]
  exact lt_of_mul_lt_mul_right h E.ΛgloS_pos.le

/-! ## 3. Closed-form derived scalars -/

/-- Sender corner stage payoff intercept, `U_S(0, ·, 1) = u₀ − q/2`. -/
def stageS0 : ℝ := E.u₀ - E.q / 2

/-- Sender corner stage payoff state slope, `r + w`. -/
def stageSlopeS : ℝ := E.r + E.w

/-- Sup-norm of the Sender's corner stage payoff on the state space. -/
def stageNormS : ℝ := max |E.stageS0| |E.stageS0 + E.stageSlopeS|

/-- Target corner stage payoff state slope. -/
def stageSlopeT : ℝ := E.n + E.v

/-- Sender value Lipschitz constant (upper band rate). -/
def KS : ℝ := symKS E.βS E.ghi E.r E.w

/-- Sender value lower state-slope (lower band rate). -/
def gS : ℝ := symGS E.βS E.glo E.r E.w

/-- Target value state-slope. -/
def gT : ℝ := StokeyLucas.bellmanLipConstant E.βT E.ghi E.stageSlopeT

/-- Sender carrier radius. -/
def MS : ℝ := max (StokeyLucas.bellmanNormBound E.βS E.stageNormS) E.KS

theorem stageSlopeS_pos : 0 < E.stageSlopeS := E.stageSlope_pos

theorem KS_eq :
    E.KS = StokeyLucas.bellmanLipConstant E.βS E.ghi E.stageSlopeS := rfl

theorem gS_eq :
    E.gS = StokeyLucas.bellmanLowerSlopeConstant E.βS E.glo E.stageSlopeS := rfl

theorem KS_pos : 0 < E.KS := by
  rw [KS_eq, StokeyLucas.bellmanLipConstant]
  exact div_pos E.stageSlopeS_pos E.ΛS_pos

theorem gS_pos : 0 < E.gS := by
  rw [gS_eq, StokeyLucas.bellmanLowerSlopeConstant]
  exact div_pos E.stageSlopeS_pos E.ΛgloS_pos

/-- The Target's corner state slope is nonnegative: the core's field `hnv`. -/
theorem stageSlopeT_nn : 0 ≤ E.stageSlopeT := E.hnv

/-- The Target value state-slope is nonnegative (the core's analogue of
`SymbolicEconomyF.gT_pos`, which needs the dropped Target conditions). -/
theorem gT_nn : 0 ≤ E.gT := by
  simp only [gT, StokeyLucas.bellmanLipConstant]
  exact div_nonneg E.stageSlopeT_nn E.ΛT_pos.le

/-- **The carrier is a cone, not a slope-pinned ball**: `g_S ≤ K_S`, with
equality exactly when `glo = ghi` (or `β_S = 0`). -/
theorem gS_le_KS : E.gS ≤ E.KS := by
  rw [gS_eq, KS_eq, StokeyLucas.bellmanLowerSlopeConstant,
    StokeyLucas.bellmanLipConstant, div_le_div_iff₀ E.ΛgloS_pos E.ΛS_pos]
  nlinarith [mul_nonneg (mul_nonneg E.hβS0 (sub_nonneg.mpr E.hglo_ghi))
    E.stageSlopeS_pos.le]

theorem KS_le_MS : E.KS ≤ E.MS := le_max_right _ _

theorem gS_le_MS : E.gS ≤ E.MS := le_trans E.gS_le_KS E.KS_le_MS

/-- **The Riccati modulus at a supplied state curvature is nonnegative**:
`(β_S·K_S·M_state)/(1 − β_S·ghi²) ≥ 0` for `M_state ≥ 0`. The modulus of the
semiconcave sub-carrier of `persistence_generalF_semiconcave`; `M_state` is a
hypothesis, not a field (plan item BJ4.3, 2026-10-08). General in `F`. -/
theorem semiconcaveModulus_nn {Mstate : ℝ} (hMstate0 : 0 ≤ Mstate) :
    0 ≤ bellmanSemiconcaveConstant E.βS E.ghi 0 E.KS Mstate := by
  rw [bellmanSemiconcaveConstant]
  exact div_nonneg
    (by nlinarith [mul_nonneg (mul_nonneg E.hβS0 E.KS_pos.le) hMstate0])
    E.Θ_pos.le

/-! ### The Sender's margins, in value-slope form -/

/-- **Implacability**: `q + k − u₀ < β_S · dlo · K_S`. -/
theorem corner_margin : E.q + E.k - E.u₀ < E.βS * E.dlo * E.KS := by
  have hEq : E.βS * E.dlo * E.KS
      = E.βS * E.dlo * E.stageSlopeS / (1 - E.βS * E.ghi) := by
    rw [KS_eq, StokeyLucas.bellmanLipConstant]; ring
  rw [hEq, lt_div_iff₀ E.ΛS_pos]
  simpa only [stageSlopeS] using E.hCorner_ghi

/-- **Implacability in value-slope form at the carrier's guaranteed LOWER
continuation slope**: `q + k − u₀ < β_S · (g_S · dlo)`.

This is what the corner argument actually spends: a carrier member's gain from
a higher sanction is bounded *below* by `g_S = (r+w)/(1 − β_S·glo)`, not by the
Lipschitz constant `K_S`. It is a theorem because the structure prices
`hCorner` at `glo`. -/
theorem corner_margin_lo : E.q + E.k - E.u₀ < E.βS * (E.gS * E.dlo) := by
  have hEq : E.βS * (E.gS * E.dlo)
      = E.βS * E.dlo * E.stageSlopeS / (1 - E.βS * E.glo) := by
    rw [gS_eq, StokeyLucas.bellmanLowerSlopeConstant]
    field_simp
  rw [hEq, lt_div_iff₀ E.ΛgloS_pos]
  simpa only [stageSlopeS] using E.hCorner

/-- **The corner stage payoff** `U_S(1, 0, 1) = (u₀ − q/2) + (r + w)` — what
the Sender collects each period once locked in. -/
def cornerStagePayoff : ℝ := E.stageS0 + E.stageSlopeS

/-- **The corner stage payoff is strictly positive at every admissible member.**
Not a sign assumption. Until plan item BJ4.1 it came from chaining `hCorner`
with the deleted Sender stage margin (through `q < u₀`). It now comes from
`hCorner` alone (plan item BJ4.6, the replacement proof): implacability puts the
corner state slope above the worst stage disincentive,
`r + w > q + k − u₀ ≥ q + r` (`wedge_lt_stageSlope` and `u₀ + r ≤ k`), so the
state benefit `w` exceeds the sanction-cost curvature `q`, and the payoff
exceeds `u₀ + r + q/2 > 0`. General in `F`. -/
theorem cornerStagePayoff_pos : 0 < E.cornerStagePayoff := by
  simp only [cornerStagePayoff, stageS0, stageSlopeS]
  linarith [E.wedge_lt_stageSlope, E.hk, E.hq, E.hu₀, E.r_pos]

/-! ## 4. The economy as a `Params` — carrying `F`, not `affineF` -/

/-- **The core's `Params`.**  The only difference from
`SymbolicEconomy.toParams` is the transition block: `F := E.F`. -/
def toParams : AbstractGame.Params where
  δ := E.δ
  δ_mem := ⟨E.hδ0, E.hδ1⟩
  β_T := E.βT
  β_T_mem := ⟨E.hβT0, E.hβT1⟩
  β_S := E.βS
  β_S_mem := ⟨E.hβS0, E.hβS1⟩
  U_T := symU_T E.ℓ E.c E.n E.v
  U_S := symU_S E.q E.u₀ E.k E.r E.w
  σ := symσ E.q E.u₀ E.k E.r
  σ_mem := symσ_mem _ _ _ _
  σ_isMaxOn_U_S := symσ_isMaxOn E.hq _ _ _ _
  U_T_continuous := symU_T_continuous _ _ _ _
  U_S_continuous := symU_S_continuous _ _ _ _ _
  F := E.F
  F_continuous := E.F_continuous
  F_mono_x := E.F_mono_x
  F_mono_s := E.F_mono_s
  F_diag := E.F_diag

/-- **`E.toParams` has a continuous static Sender selector.** General in `F`: derived from
the closed form of the family's selector (`symσ_continuous`), whatever the transition
`E.F`. The proof is the one that was the economy's `σ_continuous` field until round BJ5.1
(2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance toParams_staticSelectorContinuous :
    E.toParams.StaticSelectorContinuous where
  σ_continuous := symσ_continuous _ _ _ _

@[simp] theorem toParams_U_S :
    E.toParams.U_S = symU_S E.q E.u₀ E.k E.r E.w := rfl
@[simp] theorem toParams_U_T :
    E.toParams.U_T = symU_T E.ℓ E.c E.n E.v := rfl
@[simp] theorem toParams_σ : E.toParams.σ = symσ E.q E.u₀ E.k E.r := rfl
@[simp] theorem toParams_δ : E.toParams.δ = E.δ := rfl
@[simp] theorem toParams_β_S : E.toParams.β_S = E.βS := rfl
@[simp] theorem toParams_β_T : E.toParams.β_T = E.βT := rfl
@[simp] theorem toParams_F : E.toParams.F = E.F := rfl

/-- The transition maps the square into the interval, in the binder shape the
composition rule wants. -/
theorem F_maps : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
    E.F y s ∈ Set.Icc (0 : ℝ) 1 := fun y hy s hs => E.F_mem y s hy hs

/-- The corner section maps the interval into itself. -/
theorem F_corner_maps : ∀ y ∈ Set.Icc (0 : ℝ) 1, E.F y 1 ∈ Set.Icc (0 : ℝ) 1 :=
  fun y hy => E.F_mem y 1 hy ⟨zero_le_one, le_refl 1⟩

/-- The band, in the one-variable spelling `Foundations/SemiconcaveRiccati`
uses. -/
theorem F_stateChordBand : StateChordBand (fun y => E.F y 1) E.glo E.ghi :=
  fun _ hy₁ _ hy₂ hle => E.hband hy₁ hy₂ hle

/-! ## 5. The carrier: the two-sided cone -/

/-- **The Sender carrier.**  The gain ball at the derived closed forms —
radius `M_S`, Lipschitz `K_S`, lower state-slope `g_S`.  Since `g_S ≤ K_S` with
strict inequality whenever `glo < ghi`, this is a genuine cone: the
slope-pinned extraction `valLipGainBall_clip_diff` is NOT available here.

**The semiconcavity clause is dropped (plan item BJ4.3, 2026-10-08).** The
carrier used to be the ball intersected with semiconcavity through the clip at
the Riccati modulus `Σ_V`; the clause fed only the retired curvature route to
argmax uniqueness. The carrier is now the ball alone, a larger set. General in
`F`. -/
def carrierS : Set Val := valLipGainBall E.MS E.KS E.gS 0

/-! ### Carrier-membership consequences, extracted once -/

/-- Every carrier member is nondecreasing through the clip on `[0,1]`. -/
theorem clip_mono {V : Val} (hV : V ∈ valLipGainBall E.MS E.KS E.gS 0) :
    ∀ z₁ ∈ Set.Icc (0 : ℝ) 1, ∀ z₂ ∈ Set.Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V (Sanctions.clipS' z₁) ≤ V (Sanctions.clipS' z₂) := by
  intro z₁ hz₁ z₂ hz₂ hle
  have h := hV.2.2 (Sanctions.clipS' z₁) (Sanctions.clipS' z₂)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₁]; exact hz₁)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₂]; exact hz₂)
    (Sanctions.clipS'_mono hle)
  have hd : (0 : ℝ) ≤ E.gS * dist (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) :=
    mul_nonneg E.gS_pos.le dist_nonneg
  linarith

theorem clip_monotoneOn {V : Val} (hV : V ∈ valLipGainBall E.MS E.KS E.gS 0) :
    MonotoneOn (fun z => V (Sanctions.clipS' z)) (Set.Icc (0 : ℝ) 1) :=
  fun z₁ hz₁ z₂ hz₂ hle => E.clip_mono hV z₁ hz₁ z₂ hz₂ hle

/-- Every carrier member is `K_S`-Lipschitz through the clip. -/
theorem clip_lip {V : Val} (hV : V ∈ valLipGainBall E.MS E.KS E.gS 0) :
    ∀ z₁ ∈ Set.Icc (0 : ℝ) 1, ∀ z₂ ∈ Set.Icc (0 : ℝ) 1,
      |V (Sanctions.clipS' z₁) - V (Sanctions.clipS' z₂)| ≤ E.KS * |z₁ - z₂| := by
  intro z₁ _ z₂ _
  have h := hV.2.1 (Sanctions.clipS' z₂) (Sanctions.clipS' z₁)
  have hd : dist (Sanctions.clipS' z₂) (Sanctions.clipS' z₁) ≤ |z₁ - z₂| := by
    have h2 := Sanctions.clipS'_lipschitz_dist z₂ z₁
    rwa [abs_sub_comm] at h2
  exact le_trans h (mul_le_mul_of_nonneg_left hd E.KS_pos.le)

/-! ### Non-vacuity of the carrier -/

theorem carrierS_nonempty : E.carrierS.Nonempty :=
  ⟨affineBCF E.gS,
    SymbolicEconomyF.affineBCF_mem_gainBall_cone E.gS_pos.le E.gS_le_KS E.gS_le_MS⟩

/-! ## 6. Carrier invariance under the general transition -/

/-- **The carrier is Bellman-invariant.**

`W` is the corner-pinned Bellman image of a carrier member `V`:
`W(y) = (u₀ − q/2) + (r+w)·y + β_S·V(clipS'(F(y,1)))`.  The three ball legs
come from `mem_valLipGainBall_bellman_chord` — the transition enters ONLY
through the two-sided band `CornerStateChord F glo ghi`.

Nothing here forces the corner section affine, and no slope-pinned value
extraction is used. Since plan item BJ4.3 (2026-10-08) there is no
semiconcavity leg: the carrier is the ball alone. The Riccati step survives as
`carrierS_semiconcave_invariant`, with the corner section's curvature as a
hypothesis. General in `F`. -/
theorem carrierS_invariant {V W : Val} (hV : V ∈ E.carrierS)
    (himg : ∀ y : ↥(Sanctions.S : Set ℝ),
      W y = E.stageS0 + E.stageSlopeS * y.val
        + E.βS * V (Sanctions.clipS' (E.F y.val 1))) :
    W ∈ E.carrierS := by
  have hβghi : E.βS * E.ghi < 1 := by linarith [E.ΛS_pos]
  -- ### The three ball legs.
  have hstage_bd : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |E.stageS0 + E.stageSlopeS * y| ≤ E.stageNormS := by
    intro y hy
    exact abs_affine_le_max_endpoints E.stageSlopeS_pos.le hy
  have hstage_lip : ∀ y₁ ∈ Set.Icc (0 : ℝ) 1, ∀ y₂ ∈ Set.Icc (0 : ℝ) 1,
      |E.stageSlopeS * y₂ - E.stageSlopeS * y₁| ≤ E.stageSlopeS * |y₂ - y₁| := by
    intro y₁ _ y₂ _
    rw [show E.stageSlopeS * y₂ - E.stageSlopeS * y₁
        = E.stageSlopeS * (y₂ - y₁) by ring, abs_mul,
      abs_of_nonneg E.stageSlopeS_pos.le]
  have hstage_slope : ∀ y₁ ∈ Set.Icc (0 : ℝ) 1, ∀ y₂ ∈ Set.Icc (0 : ℝ) 1,
      y₁ ≤ y₂ → E.stageSlopeS * (y₂ - y₁)
        ≤ E.stageSlopeS * y₂ - E.stageSlopeS * y₁ := by
    intro y₁ _ y₂ _ _
    exact le_of_eq (by ring)
  exact Sanctions.AbstractGame.Params.mem_valLipGainBall_bellman_chord
    (β := E.βS) (glo := E.glo) (ghi := E.ghi) (c₀ := E.stageS0)
    (L_U := E.stageSlopeS) (g_U := E.stageSlopeS) (M_U := E.stageNormS)
    (M := E.MS) (K := E.KS) (g := E.gS)
    (stage := fun y => E.stageSlopeS * y) (F := E.F)
    E.hβS0 E.hβS1 E.hglo0 hβghi E.stageSlopeS_pos.le E.gS_pos.le
    hstage_bd hstage_lip hstage_slope E.F_corner_maps E.hband
    (le_max_left _ _) (le_of_eq E.KS_eq.symm) (le_of_eq E.gS_eq)
    hV himg

/-- **The semiconcave sub-carrier is Bellman-invariant, given the corner
section's curvature** (plan item BJ4.3, 2026-10-08).

If the corner section `y ↦ F(y,1)` is semiconcave on `[0,1]` with modulus
`M_state ≥ 0` (`hGsc`), the Bellman image `W` of a carrier member `V` that is
semiconcave through the clip at the Riccati modulus
`Σ_V = (β_S·K_S·M_state)/(1 − β_S·ghi²)` is again semiconcave at `Σ_V`. This is
the Riccati leg the carrier's invariance used to carry
(`bellman_semiconcave_invariant_clip`), with `M_state` and `hGsc` moved from
structure fields to hypotheses. General in `F`. -/
theorem carrierS_semiconcave_invariant {Mstate : ℝ} (hMstate0 : 0 ≤ Mstate)
    (hGsc : SemiconcaveOnSet (fun y => E.F y 1) (Set.Icc (0 : ℝ) 1) Mstate)
    {V W : Val} (hV : V ∈ E.carrierS)
    (hVsc : SemiconcaveOnSet (fun z => V (Sanctions.clipS' z)) (Set.Icc (0 : ℝ) 1)
      (bellmanSemiconcaveConstant E.βS E.ghi 0 E.KS Mstate))
    (himg : ∀ y : ↥(Sanctions.S : Set ℝ),
      W y = E.stageS0 + E.stageSlopeS * y.val
        + E.βS * V (Sanctions.clipS' (E.F y.val 1))) :
    SemiconcaveOnSet (fun z => W (Sanctions.clipS' z)) (Set.Icc (0 : ℝ) 1)
      (bellmanSemiconcaveConstant E.βS E.ghi 0 E.KS Mstate) := by
  have hnum : (0 : ℝ) ≤ 0 + E.βS * E.KS * Mstate := by
    nlinarith [mul_nonneg (mul_nonneg E.hβS0 E.KS_pos.le) hMstate0]
  have hcontract : E.βS * E.ghi ^ 2 < 1 :=
    semiconcave_contract_of_le_one E.hβS0 E.hβS1 E.ghi_nn E.hghi1
  have hstage_sc : SemiconcaveOnSet (fun y => E.stageS0 + E.stageSlopeS * y)
      (Set.Icc (0 : ℝ) 1) 0 := by
    intro y₁ _ y₂ _ t _ _
    have h : t * (E.stageS0 + E.stageSlopeS * y₁)
        + (1 - t) * (E.stageS0 + E.stageSlopeS * y₂)
        - (E.stageS0 + E.stageSlopeS * (t * y₁ + (1 - t) * y₂))
        = (0 : ℝ) / 2 * (t * (1 - t) * (y₁ - y₂) ^ 2) := by ring
    exact le_of_eq h
  have hclip := Sanctions.Semiconcave.bellman_semiconcave_invariant_clip
    (stage := fun y => E.stageS0 + E.stageSlopeS * y) (V := V) (F := E.F)
    (β := E.βS) (ψ := 0) (Sg := bellmanSemiconcaveConstant E.βS E.ghi 0 E.KS Mstate)
    (K := E.KS) (glo := E.glo) (ghi := E.ghi) (M_state := Mstate)
    E.hβS0 E.KS_pos.le E.hglo0 hMstate0 hnum hcontract
    le_rfl E.F_corner_maps E.F_stateChordBand hGsc
    hstage_sc hVsc (E.clip_lip hV) (E.clip_mono hV)
  refine hclip.congr_on (convex_Icc _ _) ?_
  intro z hz
  have hz' : (Sanctions.clipS' z).val = z := Sanctions.clipS'_val_eq_of_mem hz
  rw [himg (Sanctions.clipS' z), hz']

/-! ## 7. Sender argmax uniqueness at physical compliance, from monotonicity

Until plan item BJ4.3 (2026-10-08) this section proved `DAU_on_cone`, argmax
uniqueness at every real compliance level, from strict concavity of the dynamic
objective, bought by the curvature margin `hCurv` and the semiconcavity clause
(`carrier_comp_semiconcave`). Both are deleted with the curvature block. The
value-class route needs uniqueness only at `a ∈ [0,1]`, and there the dynamic
objective is strictly increasing in the sanction, so the full sanction is the
unique maximiser. -/

/-- **The Sender's dynamic objective is strictly increasing in the sanction**,
at every feasible state and compliance, for every carrier value: the carrier's
minimum upward slope `g_S`, the sanction lower chord `dlo` and the implacability
margin `corner_margin_lo` beat the worst stage disincentive `q + k − u₀`.
General in `F`. (Moved here from the certificate file by plan item BJ4.3, so
that `DAUOnI_on_cone` can use it; statement unchanged.) -/
theorem senderObj_strictMonoOn {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    StrictMonoOn
      (fun s => E.toParams.U_S x a s
        + E.toParams.β_S * V_S (Sanctions.clipS' (E.toParams.F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hd : (0 : ℝ) < s₂ - s₁ := sub_pos.mpr hlt
  have hm₁ : E.F x s₁ ∈ Set.Icc (0 : ℝ) 1 := E.F_mem x s₁ hx hs₁
  have hm₂ : E.F x s₂ ∈ Set.Icc (0 : ℝ) 1 := E.F_mem x s₂ hx hs₂
  have hchord : E.dlo * (s₂ - s₁) ≤ E.F x s₂ - E.F x s₁ :=
    E.hSlo hx hs₁ hs₂ hlt.le
  have hF12 : E.F x s₁ ≤ E.F x s₂ := E.F_mono_s x hlt.le
  have hclip12 : Sanctions.clipS' (E.F x s₁) ≤ Sanctions.clipS' (E.F x s₂) :=
    Sanctions.clipS'_mono hF12
  have hgain := hV_S.2.2 (Sanctions.clipS' (E.F x s₁))
    (Sanctions.clipS' (E.F x s₂))
    (Sanctions.clipS' (E.F x s₁)).property
    (Sanctions.clipS' (E.F x s₂)).property hclip12
  have hdist :
      dist (Sanctions.clipS' (E.F x s₁)) (Sanctions.clipS' (E.F x s₂))
        = E.F x s₂ - E.F x s₁ := by
    rw [Subtype.dist_eq, Real.dist_eq,
      Sanctions.clipS'_val_eq_of_mem hm₁, Sanctions.clipS'_val_eq_of_mem hm₂,
      abs_of_nonpos (by linarith : E.F x s₁ - E.F x s₂ ≤ 0)]
    ring
  rw [hdist] at hgain
  have hgain2 : E.gS * (E.dlo * (s₂ - s₁))
      ≤ V_S (Sanctions.clipS' (E.F x s₂)) - V_S (Sanctions.clipS' (E.F x s₁)) := by
    have h := mul_le_mul_of_nonneg_left hchord E.gS_pos.le
    linarith
  have hgain3 : E.βS * (E.gS * (E.dlo * (s₂ - s₁)))
      ≤ E.βS * (V_S (Sanctions.clipS' (E.F x s₂))
                  - V_S (Sanctions.clipS' (E.F x s₁))) :=
    mul_le_mul_of_nonneg_left hgain2 E.hβS0
  have hstage_lb : (s₂ - s₁) * (E.u₀ - E.k - E.q)
      ≤ (-(E.q / 2) * s₂ ^ 2 + s₂ * (E.u₀ - E.k * a + E.r * x) + E.w * x)
        - (-(E.q / 2) * s₁ ^ 2 + s₁ * (E.u₀ - E.k * a + E.r * x) + E.w * x) := by
    nlinarith [mul_nonneg hd.le (mul_nonneg E.k_pos.le (sub_nonneg.mpr ha.2)),
      mul_nonneg hd.le (mul_nonneg E.r_pos.le hx.1),
      mul_nonneg hd.le (mul_nonneg E.hq.le
        (by linarith [hs₁.2, hs₂.2] : (0 : ℝ) ≤ 2 - s₁ - s₂))]
  have hpos : 0 < (s₂ - s₁) * (E.βS * (E.gS * E.dlo) - (E.q + E.k - E.u₀)) :=
    mul_pos hd (by linarith [E.corner_margin_lo])
  have hsum : (s₂ - s₁) * (E.u₀ - E.k - E.q)
      + E.βS * (E.gS * (E.dlo * (s₂ - s₁)))
      = (s₂ - s₁) * (E.βS * (E.gS * E.dlo) - (E.q + E.k - E.u₀)) := by ring
  simp only [toParams_U_S, symU_S, toParams_β_S, toParams_F]
  linarith

/-- **Compliance-local Sender argmax uniqueness on the cone** (plan item BJ4.3,
2026-10-08). For every carrier value, at every feasible state and every
physical compliance level `a ∈ [0,1]`, the Sender's dynamic argmax over
`[0,1]` is unique: the objective is strictly increasing in the sanction
(`senderObj_strictMonoOn`), so both maximisers are the full sanction `1`.

Replaces `DAU_on_cone`, which claimed uniqueness at every real `a` and paid for
it with the curvature block. Nothing beyond the gain ball, the sanction lower
chord and `hCorner` is read. General in `F`. -/
theorem DAUOnI_on_cone {V_S : Val} (hV_S : V_S ∈ E.carrierS) :
    E.toParams.DynamicArgmaxUniqueOnI V_S :=
  fun _x hx _a ha _s₁ _s₂ hs₁ hs₂ h₁ h₂ =>
    Sanctions.MilgromShannon.isMaxOn_unique_of_strictMonoOn
      (E.senderObj_strictMonoOn hV_S hx ha) hs₁ hs₂ h₁ h₂

end SymbolicEconomyFPersist

namespace SymbolicEconomyF

variable (E : SymbolicEconomyF)

/-! ## 7a. The family reads the core through `toPersist`

Every declaration of §2–§7 is restated here for `SymbolicEconomyF` under its
old name and proved by reading the core version at `E.toPersist`, which agrees
with `E` field by field (plan item BJ4.4), except the Sender monotonicity lemma
`senderObj_strictMonoOn`, whose `SymbolicEconomyF` form is in the Certificate
file. The definitions keep their own bodies, so the split itself changed no
statement about `SymbolicEconomyF` (BJ4.3's changes are noted where they occur).
The Target-side facts
the core does not carry (`cT_pos`, `hTMargin_ghi`, `βT_dlo_pos`, `gT_pos`,
`target_loss_margin`) are proved here from `hn`, `hcn` and `hTMargin`. General
in `F` throughout. -/

theorem ghi_nn : 0 ≤ E.ghi := E.toPersist.ghi_nn

theorem ΛS_pos : 0 < 1 - E.βS * E.ghi := E.toPersist.ΛS_pos

theorem ΛT_pos : 0 < 1 - E.βT * E.ghi := E.toPersist.ΛT_pos

theorem ΛgloS_pos : 0 < 1 - E.βS * E.glo := E.toPersist.ΛgloS_pos

theorem ΛgloT_pos : 0 < 1 - E.βT * E.glo := E.toPersist.ΛgloT_pos

/-- The band's two discount wedges are ordered: `1 − β_S·ghi ≤ 1 − β_S·glo`. -/
theorem ΛS_le_ΛgloS : 1 - E.βS * E.ghi ≤ 1 - E.βS * E.glo :=
  E.toPersist.ΛS_le_ΛgloS

theorem ΛT_le_ΛgloT : 1 - E.βT * E.ghi ≤ 1 - E.βT * E.glo :=
  E.toPersist.ΛT_le_ΛgloT

theorem Θ_pos : 0 < 1 - E.βS * E.ghi ^ 2 := E.toPersist.Θ_pos

theorem r_pos : 0 < E.r := E.toPersist.r_pos

theorem k_pos : 0 < E.k := E.toPersist.k_pos

theorem xb_le_one : E.xb ≤ 1 := E.hxb1.le

/-- The worst stage disincentive the Sender can face is strictly positive. -/
theorem wedge_pos : 0 < E.q + E.k - E.u₀ := E.toPersist.wedge_pos

/-- **Implacability at the band's UPPER rate** — the weaker reading, derived
from the field's `glo` reading. -/
theorem hCorner_ghi :
    (E.q + E.k - E.u₀) * (1 - E.βS * E.ghi) < E.βS * E.dlo * (E.r + E.w) :=
  E.toPersist.hCorner_ghi

theorem βS_dlo_pos : 0 < E.βS * E.dlo := E.toPersist.βS_dlo_pos

/-- **Derived**: the sanction chord's lower rate is strictly positive, so the
field `hdlo0 : 0 ≤ dlo` loses nothing against the old `0 < dlo` (plan item
BJ4.2). General in `F`. -/
theorem dlo_pos : 0 < E.dlo := E.toPersist.dlo_pos

/-- **Derived, not assumed**: the Sender's corner stage payoff has strictly
positive state slope `r + w`.  Falls out of `hCorner`. -/
theorem stageSlope_pos : 0 < E.r + E.w := E.toPersist.stageSlope_pos

/-- **The sanction responsiveness and the corner band split one unit of
adjustment**: `dlo + glo ≤ 1` (`SymbolicEconomyFPersist.dlo_add_glo_le_one`).
General in `F`. -/
theorem dlo_add_glo_le_one : E.dlo + E.glo ≤ 1 := E.toPersist.dlo_add_glo_le_one

/-- **Implacability caps the worst stage disincentive by the corner state
slope**: `q + k − u₀ < r + w`. A marginal sanction's discounted continuation
gain cannot exceed one period's state benefit `r + w`
(`SymbolicEconomyFPersist.wedge_lt_stageSlope`). General in `F`. -/
theorem wedge_lt_stageSlope : E.q + E.k - E.u₀ < E.r + E.w :=
  E.toPersist.wedge_lt_stageSlope

/-- **Derived**: the Target's stage loss rate at the basin bottom is positive. -/
theorem cT_pos : 0 < E.c - E.n * E.xb := by
  have h1 : E.n * E.xb ≤ E.n := by
    nlinarith [mul_nonneg E.hn (by linarith [E.xb_le_one] : (0 : ℝ) ≤ 1 - E.xb)]
  linarith [E.hcn, E.hℓ]

/-- **Target loss offset at the band's UPPER rate** — the weaker reading,
derived from the field's `glo` reading plus `c_T > 0`. -/
theorem hTMargin_ghi :
    (E.c - E.n * E.xb) * (1 - E.βT * E.ghi) ≤ E.βT * E.dlo * (E.n + E.v) :=
  le_trans (mul_le_mul_of_nonneg_left E.ΛT_le_ΛgloT E.cT_pos.le) E.hTMargin

theorem βT_dlo_pos : 0 < E.βT * E.dlo := by
  rcases (mul_nonneg E.hβT0 E.hdlo0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hT := E.hTMargin_ghi
    rw [← h, zero_mul] at hT
    linarith [mul_pos E.cT_pos E.ΛT_pos]

/-! ### Closed-form derived scalars (bodies unchanged by plan item BJ4.4) -/

/-- Sender corner stage payoff intercept, `U_S(0, ·, 1) = u₀ − q/2`. -/
def stageS0 : ℝ := E.u₀ - E.q / 2

/-- Sender corner stage payoff state slope, `r + w`. -/
def stageSlopeS : ℝ := E.r + E.w

/-- Sup-norm of the Sender's corner stage payoff on the state space. -/
def stageNormS : ℝ := max |E.stageS0| |E.stageS0 + E.stageSlopeS|

/-- Target corner stage payoff state slope. -/
def stageSlopeT : ℝ := E.n + E.v

/-- Sender value Lipschitz constant (upper band rate). -/
def KS : ℝ := symKS E.βS E.ghi E.r E.w

/-- Sender value lower state-slope (lower band rate). -/
def gS : ℝ := symGS E.βS E.glo E.r E.w

/-- Target value state-slope. -/
def gT : ℝ := StokeyLucas.bellmanLipConstant E.βT E.ghi E.stageSlopeT

/-- Sender carrier radius. -/
def MS : ℝ := max (StokeyLucas.bellmanNormBound E.βS E.stageNormS) E.KS

theorem stageSlopeS_pos : 0 < E.stageSlopeS := E.stageSlope_pos

theorem KS_eq :
    E.KS = StokeyLucas.bellmanLipConstant E.βS E.ghi E.stageSlopeS := rfl

theorem gS_eq :
    E.gS = StokeyLucas.bellmanLowerSlopeConstant E.βS E.glo E.stageSlopeS := rfl

theorem KS_pos : 0 < E.KS := E.toPersist.KS_pos

theorem gS_pos : 0 < E.gS := E.toPersist.gS_pos

theorem gT_pos : 0 < E.gT := by
  simp only [gT, StokeyLucas.bellmanLipConstant, stageSlopeT]
  exact div_pos E.stageSlopeT_pos E.ΛT_pos

/-- **The carrier is a cone, not a slope-pinned ball**: `g_S ≤ K_S`, with
equality exactly when `glo = ghi` (or `β_S = 0`). -/
theorem gS_le_KS : E.gS ≤ E.KS := E.toPersist.gS_le_KS

theorem KS_le_MS : E.KS ≤ E.MS := le_max_right _ _

theorem gS_le_MS : E.gS ≤ E.MS := le_trans E.gS_le_KS E.KS_le_MS

/-- **The Riccati modulus at a supplied state curvature is nonnegative**
(`SymbolicEconomyFPersist.semiconcaveModulus_nn`; plan item BJ4.3). `M_state` is
a hypothesis, not a field. General in `F`. -/
theorem semiconcaveModulus_nn {Mstate : ℝ} (hMstate0 : 0 ≤ Mstate) :
    0 ≤ bellmanSemiconcaveConstant E.βS E.ghi 0 E.KS Mstate :=
  E.toPersist.semiconcaveModulus_nn hMstate0

/-! ### The margins, in value-slope form -/

/-- **Implacability**: `q + k − u₀ < β_S · dlo · K_S`. -/
theorem corner_margin : E.q + E.k - E.u₀ < E.βS * E.dlo * E.KS :=
  E.toPersist.corner_margin

/-- **Target loss offset**: `c_T ≤ β_T · g_T · dlo`. -/
theorem target_loss_margin : E.c - E.n * E.xb ≤ E.βT * E.gT * E.dlo := by
  have hEq : E.βT * E.gT * E.dlo
      = E.βT * E.dlo * E.stageSlopeT / (1 - E.βT * E.ghi) := by
    simp only [gT, StokeyLucas.bellmanLipConstant]; ring
  rw [hEq, le_div_iff₀ E.ΛT_pos]
  simpa only [stageSlopeT] using E.hTMargin_ghi

/-- **Implacability in value-slope form at the carrier's guaranteed LOWER
continuation slope**: `q + k − u₀ < β_S · (g_S · dlo)`.

This is what the corner argument actually spends: a carrier member's gain from
a higher sanction is bounded *below* by `g_S = (r+w)/(1 − β_S·glo)`, not by the
Lipschitz constant `K_S`.  Before this round it was an extra argument
(`CornerLo`) to every downstream consequence; now it is a theorem, because the
structure prices `hCorner` at `glo`. -/
theorem corner_margin_lo : E.q + E.k - E.u₀ < E.βS * (E.gS * E.dlo) :=
  E.toPersist.corner_margin_lo

/-- **The corner stage payoff** `U_S(1, 0, 1) = (u₀ − q/2) + (r + w)` — what
the Sender collects each period once locked in. -/
def cornerStagePayoff : ℝ := E.stageS0 + E.stageSlopeS

/-- **The corner stage payoff is strictly positive at every admissible member**,
exactly as in the affine family. Not a sign assumption. Since plan item BJ4.1
deleted the Sender stage margin, the proof no longer goes through `q < u₀`: it
comes from `hCorner` alone (plan item BJ4.6), because implacability puts the
corner state slope above the worst stage disincentive (`wedge_lt_stageSlope`),
so `w > q` and the payoff exceeds `u₀ + r + q/2 > 0`. General in `F`. -/
theorem cornerStagePayoff_pos : 0 < E.cornerStagePayoff :=
  E.toPersist.cornerStagePayoff_pos

/-! ### The economy as a `Params` — carrying `F`, not `affineF` -/

/-- **The general-transition family's `Params`.**  The only difference from
`SymbolicEconomy.toParams` is the transition block: `F := E.F`. -/
def toParams : AbstractGame.Params where
  δ := E.δ
  δ_mem := ⟨E.hδ0, E.hδ1⟩
  β_T := E.βT
  β_T_mem := ⟨E.hβT0, E.hβT1⟩
  β_S := E.βS
  β_S_mem := ⟨E.hβS0, E.hβS1⟩
  U_T := symU_T E.ℓ E.c E.n E.v
  U_S := symU_S E.q E.u₀ E.k E.r E.w
  σ := symσ E.q E.u₀ E.k E.r
  σ_mem := symσ_mem _ _ _ _
  σ_isMaxOn_U_S := symσ_isMaxOn E.hq _ _ _ _
  U_T_continuous := symU_T_continuous _ _ _ _
  U_S_continuous := symU_S_continuous _ _ _ _ _
  F := E.F
  F_continuous := E.F_continuous
  F_mono_x := E.F_mono_x
  F_mono_s := E.F_mono_s
  F_diag := E.F_diag

/-- **`E.toParams` has a continuous static Sender selector.** General in `F`: derived from
the closed form of the family's selector (`symσ_continuous`), whatever the transition
`E.F`. The proof is the one that was the economy's `σ_continuous` field until round BJ5.1
(2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance toParams_staticSelectorContinuous :
    E.toParams.StaticSelectorContinuous where
  σ_continuous := symσ_continuous _ _ _ _

@[simp] theorem toParams_U_S :
    E.toParams.U_S = symU_S E.q E.u₀ E.k E.r E.w := rfl
@[simp] theorem toParams_U_T :
    E.toParams.U_T = symU_T E.ℓ E.c E.n E.v := rfl
@[simp] theorem toParams_σ : E.toParams.σ = symσ E.q E.u₀ E.k E.r := rfl
@[simp] theorem toParams_δ : E.toParams.δ = E.δ := rfl
@[simp] theorem toParams_β_S : E.toParams.β_S = E.βS := rfl
@[simp] theorem toParams_β_T : E.toParams.β_T = E.βT := rfl
@[simp] theorem toParams_F : E.toParams.F = E.F := rfl

/-- **Bridge to the core**: the core's `Params` at `E.toPersist` is `E`'s own
`Params`, definitionally. -/
theorem toPersist_toParams : E.toPersist.toParams = E.toParams := rfl

/-- The transition maps the square into the interval, in the binder shape the
composition rule wants. -/
theorem F_maps : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
    E.F y s ∈ Set.Icc (0 : ℝ) 1 := fun y hy s hs => E.F_mem y s hy hs

/-- The corner section maps the interval into itself. -/
theorem F_corner_maps : ∀ y ∈ Set.Icc (0 : ℝ) 1, E.F y 1 ∈ Set.Icc (0 : ℝ) 1 :=
  fun y hy => E.F_mem y 1 hy ⟨zero_le_one, le_refl 1⟩

/-- The band, in the one-variable spelling `Foundations/SemiconcaveRiccati`
uses. -/
theorem F_stateChordBand : StateChordBand (fun y => E.F y 1) E.glo E.ghi :=
  fun _ hy₁ _ hy₂ hle => E.hband hy₁ hy₂ hle

/-! ### The carrier, its invariance, and argmax uniqueness -/

/-- **The Sender carrier.**  The gain ball at the derived closed forms —
radius `M_S`, Lipschitz `K_S`, lower state-slope `g_S`.  Since `g_S ≤ K_S` with
strict inequality whenever `glo < ghi`, this is a genuine cone: the
slope-pinned extraction `valLipGainBall_clip_diff` is NOT available here.

**The semiconcavity clause is dropped (plan item BJ4.3, 2026-10-08).** The
carrier used to be the ball intersected with semiconcavity through the clip at
the Riccati modulus `Σ_V`; it is now the ball alone, a larger set. Every
statement `V ∈ E.carrierS` is correspondingly weaker. General in `F`. -/
def carrierS : Set Val := valLipGainBall E.MS E.KS E.gS 0

/-- **Bridge to the core**: the core's Sender carrier at `E.toPersist` is `E`'s
own carrier, definitionally. -/
theorem toPersist_carrierS : E.toPersist.carrierS = E.carrierS := rfl

/-- Every carrier member is nondecreasing through the clip on `[0,1]`. -/
theorem clip_mono {V : Val} (hV : V ∈ valLipGainBall E.MS E.KS E.gS 0) :
    ∀ z₁ ∈ Set.Icc (0 : ℝ) 1, ∀ z₂ ∈ Set.Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      V (Sanctions.clipS' z₁) ≤ V (Sanctions.clipS' z₂) :=
  E.toPersist.clip_mono hV

theorem clip_monotoneOn {V : Val} (hV : V ∈ valLipGainBall E.MS E.KS E.gS 0) :
    MonotoneOn (fun z => V (Sanctions.clipS' z)) (Set.Icc (0 : ℝ) 1) :=
  E.toPersist.clip_monotoneOn hV

/-- Every carrier member is `K_S`-Lipschitz through the clip. -/
theorem clip_lip {V : Val} (hV : V ∈ valLipGainBall E.MS E.KS E.gS 0) :
    ∀ z₁ ∈ Set.Icc (0 : ℝ) 1, ∀ z₂ ∈ Set.Icc (0 : ℝ) 1,
      |V (Sanctions.clipS' z₁) - V (Sanctions.clipS' z₂)| ≤ E.KS * |z₁ - z₂| :=
  E.toPersist.clip_lip hV

theorem carrierS_nonempty : E.carrierS.Nonempty := E.toPersist.carrierS_nonempty

/-- **The carrier is Bellman-invariant** under the general transition: the
chord argument of `SymbolicEconomyFPersist.carrierS_invariant`, which reads the
transition only through `CornerStateChord F glo ghi`. General in `F`. -/
theorem carrierS_invariant {V W : Val} (hV : V ∈ E.carrierS)
    (himg : ∀ y : ↥(Sanctions.S : Set ℝ),
      W y = E.stageS0 + E.stageSlopeS * y.val
        + E.βS * V (Sanctions.clipS' (E.F y.val 1))) :
    W ∈ E.carrierS :=
  E.toPersist.carrierS_invariant hV himg

/-- **The semiconcave sub-carrier is Bellman-invariant, given the corner
section's curvature** (plan item BJ4.3, 2026-10-08): the Riccati step of
`SymbolicEconomyFPersist.carrierS_semiconcave_invariant`, with `M_state` and
`hGsc` as hypotheses rather than fields. General in `F`. -/
theorem carrierS_semiconcave_invariant {Mstate : ℝ} (hMstate0 : 0 ≤ Mstate)
    (hGsc : SemiconcaveOnSet (fun y => E.F y 1) (Set.Icc (0 : ℝ) 1) Mstate)
    {V W : Val} (hV : V ∈ E.carrierS)
    (hVsc : SemiconcaveOnSet (fun z => V (Sanctions.clipS' z)) (Set.Icc (0 : ℝ) 1)
      (bellmanSemiconcaveConstant E.βS E.ghi 0 E.KS Mstate))
    (himg : ∀ y : ↥(Sanctions.S : Set ℝ),
      W y = E.stageS0 + E.stageSlopeS * y.val
        + E.βS * V (Sanctions.clipS' (E.F y.val 1))) :
    SemiconcaveOnSet (fun z => W (Sanctions.clipS' z)) (Set.Icc (0 : ℝ) 1)
      (bellmanSemiconcaveConstant E.βS E.ghi 0 E.KS Mstate) :=
  E.toPersist.carrierS_semiconcave_invariant hMstate0 hGsc hV hVsc himg

/-- **Compliance-local Sender argmax uniqueness on the cone** (plan item BJ4.3,
2026-10-08): every carrier value gives the Sender a unique dynamic argmax at
every state and every physical compliance level `a ∈ [0,1]`
(`SymbolicEconomyFPersist.DAUOnI_on_cone`). It replaces `DAU_on_cone` (every
real `a`, bought by the deleted curvature block). General in `F`. -/
theorem DAUOnI_on_cone {V_S : Val} (hV_S : V_S ∈ E.carrierS) :
    E.toParams.DynamicArgmaxUniqueOnI V_S :=
  E.toPersist.DAUOnI_on_cone hV_S

/-! ## 8. (Retired.) The affine embedding lives in the embedding file

This section used to define a second embedding of the affine family,
`ofSymbolic`, with `affineF_eq` and three `rfl` lemmas about it. It duplicated
`SymbolicEconomy.toF` (`SymbolicCertifiedFamilyGeneralFEmbedding.lean`), which
builds the same member at the degenerate band `glo = ghi = 1 − δ` with
`dlo = δ` and is the embedding the paper cites. The
duplicate was deleted on 2026-10-06 (plan item BG3.8); no statement about the
family changed. -/

end SymbolicEconomyF

/-! ## 9. Rule-9 non-vacuity: a member with a genuinely NON-AFFINE realised
recursion and a STRICTLY two-sided band.

Without this the structure could be vacuous, or (worse) inhabited only by the
affine members — in which case the affine embedding `SymbolicEconomy.toF`
(`SymbolicCertifiedFamilyGeneralFEmbedding.lean`) would be the whole story.  The
witness is `wobbleF (1/2) (1/100)` (`Examples/WobbleCornerCertWitness.lean`),
whose realised corner section `y ↦ y/2 + 1/2 + (1−y)²/100` is a parabola.

Rates:  `glo = 12/25 < 1/2 = ghi`, `dlo = 12/25`.

Payoff point (located by exact-rational arithmetic before any Lean was
written, Rule 9C; every margin below clears with slack, so it is not a
knife-edge):

    βS = βT = 1/2, q = 1/2, u₀ = 2, k = 3, r = 1, w = 4,
    ℓ = 1, c = 1, n = 0, v = 4, x̄ = 1/2.

(Until plan item BJ4.1 the point also fixed a sanction floor `s̄ = 1/2` for
the deleted Sender stage margin.)

Derived: `K_S = 20/3`, `g_S = 125/19 < K_S`.

**`κ = 1/100` is a choice, not a constraint (plan item BJ4.3, 2026-10-08).**
Until then the curvature margin `hCurv` and `hCorner` together forced the cap
`M_F < dlo/2`, which ruled out the wobble file's own `κ = 1/10` at `dd = 1/2`.
The curvature block and the cap are deleted, and §10 exhibits a member at
`wobbleF (1/2) (1/10)` itself (`wobbleEconFHalfTenth`). -/

/-- **The non-affine witness economy.** -/
def wobbleEconF : SymbolicEconomyF where
  F := wobbleF (1 / 2) (1 / 100)
  F_continuous := wobbleF_continuous _ _
  F_mono_x := wobbleF_mono_x (by norm_num) (by norm_num)
  F_mono_s := wobbleF_mono_s (by norm_num) (by norm_num)
  F_diag := wobbleF_diag _ _
  glo := 1 - 1 / 2 - 2 * (1 / 100)
  ghi := 1 - 1 / 2
  dlo := 1 / 2 - 2 * (1 / 100)
  hband := wobbleF_cornerStateChord (by norm_num)
  hSlo := wobbleF_sanctionLowerChord (by norm_num)
  hglo0 := by norm_num
  hghi1 := by norm_num
  hdlo0 := by norm_num
  δ := 1 / 2
  βS := 1 / 2
  βT := 1 / 2
  q := 1 / 2
  u₀ := 2
  k := 3
  r := 1
  w := 4
  ℓ := 1
  c := 1
  n := 0
  v := 4
  xb := 1 / 2
  hδ0 := by norm_num
  hδ1 := by norm_num
  hβS0 := by norm_num
  hβS1 := by norm_num
  hβT0 := by norm_num
  hβT1 := by norm_num
  hq := by norm_num
  hqr := by norm_num
  hu₀ := by norm_num
  hk := by norm_num
  hn := by norm_num
  hℓ := by norm_num
  hcn := by norm_num
  hxb0 := by norm_num
  hxb1 := by norm_num
  hCorner := by norm_num
  hTMargin := by norm_num

/-- The realised recursion is `x' = x/2 + 1/2 + (1 − x)²/100` — a parabola. -/
theorem wobbleEconF_realised (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    wobbleEconF.F y 1 = y / 2 + 1 / 2 + (1 - y) ^ 2 / 100 := by
  show wobbleF (1 / 2) (1 / 100) y 1 = _
  rw [wobbleF_corner _ _ hy]; ring

/-- **The witness is excluded by the abandoned corner-EQUALITY route.** No `γ`
makes its corner section the normalised affine map, so a family pinned by
`CornerSectionTop` cannot contain this economy. -/
theorem wobbleEconF_not_cornerSectionTop :
    ¬ ∃ γ : ℝ, CornerSectionTop wobbleEconF.F γ :=
  wobbleF_not_cornerSectionTop (by norm_num)

/-- ... and it is not the affine law at any weight, `δ` field notwithstanding. -/
theorem wobbleEconF_F_ne_affineF (d : ℝ) :
    wobbleEconF.F ≠ AbstractGame.affineF d :=
  wobbleF_ne_affineF (by norm_num) d

/-- **The band is strictly two-sided**: `glo = 12/25 < 1/2 = ghi`. -/
theorem wobbleEconF_band_strict : wobbleEconF.glo < wobbleEconF.ghi := by
  show (1 : ℝ) - 1 / 2 - 2 * (1 / 100) < 1 - 1 / 2
  norm_num

/-- **The carrier is a genuine cone, never slope-pinned**: `g_S < K_S`
(`125/19 < 20/3`).  This is precisely why `valLipGainBall_clip_diff` — the
exact-affine extraction `SymbolicEconomy.DAU_on_carrier` runs on — is
unavailable, and why argmax uniqueness comes from strict monotonicity in the
sanction (`DAUOnI_on_cone`) rather than from an exact value. -/
theorem wobbleEconF_gS_lt_KS : wobbleEconF.gS < wobbleEconF.KS := by
  show symGS (1 / 2) (1 - 1 / 2 - 2 * (1 / 100)) 1 4
      < symKS (1 / 2) (1 - 1 / 2) 1 4
  simp only [symGS, symKS, StokeyLucas.bellmanLowerSlopeConstant,
    StokeyLucas.bellmanLipConstant]
  norm_num

theorem wobbleEconF_carrier_nonempty : wobbleEconF.carrierS.Nonempty :=
  wobbleEconF.carrierS_nonempty

/-- **End-to-end**: at a genuinely non-affine realised recursion, every carrier
member has a unique dynamic Sender argmax at every physical state and every
physical compliance level `a ∈ [0,1]`. General in `F` (the witness's `F` is
the non-affine `wobbleF`).

**Edited in place (plan item BJ4.3, 2026-10-08).** The conclusion was
`DynamicArgmaxUnique V`, uniqueness at every real compliance level, from the
deleted curvature route; it is now the compliance-local
`DynamicArgmaxUniqueOnI V` (`DAUOnI_on_cone`), the form the value class reads. -/
theorem wobbleEconF_DAU {V : Val} (hV : V ∈ wobbleEconF.carrierS) :
    wobbleEconF.toParams.DynamicArgmaxUniqueOnI V :=
  wobbleEconF.DAUOnI_on_cone hV

/-- **End-to-end**: and the carrier is Bellman-invariant there. -/
theorem wobbleEconF_invariant {V W : Val} (hV : V ∈ wobbleEconF.carrierS)
    (himg : ∀ y : ↥(Sanctions.S : Set ℝ),
      W y = wobbleEconF.stageS0 + wobbleEconF.stageSlopeS * y.val
        + wobbleEconF.βS * V (Sanctions.clipS' (wobbleEconF.F y.val 1))) :
    W ∈ wobbleEconF.carrierS :=
  wobbleEconF.carrierS_invariant hV himg

/-! ## 10. WIRE 2 — members at the wobble file's OWN published curvature

§9's witness runs at `κ = 1/100`: one hundredth of the curvature
`Examples/WobbleCornerCertWitness.lean` actually publishes.  A reader is
entitled to ask whether the general family is a real generalisation or a
family of *nearly* affine transitions.  This section answers it with two
members at the published `κ = 1/10`: `wobbleEconFHalfTenth` at the published
transition `wobbleF (1/2) (1/10)` itself (§10.2), and `wobbleEconF10` at the
faster adjustment speed `dd = 3/4` (§10.3).

**History (plan item BJ4.3, 2026-10-08).** Until then this section proved a
cap `M_F < dlo/2` (`MF_lt_half_dlo`, `curvature_budget`) from the curvature
margin `hCurv` and `hCorner`, and from it a Rule-11 "refutation" that
`wobbleF (1/2) (1/10)` is the transition of no member
(`wobbleF_realisable_needs`, `wobbleF_half_tenth_not_realisable`,
`wobbleF_kappa_ceiling`, `wobbleF_threequarters_eighth_not_realisable`,
`wobbleEconF10_window`). The refutation was a consequence of `hCurv`, not a
necessity result: with the curvature block deleted it is false, and
`wobbleEconFHalfTenth` is a member at exactly that transition. The cap, the
refutation and the window lemmas are deleted. -/

/-! ### 10.1 `wobbleF`'s curvature moduli are sharp from below

`WobbleCornerCertWitness` proves its four *chord* rates sharp
(`wobbleF_stateChordBand_sharp`, `wobbleF_sanctionChords_sharp`) but not
its two *curvature* moduli.  Both defects are attained at the midpoint of
`[0,1]` with value `κ/4` against a budget `M/8`, so `M ≥ 2κ` in each
direction.  They fed the retired cap; they remain facts about the
transition, and say that `2κ` is the least corner curvature one can supply to
`persistence_generalF_semiconcave` at a `wobbleF` member. -/

/-- **The sanction-direction modulus cannot be declared below `2κ`.** -/
theorem wobbleF_sanctionSemiconcave_sharp {dd κ M : ℝ}
    (h : SanctionSemiconcave (wobbleF dd κ) M) : 2 * κ ≤ M := by
  have hzero : ((0 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have hone : ((1 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hhalf : ((1 : ℝ) / 2) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h0 : (1 : ℝ) / 2 * wobbleF dd κ 0 0 + (1 - 1 / 2) * wobbleF dd κ 0 1
      - wobbleF dd κ 0 (1 / 2 * 0 + (1 - 1 / 2) * 1)
      ≤ M / 2 * (1 / 2 * (1 - 1 / 2) * ((0 : ℝ) - 1) ^ 2) :=
    h 0 hzero 0 hzero 1 hone (1 / 2) (by norm_num) (by norm_num)
  rw [show ((1 : ℝ) / 2 * 0 + (1 - 1 / 2) * 1) = 1 / 2 by norm_num] at h0
  rw [wobbleF_diag dd κ 0, wobbleF_sq hzero hone, wobbleF_sq hzero hhalf] at h0
  nlinarith [h0]

/-- **The corner-section (state-direction) modulus cannot be declared below
`2κ`.** -/
theorem wobbleF_corner_semiconcave_sharp {dd κ M : ℝ}
    (h : SemiconcaveOnSet (fun y => wobbleF dd κ y 1) (Set.Icc (0 : ℝ) 1) M) :
    2 * κ ≤ M := by
  have hzero : ((0 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have hone : ((1 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hhalf : ((1 : ℝ) / 2) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h0 : (1 : ℝ) / 2 * wobbleF dd κ 0 1 + (1 - 1 / 2) * wobbleF dd κ 1 1
      - wobbleF dd κ (1 / 2 * 0 + (1 - 1 / 2) * 1) 1
      ≤ M / 2 * (1 / 2 * (1 - 1 / 2) * ((0 : ℝ) - 1) ^ 2) :=
    h 0 hzero 1 hone (1 / 2) (by norm_num) (by norm_num)
  rw [show ((1 : ℝ) / 2 * 0 + (1 - 1 / 2) * 1) = 1 / 2 by norm_num] at h0
  rw [wobbleF_corner dd κ hzero, wobbleF_corner dd κ hone,
    wobbleF_corner dd κ hhalf] at h0
  nlinarith [h0]

/-! ### 10.2 The wobble file's own published transition is a member

`wobbleEconFHalfTenth` carries `wobbleF (1/2) (1/10)`, the transition
`Examples/WobbleCornerCertWitness.lean` publishes, with the rates read off its
two exact chord identities (all proved sharp there):

| object | formula | value |
|---|---|---|
| corner band lower `glo`  | `1 − dd − 2κ` | `3/10` |
| corner band upper `ghi`  | `1 − dd`      | `1/2`  |
| sanction lower `dlo`     | `dd − 2κ`     | `3/10` |

Payoffs (exact rationals; every margin clears with slack):

    β_S = β_T = 1/2,  q = 1/2,  u₀ = 2,  k = 3,  r = 1,  w = 10,
    ℓ = 1,  c = 1,  n = 0,  v = 6,  x̄ = 1/2,  δ = 1/2.

Margins: `hCorner` `51/40 < 33/20`, `hTMargin` `17/20 ≤ 9/10`. The point is
`wobbleEconF`'s with the Sender's state benefit `w` raised from `4` to `10` and
the Target's state gain `v` from `4` to `6`: at the lower sanction
responsiveness `dlo = 3/10` a larger state stake buys back implacability and
the loss offset.

Rule 9: an existence certificate. It shows the deleted cap excluded genuine
members; it shows nothing about how large the admissible region is. -/

/-- **A member at the wobble file's own published transition**
`wobbleF (1/2) (1/10)` (plan item BJ4.3, 2026-10-08). Under the deleted
curvature block no member had this transition. General in `F`: the transition
is the non-affine `wobbleF`, read only through its chord rates. -/
def wobbleEconFHalfTenth : SymbolicEconomyF where
  F := wobbleF (1 / 2) (1 / 10)
  F_continuous := wobbleF_continuous _ _
  F_mono_x := wobbleF_mono_x (by norm_num) (by norm_num)
  F_mono_s := wobbleF_mono_s (by norm_num) (by norm_num)
  F_diag := wobbleF_diag _ _
  glo := 1 - 1 / 2 - 2 * (1 / 10)
  ghi := 1 - 1 / 2
  dlo := 1 / 2 - 2 * (1 / 10)
  hband := wobbleF_cornerStateChord (by norm_num)
  hSlo := wobbleF_sanctionLowerChord (by norm_num)
  hglo0 := by norm_num
  hghi1 := by norm_num
  hdlo0 := by norm_num
  δ := 1 / 2
  βS := 1 / 2
  βT := 1 / 2
  q := 1 / 2
  u₀ := 2
  k := 3
  r := 1
  w := 10
  ℓ := 1
  c := 1
  n := 0
  v := 6
  xb := 1 / 2
  hδ0 := by norm_num
  hδ1 := by norm_num
  hβS0 := by norm_num
  hβS1 := by norm_num
  hβT0 := by norm_num
  hβT1 := by norm_num
  hq := by norm_num
  hqr := by norm_num
  hu₀ := by norm_num
  hk := by norm_num
  hn := by norm_num
  hℓ := by norm_num
  hcn := by norm_num
  hxb0 := by norm_num
  hxb1 := by norm_num
  hCorner := by norm_num
  hTMargin := by norm_num

/-- **The wobble file's own published transition is realisable in the family**
(plan item BJ4.3, 2026-10-08). It replaces the deleted Rule-11 "refutation"
`wobbleF_half_tenth_not_realisable`, which held only because of the deleted
curvature margin. General in `F`. -/
theorem wobbleF_half_tenth_realisable :
    ∃ E : SymbolicEconomyF, E.F = wobbleF (1 / 2) (1 / 10) :=
  ⟨wobbleEconFHalfTenth, rfl⟩

/-- The realised recursion is `x' = x/2 + 1/2 + (1 − x)²/10` — a parabola
with the published bump coefficient.
A fact about one concrete member, whose transition is not affine. -/
theorem wobbleEconFHalfTenth_realised (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    wobbleEconFHalfTenth.F y 1 = y / 2 + 1 / 2 + (1 - y) ^ 2 / 10 := by
  change wobbleF (1 / 2) (1 / 10) y 1 = _
  rw [wobbleF_corner _ _ hy]; ring

/-- No affine map agrees with this member's realised corner section on the
state space. A fact about one concrete member, whose transition is not affine. -/
theorem wobbleEconFHalfTenth_corner_not_affine :
    ¬ ∃ a b : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, wobbleEconFHalfTenth.F y 1 = a * y + b :=
  wobbleF_corner_not_affine (by norm_num)

/-- **The member's curvature is the published one, in both directions, and no
smaller modulus works.** The transition is semiconcave in the sanction with
modulus `1/5 = 2κ` and with no smaller modulus, and so is the corner section.
These are exactly the moduli `wobbleParams` publishes, and they exceed the
cap `M_F < dlo/2 = 3/20` the deleted curvature margin imposed.
A fact about one concrete member, whose transition is not affine. -/
theorem wobbleEconFHalfTenth_curvature :
    (SanctionSemiconcave wobbleEconFHalfTenth.F (1 / 5)
      ∧ ∀ M, SanctionSemiconcave wobbleEconFHalfTenth.F M → 1 / 5 ≤ M)
    ∧ (SemiconcaveOnSet (fun y => wobbleEconFHalfTenth.F y 1)
          (Set.Icc (0 : ℝ) 1) (1 / 5)
      ∧ ∀ M, SemiconcaveOnSet (fun y => wobbleEconFHalfTenth.F y 1)
          (Set.Icc (0 : ℝ) 1) M → 1 / 5 ≤ M) := by
  refine ⟨⟨?_, fun M h => ?_⟩, ⟨?_, fun M h => ?_⟩⟩
  · have h := wobbleF_sanctionSemiconcave (1 / 2 : ℝ) (1 / 10)
    rw [show (2 : ℝ) * (1 / 10) = 1 / 5 by norm_num] at h
    exact h
  · have := wobbleF_sanctionSemiconcave_sharp (dd := 1 / 2) (κ := 1 / 10) h
    linarith
  · have h := wobbleF_corner_semiconcave (1 / 2 : ℝ) (1 / 10)
    rw [show (2 : ℝ) * (1 / 10) = 1 / 5 by norm_num] at h
    exact h
  · have := wobbleF_corner_semiconcave_sharp (dd := 1 / 2) (κ := 1 / 10) h
    linarith

/-- The corner state band is strictly two-sided: `glo = 3/10 < 1/2 = ghi`.
A fact about one concrete member, whose transition is not affine. -/
theorem wobbleEconFHalfTenth_band_strict :
    wobbleEconFHalfTenth.glo < wobbleEconFHalfTenth.ghi := by
  change (1 : ℝ) - 1 / 2 - 2 * (1 / 10) < 1 - 1 / 2
  norm_num

/-- The Sender carrier at this member is nonempty.
A fact about one concrete member, whose transition is not affine. -/
theorem wobbleEconFHalfTenth_carrier_nonempty :
    wobbleEconFHalfTenth.carrierS.Nonempty :=
  wobbleEconFHalfTenth.carrierS_nonempty

/-- **End-to-end**: at the published transition every carrier member has a
unique dynamic Sender argmax at every physical state and every physical
compliance level. General in `F`. -/
theorem wobbleEconFHalfTenth_DAU {V : Val}
    (hV : V ∈ wobbleEconFHalfTenth.carrierS) :
    wobbleEconFHalfTenth.toParams.DynamicArgmaxUniqueOnI V :=
  wobbleEconFHalfTenth.DAUOnI_on_cone hV

/-- **End-to-end**: and the carrier is Bellman-invariant there.
A fact about one concrete member, whose transition is not affine. -/
theorem wobbleEconFHalfTenth_invariant {V W : Val}
    (hV : V ∈ wobbleEconFHalfTenth.carrierS)
    (himg : ∀ y : ↥(Sanctions.S : Set ℝ),
      W y = wobbleEconFHalfTenth.stageS0 + wobbleEconFHalfTenth.stageSlopeS * y.val
        + wobbleEconFHalfTenth.βS
          * V (Sanctions.clipS' (wobbleEconFHalfTenth.F y.val 1))) :
    W ∈ wobbleEconFHalfTenth.carrierS :=
  wobbleEconFHalfTenth.carrierS_invariant hV himg

/-! ### 10.3 A second member at the published curvature, at `dd = 3/4`

`wobbleEconF10` carries the published `κ = 1/10` at the faster adjustment
speed `dd = 3/4`. It was built, before plan item BJ4.3, to clear the retired
cap at `κ = 1/10`, which `dd = 1/2` could not; the cap is gone and it is kept
as a second member with a different band. Rates (all read off
`WobbleCornerCertWitness`'s two exact chord identities, and all proved sharp
there):

| object | formula | value |
|---|---|---|
| corner band lower `glo`  | `1 − dd − 2κ` | `1/20`  |
| corner band upper `ghi`  | `1 − dd`      | `1/4`   |
| sanction lower `dlo`     | `dd − 2κ`     | `11/20` |

The transition also has the sanction upper chord rate `dd + 2κ = 19/20` and the
curvature moduli `2κ = 1/5` in both directions (`wobbleEconF10_MF`,
`wobbleEconF10_Mstate`); since plan item BJ4.3 these are properties of `F`,
not fields.

Payoffs, located by exact-rational sweep (Rule 9C) over a 20 × 10
`(dd, β_S)` grid and then snapped:

    β_S = 1/10,  β_T = 1/2,  q = 1/4,  u₀ = 1,  k = 5/4,  r = 1/4,
    w = 19/2,    ℓ = 1,      c = 1,    n = 0,   v = 4,    x̄ = 1/2,
    δ = 3/4  (the inert `Params.δ` slot, set to the transition's own
              affine weight rather than left as decoration).

Derived: `K_S = 10`, `g_S = 1950/199 < K_S`.  Margins, with slack: `hCorner`
`39/80 < 429/800` (the deleted stage margin, at `s̄ = 1/2`, read
`429/800 < 39/40`); `hTMargin` `7/8 ≤ 11/10`. (The deleted curvature margin
read `4336/19875 < 1/4`.) -/

/-- **The full-curvature witness economy at `dd = 3/4`.** -/
def wobbleEconF10 : SymbolicEconomyF where
  F := wobbleF (3 / 4) (1 / 10)
  F_continuous := wobbleF_continuous _ _
  F_mono_x := wobbleF_mono_x (by norm_num) (by norm_num)
  F_mono_s := wobbleF_mono_s (by norm_num) (by norm_num)
  F_diag := wobbleF_diag _ _
  glo := 1 - 3 / 4 - 2 * (1 / 10)
  ghi := 1 - 3 / 4
  dlo := 3 / 4 - 2 * (1 / 10)
  hband := wobbleF_cornerStateChord (by norm_num)
  hSlo := wobbleF_sanctionLowerChord (by norm_num)
  hglo0 := by norm_num
  hghi1 := by norm_num
  hdlo0 := by norm_num
  δ := 3 / 4
  βS := 1 / 10
  βT := 1 / 2
  q := 1 / 4
  u₀ := 1
  k := 5 / 4
  r := 1 / 4
  w := 19 / 2
  ℓ := 1
  c := 1
  n := 0
  v := 4
  xb := 1 / 2
  hδ0 := by norm_num
  hδ1 := by norm_num
  hβS0 := by norm_num
  hβS1 := by norm_num
  hβT0 := by norm_num
  hβT1 := by norm_num
  hq := by norm_num
  hqr := by norm_num
  hu₀ := by norm_num
  hk := by norm_num
  hn := by norm_num
  hℓ := by norm_num
  hcn := by norm_num
  hxb0 := by norm_num
  hxb1 := by norm_num
  hCorner := by norm_num
  hTMargin := by norm_num

/-! #### The curvature really is the published one -/

/-- The transition is `wobbleF` at the wobble file's own `κ = 1/10`. -/
theorem wobbleEconF10_F : wobbleEconF10.F = wobbleF (3 / 4) (1 / 10) := rfl

/-- **Sanction-direction curvature `1/5`, exactly** — `wobbleParams`'
published modulus: the transition is semiconcave in the sanction with modulus
`1/5`, and with no smaller modulus.

**Edited in place (plan item BJ4.3, 2026-10-08).** The statement was
`wobbleEconF10.MF = 1 / 5`, the value of a declared field; the field `MF` is
deleted, so the statement is now the property of `F` it recorded, together with
its sharpness (`wobbleF_sanctionSemiconcave_sharp`).
A fact about one concrete member, whose transition is not affine. -/
theorem wobbleEconF10_MF :
    SanctionSemiconcave wobbleEconF10.F (1 / 5)
      ∧ ∀ M, SanctionSemiconcave wobbleEconF10.F M → 1 / 5 ≤ M := by
  refine ⟨?_, fun M h => ?_⟩
  · have h := wobbleF_sanctionSemiconcave (3 / 4 : ℝ) (1 / 10)
    rw [show (2 : ℝ) * (1 / 10) = 1 / 5 by norm_num] at h
    exact h
  · have := wobbleF_sanctionSemiconcave_sharp (dd := 3 / 4) (κ := 1 / 10) h
    linarith

/-- **Corner-section curvature `1/5`, exactly** — `wobbleParams`' published
modulus: the corner section is semiconcave with modulus `1/5`, and with no
smaller modulus.

**Edited in place (plan item BJ4.3, 2026-10-08).** The statement was
`wobbleEconF10.Mstate = 1 / 5`; the field `Mstate` is deleted, so the statement
is now the property of `F` it recorded, with its sharpness
(`wobbleF_corner_semiconcave_sharp`).
A fact about one concrete member, whose transition is not affine. -/
theorem wobbleEconF10_Mstate :
    SemiconcaveOnSet (fun y => wobbleEconF10.F y 1) (Set.Icc (0 : ℝ) 1) (1 / 5)
      ∧ ∀ M, SemiconcaveOnSet (fun y => wobbleEconF10.F y 1)
          (Set.Icc (0 : ℝ) 1) M → 1 / 5 ≤ M := by
  refine ⟨?_, fun M h => ?_⟩
  · have h := wobbleF_corner_semiconcave (3 / 4 : ℝ) (1 / 10)
    rw [show (2 : ℝ) * (1 / 10) = 1 / 5 by norm_num] at h
    exact h
  · have := wobbleF_corner_semiconcave_sharp (dd := 3 / 4) (κ := 1 / 10) h
    linarith

/-! #### THE PAYOFF — the realised recursion is genuinely non-affine -/

/-- The realised recursion is `x' = x/4 + 3/4 + (1 − x)²/10` — a parabola
with the published bump coefficient, not a line. -/
theorem wobbleEconF10_realised (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    wobbleEconF10.F y 1 = y / 4 + 3 / 4 + (1 - y) ^ 2 / 10 := by
  show wobbleF (3 / 4) (1 / 10) y 1 = _
  rw [wobbleF_corner _ _ hy]; ring

/-- **THE WIRE-2 PAYOFF.** No affine map agrees with this member's realised
corner section anywhere on the state space: the family contains an economy
whose certified dynamics are genuinely non-affine.  The obstruction is the
midpoint defect `κ/4 = 1/40` against the endpoint chord. -/
theorem wobbleEconF10_corner_not_affine :
    ¬ ∃ a b : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, wobbleEconF10.F y 1 = a * y + b :=
  wobbleF_corner_not_affine (by norm_num)

/-- The same statement at the `Params` the family actually produces —
this is the object every downstream theorem consumes. -/
theorem wobbleEconF10_toParams_corner_not_affine :
    ¬ ∃ a b : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      wobbleEconF10.toParams.F y 1 = a * y + b :=
  wobbleF_corner_not_affine (by norm_num)

/-- The abandoned corner-EQUALITY route excludes this member outright. -/
theorem wobbleEconF10_not_cornerSectionTop :
    ¬ ∃ γ : ℝ, CornerSectionTop wobbleEconF10.F γ :=
  wobbleF_not_cornerSectionTop (by norm_num)

/-- ... and the transition is not the affine law at any weight, `δ`
notwithstanding. -/
theorem wobbleEconF10_F_ne_affineF (d : ℝ) :
    wobbleEconF10.F ≠ AbstractGame.affineF d :=
  wobbleF_ne_affineF (by norm_num) d

/-- The same, at the `Params` level: the family's `Params` is NOT the
affine family's `Params` for any weight — so the affine embedding
`SymbolicEconomy.toF` (`SymbolicCertifiedFamilyGeneralFEmbedding.lean`) does
not reach this member. -/
theorem wobbleEconF10_toParams_F_ne_affineF (d : ℝ) :
    wobbleEconF10.toParams.F ≠ AbstractGame.affineF d :=
  wobbleF_ne_affineF (by norm_num) d

/-! #### The band, the cone, and the certified conclusions -/

/-- The corner state band is strictly two-sided: `glo = 1/20 < 1/4 = ghi`. -/
theorem wobbleEconF10_band_strict : wobbleEconF10.glo < wobbleEconF10.ghi := by
  show (1 : ℝ) - 3 / 4 - 2 * (1 / 10) < 1 - 3 / 4
  norm_num

/-- **The sanction chord band is strictly two-sided**: the transition has no
upper sanction chord at its lower rate `dlo = 11/20` (its sharp upper rate is
`19/20`), so its sanction responsiveness genuinely varies.

**Edited in place (plan item BJ4.3, 2026-10-08).** The statement was
`wobbleEconF10.dlo < wobbleEconF10.dhi`; the field `dhi` is deleted, so the
statement now says the same thing of `F` directly, via
`wobbleF_sanctionChords_sharp`. A fact about one concrete member, whose transition is not affine. -/
theorem wobbleEconF10_sanction_band_strict :
    ¬ SanctionUpperChord wobbleEconF10.F wobbleEconF10.dlo := by
  intro h
  have hlo : SanctionLowerChord (wobbleF (3 / 4) (1 / 10)) wobbleEconF10.dlo :=
    wobbleEconF10.hSlo
  have hhi : SanctionUpperChord (wobbleF (3 / 4) (1 / 10)) wobbleEconF10.dlo := h
  have hs := (wobbleF_sanctionChords_sharp (by norm_num) hlo hhi).2
  change (3 : ℝ) / 4 + 2 * (1 / 10) ≤ 3 / 4 - 2 * (1 / 10) at hs
  norm_num at hs

theorem wobbleEconF10_KS_eq : wobbleEconF10.KS = 10 := by
  show symKS (1 / 10) (1 - 3 / 4) (1 / 4) (19 / 2) = 10
  simp only [symKS, StokeyLucas.bellmanLipConstant]
  norm_num

theorem wobbleEconF10_gS_eq : wobbleEconF10.gS = 1950 / 199 := by
  show symGS (1 / 10) (1 - 3 / 4 - 2 * (1 / 10)) (1 / 4) (19 / 2) = 1950 / 199
  simp only [symGS, StokeyLucas.bellmanLowerSlopeConstant]
  norm_num

/-- **The carrier is a genuine cone**, `g_S = 1950/199 < 10 = K_S`, so the
slope-pinned extraction `valLipGainBall_clip_diff` that
`SymbolicEconomy.DAU_on_carrier` runs on is unavailable, and argmax
uniqueness comes from strict monotonicity in the sanction
(`DAUOnI_on_cone`). -/
theorem wobbleEconF10_gS_lt_KS : wobbleEconF10.gS < wobbleEconF10.KS := by
  rw [wobbleEconF10_gS_eq, wobbleEconF10_KS_eq]
  norm_num

theorem wobbleEconF10_carrier_nonempty : wobbleEconF10.carrierS.Nonempty :=
  wobbleEconF10.carrierS_nonempty

/-- **End-to-end**: at the published curvature, every carrier member has a
unique dynamic Sender argmax at every physical state and every physical
compliance level `a ∈ [0,1]`. General in `F`.

**Edited in place (plan item BJ4.3, 2026-10-08).** The conclusion was
`DynamicArgmaxUnique V` (every real compliance level) from the deleted
curvature route; it is now `DynamicArgmaxUniqueOnI V` (`DAUOnI_on_cone`). -/
theorem wobbleEconF10_DAU {V : Val} (hV : V ∈ wobbleEconF10.carrierS) :
    wobbleEconF10.toParams.DynamicArgmaxUniqueOnI V :=
  wobbleEconF10.DAUOnI_on_cone hV

/-- **End-to-end**: and the carrier is Bellman-invariant there. -/
theorem wobbleEconF10_invariant {V W : Val} (hV : V ∈ wobbleEconF10.carrierS)
    (himg : ∀ y : ↥(Sanctions.S : Set ℝ),
      W y = wobbleEconF10.stageS0 + wobbleEconF10.stageSlopeS * y.val
        + wobbleEconF10.βS * V (Sanctions.clipS' (wobbleEconF10.F y.val 1))) :
    W ∈ wobbleEconF10.carrierS :=
  wobbleEconF10.carrierS_invariant hV himg

/-! #### The whole WIRE-2 deliverable, bundled -/

/-- **WIRE 2, in one statement.**

Reading the conjuncts in order: this member's transition is `wobbleF` at
the wobble file's own published curvature `κ = 1/10`; its realised corner
section admits no affine representative, and no `γ` makes it the
normalised affine map, and it is not the affine law at any weight; its
corner state band is strictly two-sided and it has no upper sanction chord at
its lower rate; its sanction-direction and corner-section curvature moduli are
exactly the published `1/5`; the carrier is a genuine cone (`g_S < K_S`) and is
inhabited; and on that carrier the dynamic Sender argmax is unique at every
physical compliance level.

**Edited in place (plan item BJ4.3, 2026-10-08).** Four conjuncts named deleted
fields or the deleted curvature route: `dlo < dhi` became "no upper sanction
chord at `dlo`", `MF = 1/5` and `Mstate = 1/5` became the sharp curvature
statements `wobbleEconF10_MF` and `wobbleEconF10_Mstate`, `0 < Σ_V` was dropped
with the semiconcavity clause, and `DynamicArgmaxUnique` became the
compliance-local `DynamicArgmaxUniqueOnI`.

Rule 9A scope: an existence certificate and nothing more.  It shows the
general family is not a disguised affine family.  It shows nothing about
genericity. -/
theorem wobbleEconF10_wire2_bundle :
    wobbleEconF10.F = wobbleF (3 / 4) (1 / 10)
    ∧ (¬ ∃ a b : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, wobbleEconF10.F y 1 = a * y + b)
    ∧ (¬ ∃ γ : ℝ, CornerSectionTop wobbleEconF10.F γ)
    ∧ (∀ d : ℝ, wobbleEconF10.toParams.F ≠ AbstractGame.affineF d)
    ∧ wobbleEconF10.glo < wobbleEconF10.ghi
    ∧ ¬ SanctionUpperChord wobbleEconF10.F wobbleEconF10.dlo
    ∧ (SanctionSemiconcave wobbleEconF10.F (1 / 5)
        ∧ ∀ M, SanctionSemiconcave wobbleEconF10.F M → 1 / 5 ≤ M)
    ∧ (SemiconcaveOnSet (fun y => wobbleEconF10.F y 1) (Set.Icc (0 : ℝ) 1) (1 / 5)
        ∧ ∀ M, SemiconcaveOnSet (fun y => wobbleEconF10.F y 1)
            (Set.Icc (0 : ℝ) 1) M → 1 / 5 ≤ M)
    ∧ wobbleEconF10.gS < wobbleEconF10.KS
    ∧ wobbleEconF10.carrierS.Nonempty
    ∧ (∀ V : Val, V ∈ wobbleEconF10.carrierS →
        wobbleEconF10.toParams.DynamicArgmaxUniqueOnI V) :=
  ⟨wobbleEconF10_F, wobbleEconF10_corner_not_affine,
    wobbleEconF10_not_cornerSectionTop, wobbleEconF10_toParams_F_ne_affineF,
    wobbleEconF10_band_strict, wobbleEconF10_sanction_band_strict,
    wobbleEconF10_MF, wobbleEconF10_Mstate, wobbleEconF10_gS_lt_KS,
    wobbleEconF10_carrier_nonempty,
    fun _ hV => wobbleEconF10_DAU hV⟩

end -- noncomputable section

end Examples

end Sanctions

-- Rule 10: the derived conditions (wedge below the stage slope, dlo > 0, F_mem, glo ≤ ghi)
-- and the persistence core read back through toPersist.
#print axioms Sanctions.Examples.SymbolicEconomyF.hCorner_ghi
#print axioms Sanctions.Examples.SymbolicEconomyF.hTMargin_ghi
#print axioms Sanctions.Examples.SymbolicEconomyF.corner_margin_lo
#print axioms Sanctions.Examples.SymbolicEconomyF.wedge_lt_stageSlope
#print axioms Sanctions.Examples.SymbolicEconomyF.dlo_pos
#print axioms Sanctions.Examples.SymbolicEconomyF.F_mem
#print axioms Sanctions.Examples.SymbolicEconomyF.hglo_ghi
#print axioms Sanctions.Examples.SymbolicEconomyF.stageSlopeT_pos
#print axioms Sanctions.Examples.SymbolicEconomyF.toPersist
#print axioms Sanctions.Examples.SymbolicEconomyFPersist.carrierS_invariant
#print axioms Sanctions.Examples.SymbolicEconomyFPersist.carrierS_semiconcave_invariant
#print axioms Sanctions.Examples.SymbolicEconomyFPersist.senderObj_strictMonoOn
#print axioms Sanctions.Examples.SymbolicEconomyFPersist.DAUOnI_on_cone
#print axioms Sanctions.Examples.SymbolicEconomyFPersist.cornerStagePayoff_pos
#print axioms Sanctions.Examples.SymbolicEconomyF.cornerStagePayoff_pos
#print axioms Sanctions.Examples.SymbolicEconomyF.carrierS_invariant
#print axioms Sanctions.Examples.SymbolicEconomyF.carrierS_semiconcave_invariant
#print axioms Sanctions.Examples.SymbolicEconomyF.DAUOnI_on_cone
#print axioms Sanctions.Examples.SymbolicEconomyF.carrierS_nonempty
#print axioms Sanctions.Examples.wobbleEconF_DAU
#print axioms Sanctions.Examples.wobbleEconF_invariant
#print axioms Sanctions.Examples.wobbleEconF_not_cornerSectionTop
#print axioms Sanctions.Examples.wobbleEconF_gS_lt_KS
#print axioms Sanctions.Examples.wobbleEconF_carrier_nonempty

-- WIRE 2
#print axioms Sanctions.Examples.wobbleF_sanctionSemiconcave_sharp
#print axioms Sanctions.Examples.wobbleF_corner_semiconcave_sharp
#print axioms Sanctions.Examples.wobbleF_half_tenth_realisable
#print axioms Sanctions.Examples.wobbleEconFHalfTenth_corner_not_affine
#print axioms Sanctions.Examples.wobbleEconFHalfTenth_curvature
#print axioms Sanctions.Examples.wobbleEconFHalfTenth_DAU
#print axioms Sanctions.Examples.wobbleEconFHalfTenth_invariant
#print axioms Sanctions.Examples.wobbleEconF10_corner_not_affine
#print axioms Sanctions.Examples.wobbleEconF10_toParams_corner_not_affine
#print axioms Sanctions.Examples.wobbleEconF10_wire2_bundle
#print axioms Sanctions.Examples.wobbleEconF10_DAU
#print axioms Sanctions.Examples.wobbleEconF10_invariant
#print axioms Sanctions.Examples.wobbleEconF10_carrier_nonempty
#print axioms Sanctions.Examples.wobbleEconF10_gS_lt_KS
#print axioms Sanctions.Examples.wobbleEconF10_MF
#print axioms Sanctions.Examples.wobbleEconF10_Mstate
#print axioms Sanctions.Examples.wobbleEconF10_sanction_band_strict
