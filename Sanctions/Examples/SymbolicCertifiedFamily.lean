/-
Sanctions/Examples/SymbolicCertifiedFamily.lean

**A certificate-bearing family of sanctions economies with symbolic payoff
coefficients.**

Every previous complete certificate witness in this development
(`eeCertParams`, `fgcParams`, `b2Params`, …) is a *single point* of the
parameter space: its payoff coefficients are hand-chosen rationals, and the
certificate's margins close because those particular numbers happen to work.
This file replaces the point by a **family**.

## READ THIS BEFORE CLASSIFYING ANYTHING IN THIS FILE (audit note)

**The results here are universals over a family, not witness instances.** They
are quantified over `(E : SymbolicEconomy)` — every admissible member — so they
license universal statements about the family, and Rule 9's "a witness proves
only existence" restriction does **not** apply to them.

The file sits under `Examples/` because the family fixes a *functional form*
(`symU_S q u₀ k r w x a s = -(q/2)s² + s(u₀ - k·a + r·x) + w·x`, and its
Target counterpart), not because its theorems are point checks. Rule 19 keeps
`Theory/` for statements over an arbitrary `Params`; a nine-coefficient algebraic
family is narrower than that, so `Examples/` is the correct home and the file is
deliberately not moved.

This banner exists because the filing has already misled an audit. A 2026-08-16
review classified `prop:equilibrium-patience-feedback` as a paper universal
backed only by a witness, having found the `eeCertB_*` numbers cited in the
formalization map and not the `symbolic_*` siblings here. The paper was right and
the audit was wrong. If you are deciding what a paper claim rests on, grep this
file before concluding that a family-level claim has only witness backing.

## What is symbolic here

The Sender and Target stage payoffs carry nine free real coefficients, the
transition carries a free adjustment rate, and the two discount factors and
the basin geometry are free as well:

```
U_S(x, a, s) = −(q/2)·s² + s·(u₀ − k·a + r·x) + w·x
U_T(x, a, s) = −ℓ·a + s·(n·x − c) + v·x
F(x, s)      = (1 − δ)·x + δ·s
```

* `q  > 0` — curvature of the Sender's own cost of sanctioning;
* `u₀ > 0` — the Sender's baseline marginal value of sanctioning;
* `k  > 0` — the **placation rate**: how fast Target compliance kills the
  Sender's appetite for sanctions (`∂²U_S/∂s∂a = −k < 0`, Eaton–Engers);
* `r  > 0` — the Sender's **rally slope** (`∂²U_S/∂s∂x = r`,
  Kaempfer–Lowenberg complementarity);
* `w` — the Sender's direct valuation of the political state;
* `ℓ  > 0` — the Target incumbent's per-unit cost of complying;
* `c` — the Target's per-unit pain from being sanctioned;
* `n  ≥ 0` — the Target's rally slope (`∂²U_T/∂s∂x = n`);
* `v` — the Target's direct valuation of the political state.

**No coefficient is a chosen magnitude.** The admissible region is carved out
purely by inequalities among these coefficients, the discount factors and the
basin geometry (`SymbolicEconomy` below), and that region is proved non-empty
by a backwards Fourier–Motzkin chain of `exists_between` / `exists_gt` —
`symbolicEconomy_nonempty` names no point anywhere.

## The regime: corner-pinned and decoupled

The family lives in the **corner / decoupled** regime, and the three margin
inequalities are exactly what pins it there:

* `hCorner` — the forward-looking Sender is *implacable*: its dynamic
  objective is strictly increasing in the sanction at every feasible
  `(x, a)`, so `σ_dyn ≡ 1`. In primitives: the discounted continuation gain
  `β_S·δ·K_S` strictly exceeds the largest stage disincentive `q + k − u₀`
  (full sanctions against full compliance).
* `hSMargin` — the Sender's *stage* chord slope on the basin's low-sanction
  domain still dominates that same continuation wedge. This is the
  certificate's `hS_margin`.
* `hTMargin` — the Target's stage loss rate from sanctions is covered by its
  discounted continuation gain. This is the Target loss-offset margin
  `hT_loss_margin` (a certificate field until round BJ1.4, 2026-10-07).
  Together with `ℓ > 0` it makes full defiance the Target's derived Bellman
  argmax, `α_on ≡ 0`.

Because the derived leader policy is a *constant* and the derived Sender
response is a *corner*, both cross-Lipschitz coefficients of the Schur system
vanish (`L_TS = L_ST = 0`) and the row conditions reduce to `β_T < 1`,
`β_S < 1`. This is the scope fence: the coupled interior case is **not**
attempted here.

## Closed-form value functions

With the corner pinned, both Bellman images are affine in the state, and the
Stokey–Lucas closed forms give the carriers with no free radius or slope:

* slope  `K_S = (r + w)/(1 − β_S·(1 − δ))`, `g_T = (n + v)/(1 − β_T·(1 − δ))`
  — the discounted geometric sum of the corner stage payoff's state slope,
  damped by the state-persistence weight `1 − δ`, which is the multiplier of
  `y` in the corner-pinned transition `F(y, 1) = (1 − δ)·y + δ`;
* radius `max (M_U/(1 − β)) K` — the larger of the smallest Bellman-invariant
  sup-norm radius and the pinned slope (the second only so that the affine
  generator `y ↦ K·y` fits inside its own ball).

The two equilibrium value functions themselves are affine with closed-form
coefficients (`VSstar`, `VTstar`): the slope is the constant above, and the
intercept solves the matching scalar equation `A = c₀ + β·(K·δ + A)`, i.e.
`A = (c₀ + β·K·δ)/(1 − β)`. `VSstar_bellman_fix` and `VTstar_bellman_fix`
prove these *are* the Bellman fixed points. This is the symbolic form of the
numeric witnesses' `V_S✶ = (16x + 17)/3` and `V_T✶ = (82x + 39)/11`: those two
are not independent facts but one identity evaluated at a point.

Every Bellman fixed-point step is then a `ring` / `linear_combination`
identity in the symbolic coefficients; `norm_num` on rationals appears
nowhere.

## Where this sits in the existence literature

`PaperRefer/StochasticGames/StackelbergExistenceSymbolicRoutes-synthesis-2026-08.md`
records that there is **no** general feedback-Stackelberg existence theorem for
this game class as axiomatised — Bucarey et al. (2023) §IV-B exhibit
non-existence in a two-state *finite* game — and isolates the one property all
known positive results share: *the follower's reaction set must be governed by
something other than its own continuation value* (Bucarey's MFS classes,
Escobar 2013 Cor. 4 / Bressan–Jiang 2020 Lemma 2.2 / Nowak 2007 / Balbus–
Reffett–Woźny 2013 Asm. 2).

This family satisfies that property by a route not on that list: the Sender's
reaction is **corner-dominant**. `hCorner` pins the sign of the Sender's
dynamic marginal payoff uniformly over the whole carrier, so `σ_dyn ≡ 1`
whatever the continuation value happens to be inside it — the reaction set is
continuation-*insensitive* rather than continuation-free. Nothing here
therefore contradicts the negative results, and nothing here is a general
existence theorem: it is a structurally-defined, symbolically-parameterised
subclass on which existence, uniqueness-in-carrier and the dominance headline
all go through. The interior/coupled case remains open and is fenced out
above.

The construction also follows the pattern that note recommends copying
(Curtat 1996 Thm 4.6, step 4): *the carrier radius and slope are derived from
the primitives rather than chosen*, which is stated there as exactly the
difference between a witness like `valLipGainBall 8 (4/3) (4/3) 0` and a
symbolic theorem.

## Rule compliance

**Rule 1.** No strategy is posited anywhere. `σ_dyn` is pinned at the corner
by a *proved* strict-monotonicity argument; the leader policy `α_on` is the
`ValueClass2` selector, pinned by proved state-local argmax uniqueness; the
myopic comparator's compliance is proved to be the stage argmax
(`symMyopic.α_opt`), never assumed.

**Rule 3.** `SymbolicEconomy` is a *scaffolding* structure: every field is
either a free real coefficient or an explicit inequality between such
coefficients. It carries no `Prop`-typed field of economic content (so Rule 14
laundering is impossible), it is never taken as a hypothesis of any
pre-existing theorem, and it widens no assumption surface — it is the
existence certificate of Rule 5/9, quantified over.

**Rule 5.** Everything is parametric; the numeric witnesses in the sibling
files remain as separate points and are untouched.

**Rule 9.** `symbolicEconomy_nonempty` is the non-vacuity discharge, by
`exists_between` / `exists_gt` chaining with no named point.

**Rule 19.** Sanctions-specific wiring, hence `Examples/`; the general
closed-form carrier machinery it consumes lives in
`Foundations/StokeyLucas.lean` and `Theory/Bellman/InvariantLipGainBall.lean`.
-/

import Sanctions.Examples.SubstantiveComplianceWitness
import Sanctions.Examples.WitnessKit
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Theory.Certificates.StandardComplianceMain
import Sanctions.Theory.Certificates.StandardComplianceSchur
import Sanctions.Theory.Bellman.ChordInvariance
import Sanctions.Theory.Certificates.GeneralFDischargers
-- `affine_sender_chord_on`, which discharges this economy's `hF_chord` field.
import Sanctions.Examples.AffineInstance.Certificates
import Sanctions.Examples.AffineInstance.ComplianceTower
import Sanctions.Examples.AffineInstance.TransitionChords

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame
  Sanctions.AbstractGame.Params

noncomputable section

/-! ## 0. A sup-norm bound for affine stage payoffs -/

/-- An affine function of the state with nonnegative slope is bounded on
`[0,1]` by the larger of its two endpoint absolute values. This supplies the
`M_U` input of the Stokey–Lucas radius closed form without any chosen
constant. -/
theorem abs_affine_le_max_endpoints {c₀ g y : ℝ} (hg : 0 ≤ g)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : |c₀ + g * y| ≤ max |c₀| |c₀ + g| := by
  rw [abs_le]
  constructor
  · have h1 : -|c₀| ≤ c₀ := neg_abs_le c₀
    have h2 : c₀ ≤ c₀ + g * y := by nlinarith [hy.1]
    have h3 : |c₀| ≤ max |c₀| |c₀ + g| := le_max_left _ _
    linarith
  · have h1 : c₀ + g * y ≤ c₀ + g := by nlinarith [hy.2]
    have h2 : c₀ + g ≤ |c₀ + g| := le_abs_self _
    have h3 : |c₀ + g| ≤ max |c₀| |c₀ + g| := le_max_right _ _
    linarith

/-- Affine value function with an intercept, `y ↦ A + K·y`, as a bounded
continuous function on the state space. -/
def affineIntBCF (A K : ℝ) : Val :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => A + K * y.val)
      (by fun_prop))

@[simp] theorem affineIntBCF_apply (A K : ℝ) (y : ↥(Sanctions.S : Set ℝ)) :
    affineIntBCF A K y = A + K * y.val := rfl

/-- An affine value function with nonnegative slope lies in the slope-pinned
gain ball of any radius that bounds it pointwise on the state space. -/
theorem affineIntBCF_mem_gainBall {A K M : ℝ} (hK : 0 ≤ K)
    (hM : ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → |A + K * y| ≤ M) :
    affineIntBCF A K ∈ valLipGainBall M K K 0 := by
  have hM0 : (0 : ℝ) ≤ M :=
    le_trans (abs_nonneg _) (hM 0 ⟨le_refl 0, zero_le_one⟩)
  refine ⟨?_, ?_, ?_⟩
  · rw [BoundedContinuousFunction.norm_le hM0]
    intro y
    rw [affineIntBCF_apply, Real.norm_eq_abs]
    exact hM y.val y.property
  · intro y₁ y₂
    rw [affineIntBCF_apply, affineIntBCF_apply, Subtype.dist_eq, Real.dist_eq,
      show A + K * y₂.val - (A + K * y₁.val) = K * (y₂.val - y₁.val) by ring,
      abs_mul, abs_of_nonneg hK]
    exact le_of_eq (by rw [abs_sub_comm])
  · intro y₁ y₂ _ _ hle
    have hle' : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
    rw [affineIntBCF_apply, affineIntBCF_apply, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
    nlinarith [hle']

/-! ## 1. The symbolic payoff forms -/

/-- **Sender stage payoff, symbolic.** A quadratic sanction cost with
curvature `q`, a linear marginal benefit `u₀ − k·a + r·x` (baseline `u₀`,
placated at rate `k` by Target compliance, rallied at rate `r` by the
political state), and a direct state valuation `w·x`. -/
def symU_S (q u₀ k r w : ℝ) (x a s : ℝ) : ℝ :=
  -(q / 2) * s ^ 2 + s * (u₀ - k * a + r * x) + w * x

/-- **Target stage payoff, symbolic.** A linear compliance cost `ℓ·a`, a
sanction term whose per-unit pain `c − n·x` is softened by the rally slope
`n`, and a direct state valuation `v·x`. -/
def symU_T (ℓ c n v : ℝ) (x a s : ℝ) : ℝ :=
  -ℓ * a + s * (n * x - c) + v * x

/-- **Static (myopic) Sender stage selector, symbolic**: the clipped vertex
`clip((u₀ − k·a + r·x)/q)` of the concave stage parabola. Rule 1: proved to
be the Sender's stage argmax in `symσ_isMaxOn`. -/
def symσ (q u₀ k r : ℝ) (x a : ℝ) : ℝ :=
  max 0 (min 1 ((u₀ - k * a + r * x) / q))

theorem symσ_mem (q u₀ k r : ℝ) (x a : ℝ) :
    symσ q u₀ k r x a ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem symσ_continuous (q u₀ k r : ℝ) :
    Continuous (fun (xa : ℝ × ℝ) => symσ q u₀ k r xa.1 xa.2) := by
  unfold symσ; fun_prop

/-- **Rule-1 coupling.** The clipped vertex maximises the Sender's stage
payoff on `[0,1]`: `U_S(x,a,·) = C − (q/2)·(· − t)²` with vertex
`t = (u₀ − k·a + r·x)/q`. -/
theorem symσ_isMaxOn {q : ℝ} (hq : 0 < q) (u₀ k r w : ℝ) (x a : ℝ) :
    IsMaxOn (fun s => symU_S q u₀ k r w x a s) (Set.Icc (0 : ℝ) 1)
      (symσ q u₀ k r x a) := by
  have hqne : q ≠ 0 := ne_of_gt hq
  exact WitnessKit.clipVertex_isMaxOn (by linarith : (0 : ℝ) < q / 2)
    (C := w * x + (u₀ - k * a + r * x) ^ 2 / (2 * q))
    (fun s => by simp only [symU_S]; field_simp; ring)

theorem symU_S_continuous (q u₀ k r w : ℝ) :
    Continuous (fun (xas : ℝ × ℝ × ℝ) =>
      symU_S q u₀ k r w xas.1 xas.2.1 xas.2.2) := by
  unfold symU_S; fun_prop

theorem symU_T_continuous (ℓ c n v : ℝ) :
    Continuous (fun (xas : ℝ × ℝ × ℝ) =>
      symU_T ℓ c n v xas.1 xas.2.1 xas.2.2) := by
  unfold symU_T; fun_prop

/-- **The myopic Target's stage argmax, in raw coefficients.** Complying exactly
enough to zero the static Sender's sanction, `a = (u₀ + r·x)/k`, maximises the
myopic Target's stage payoff `a ↦ U_T(x, a, σ(x, a))` over `[0,1]` whenever the
compliance cost is at most the sanction pain (`ℓ ≤ c − n·x`), the sanction-cost
curvature is at most the placation rate (`q ≤ k`), and the zeroing compliance
is at most full (`u₀ + r·x ≤ k`): the compliance the myopic Target buys never
costs more than the sanction pain it avoids. Transition-free (the myopic problem
never reads `F`), so it serves the affine family (`SymbolicEconomy.symMyopic`)
and the general family (`SymbolicEconomyF.symMyopic`) alike. Extracted from the
affine `symMyopic` with no change to the argument (plan item BJ4.6). -/
theorem symMyopic_isMaxOn {q u₀ k r ℓ c n v x : ℝ} (hq : 0 < q) (hk : 0 < k)
    (hqk : q ≤ k) (hℓ : 0 < ℓ) (hψ : ℓ ≤ c - n * x) (hTk : u₀ + r * x ≤ k) :
    IsMaxOn (fun a => symU_T ℓ c n v x a (symσ q u₀ k r x a)) Sanctions.I
      ((u₀ + r * x) / k) := by
  rw [isMaxOn_iff]
  intro a ha
  have ha0 := ha.1
  have ha1 := ha.2
  have hψ0 : 0 < c - n * x := lt_of_lt_of_le hℓ hψ
  have hσ0 : 0 ≤ symσ q u₀ k r x a := (symσ_mem _ _ _ _ x a).1
  -- The heart of it: `ℓ·(u₀ + r·x − k·a) ≤ k·σ(x,a)·(c − n·x)`, i.e. the
  -- compliance the myopic Target buys is never dearer than the sanction
  -- pain it avoids.
  have hkey : ℓ * (u₀ + r * x - k * a) ≤ k * symσ q u₀ k r x a * (c - n * x) := by
    rcases le_or_gt (u₀ + r * x) (k * a) with hc1 | hc2
    · nlinarith [hℓ, mul_nonneg (mul_nonneg hk.le hσ0) hψ0.le]
    · have hpos : 0 < (u₀ - k * a + r * x) / q := div_pos (by linarith) hq
      rcases le_or_gt ((u₀ - k * a + r * x) / q) 1 with ht1 | ht1
      · have hσ : symσ q u₀ k r x a = (u₀ - k * a + r * x) / q := by
          simp only [symσ, min_eq_right ht1, max_eq_right hpos.le]
        have hlq : ℓ * q ≤ k * (c - n * x) := by nlinarith [hqk, hℓ, hψ, hk]
        have hexp : k * ((u₀ - k * a + r * x) / q) * (c - n * x)
            = k * (c - n * x) * (u₀ - k * a + r * x) / q := by
          ring
        rw [hσ, hexp, le_div_iff₀ hq]
        nlinarith [mul_le_mul_of_nonneg_right hlq
          (by linarith : (0 : ℝ) ≤ u₀ - k * a + r * x)]
      · have hσ : symσ q u₀ k r x a = 1 := by
          simp only [symσ, min_eq_left ht1.le, max_eq_right zero_le_one]
        rw [hσ]
        nlinarith [hℓ, mul_nonneg (mul_nonneg hℓ.le ha0) hk.le]
  -- Clear the division and conclude.
  have hA : k * ((u₀ + r * x) / k) = u₀ + r * x := by
    field_simp
  have hfinal : ℓ * ((u₀ + r * x) / k) - ℓ * a
      ≤ -(symσ q u₀ k r x a * (n * x - c)) := by
    refine le_of_mul_le_mul_left ?_ hk
    calc k * (ℓ * ((u₀ + r * x) / k) - ℓ * a)
        = ℓ * (k * ((u₀ + r * x) / k) - k * a) := by ring
      _ = ℓ * (u₀ + r * x - k * a) := by rw [hA]
      _ ≤ k * symσ q u₀ k r x a * (c - n * x) := hkey
      _ = k * -(symσ q u₀ k r x a * (n * x - c)) := by ring
  have hz : symσ q u₀ k r x ((u₀ + r * x) / k) = 0 := by
    have hz0 : u₀ - k * ((u₀ + r * x) / k) + r * x = 0 := by
      field_simp; ring
    simp only [symσ, hz0, zero_div]
    norm_num
  simp only [symU_T]
  rw [hz]
  linarith [hfinal]

/-! ## 2. The admissible region -/

/-- **An admissible member of the symbolic family.**

Fourteen free real coefficients plus the inequalities that carve out the
corner/decoupled regime. Reading the three margins:

* `hCorner` — *the forward-looking Sender is implacable*. The discounted
  continuation gain from a marginal sanction (written division-free as
  `β_S·δ·(r + w)` against the denominator `1 − β_S·(1 − δ)`) strictly
  exceeds `q + k − u₀`, the largest stage disincentive the Sender can face.
  Hence `σ_dyn ≡ 1` on the carrier.
* `hSMargin` — *the Sender's stage slope still beats the wedge*. The same
  continuation quantity is strictly below `u₀ + r·x̄ − q·s̄`, the minimum
  stage chord slope of `U_S(x, 0, ·)` on the basin's low-sanction domain.
* `hTMargin` — *the Target's loss is offset*. Its stage loss rate at the
  basin bottom, `c − n·x̄`, is covered by the discounted continuation gain.

The remaining fields are sign and ordering conditions: `q ≤ r` (the rally
slope is at least the own-cost curvature, so the Sender's stage chord slope
is minimised at the basin bottom), `u₀ + r ≤ k` (full compliance can always
zero the *static* Sender's sanction, which is what gives the myopic
comparator content), and `ℓ ≤ c − n` (the Target's compliance cost never
exceeds its worst-case sanction pain, so complying to buy the sanction down
is worth it for a myopic incumbent). -/
structure SymbolicEconomy where
  /-- Adjustment rate: weight of the current sanction in the transition. -/
  δ : ℝ
  /-- Sender discount factor. -/
  βS : ℝ
  /-- Target discount factor. -/
  βT : ℝ
  /-- Curvature of the Sender's own cost of sanctioning. -/
  q : ℝ
  /-- The Sender's baseline marginal value of sanctioning. -/
  u₀ : ℝ
  /-- Placation rate `−∂²U_S/∂s∂a`. -/
  k : ℝ
  /-- Sender rally slope `∂²U_S/∂s∂x`. -/
  r : ℝ
  /-- The Sender's direct valuation of the political state. -/
  w : ℝ
  /-- The Target incumbent's per-unit cost of complying. -/
  ℓ : ℝ
  /-- The Target's per-unit pain from being sanctioned. -/
  c : ℝ
  /-- Target rally slope `∂²U_T/∂s∂x`. -/
  n : ℝ
  /-- The Target's direct valuation of the political state. -/
  v : ℝ
  /-- Basin bottom (both `xT` and `xS` of the certificate). -/
  xb : ℝ
  /-- Sanction floor of the basin. -/
  sbar : ℝ
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
  hxbs : xb ≤ sbar
  hsbar0 : 0 < sbar
  hsbar1 : sbar < 1
  /-- **Implacability**: the continuation gain dominates the worst stage
  disincentive, so the forward-looking Sender corners at full sanctions. -/
  hCorner : (q + k - u₀) * (1 - βS * (1 - δ)) < βS * δ * (r + w)
  /-- **Sender stage margin**: the same continuation wedge is strictly below
  the stage chord slope on the basin's low-sanction domain. -/
  hSMargin : βS * δ * (r + w) < (u₀ + r * xb - q * sbar) * (1 - βS * (1 - δ))
  /-- **Target loss offset**: the stage sanction loss is covered by the
  discounted continuation gain. -/
  hTMargin : (c - n * xb) * (1 - βT * (1 - δ)) ≤ βT * δ * (n + v)

namespace SymbolicEconomy

variable (E : SymbolicEconomy)

/-! ### 2a. Elementary derived facts -/

theorem ΛS_pos : 0 < 1 - E.βS * (1 - E.δ) := by
  have h : E.βS * (1 - E.δ) = E.βS - E.βS * E.δ := by ring
  have h2 : 0 ≤ E.βS * E.δ := mul_nonneg E.hβS0 E.hδ0.le
  rw [h]; linarith [E.hβS1]

theorem ΛT_pos : 0 < 1 - E.βT * (1 - E.δ) := by
  have h : E.βT * (1 - E.δ) = E.βT - E.βT * E.δ := by ring
  have h2 : 0 ≤ E.βT * E.δ := mul_nonneg E.hβT0 E.hδ0.le
  rw [h]; linarith [E.hβT1]

theorem r_pos : 0 < E.r := lt_of_lt_of_le E.hq E.hqr

theorem k_pos : 0 < E.k := by linarith [E.hk, E.hu₀, E.r_pos]

theorem q_le_k : E.q ≤ E.k := by linarith [E.hk, E.hqr, E.hu₀]

theorem xb_le_one : E.xb ≤ 1 := by linarith [E.hxbs, E.hsbar1]

/-- The worst stage disincentive the Sender can face is strictly positive:
`q + k − u₀ > 0` (full compliance more than kills the baseline appetite). -/
theorem wedge_pos : 0 < E.q + E.k - E.u₀ := by linarith [E.hk, E.hq, E.r_pos]

theorem βS_δ_pos : 0 < E.βS * E.δ := by
  rcases (mul_nonneg E.hβS0 E.hδ0.le).lt_or_eq with h | h
  · exact h
  · exfalso
    have hC := E.hCorner
    rw [← h, zero_mul] at hC
    linarith [mul_pos E.wedge_pos E.ΛS_pos]

/-- **Derived**: the Sender's corner stage payoff has strictly positive state
slope, `r + w > 0`. Not assumed — it falls out of `hCorner`. -/
theorem stageSlopeS_pos : 0 < E.r + E.w := by
  have h2 : 0 < E.βS * E.δ * (E.r + E.w) :=
    lt_trans (mul_pos E.wedge_pos E.ΛS_pos) E.hCorner
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [E.βS_δ_pos]

/-- **Derived**: the Sender's minimum basin stage chord slope is strictly
positive. Read off `hSMargin`. -/
theorem mS_pos : 0 < E.u₀ + E.r * E.xb - E.q * E.sbar := by
  have h2 : 0 < (E.u₀ + E.r * E.xb - E.q * E.sbar) * (1 - E.βS * (1 - E.δ)) :=
    lt_trans (lt_trans (mul_pos E.wedge_pos E.ΛS_pos) E.hCorner) E.hSMargin
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [E.ΛS_pos]

/-- **Derived**: the Target's stage loss rate at the basin bottom is strictly
positive (`c > n·x̄`), since `ℓ > 0` and `ℓ ≤ c − n`. -/
theorem cT_pos : 0 < E.c - E.n * E.xb := by
  have h1 : E.n * E.xb ≤ E.n := by
    nlinarith [mul_nonneg E.hn (by linarith [E.xb_le_one] : (0 : ℝ) ≤ 1 - E.xb)]
  linarith [E.hcn, E.hℓ]

theorem βT_δ_pos : 0 < E.βT * E.δ := by
  rcases (mul_nonneg E.hβT0 E.hδ0.le).lt_or_eq with h | h
  · exact h
  · exfalso
    have hT := E.hTMargin
    rw [← h, zero_mul] at hT
    linarith [mul_pos E.cT_pos E.ΛT_pos]

/-- **Derived**: the Target's corner stage payoff has strictly positive state
slope, `n + v > 0`. Read off `hTMargin`. -/
theorem stageSlopeT_pos : 0 < E.n + E.v := by
  have h2 : 0 < E.βT * E.δ * (E.n + E.v) :=
    lt_of_lt_of_le (mul_pos E.cT_pos E.ΛT_pos) E.hTMargin
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [E.βT_δ_pos]

/-! ### 2b. Closed-form derived scalars

Nothing below is chosen: each is the Stokey–Lucas closed form evaluated at
the family's own primitives, along the *derived* corner path. -/

/-- Sender corner stage payoff intercept, `U_S(0, 0, 1) = u₀ − q/2`. -/
def stageS0 : ℝ := E.u₀ - E.q / 2

/-- Sender corner stage payoff state slope, `r + w`. -/
def stageSlopeS : ℝ := E.r + E.w

/-- Sup-norm of the Sender's corner stage payoff on the state space. -/
def stageNormS : ℝ := max |E.stageS0| |E.stageS0 + E.stageSlopeS|

/-- Target corner stage payoff intercept, `U_T(0, 0, 1) = −c`. -/
def stageT0 : ℝ := -E.c

/-- Target corner stage payoff state slope, `n + v`. -/
def stageSlopeT : ℝ := E.n + E.v

/-- Sup-norm of the Target's corner stage payoff on the state space. -/
def stageNormT : ℝ := max |E.stageT0| |E.stageT0 + E.stageSlopeT|

/-- **Sender value slope, closed form.** `K_S = (r + w)/(1 − β_S·(1 − δ))`:
the Hinderer 4.2(c) constant at transition multiplier `1 − δ`, the multiplier of the
state along the corner-pinned path `y ↦ F(y, 1) = (1 − δ)·y + δ`. -/
def KS : ℝ := StokeyLucas.bellmanLipConstant E.βS (1 - E.δ) E.stageSlopeS

/-- **Target value slope, closed form.** `g_T = (n + v)/(1 − β_T·(1 − δ))`. -/
def gT : ℝ := StokeyLucas.bellmanLipConstant E.βT (1 - E.δ) E.stageSlopeT

/-- Sender carrier radius: the larger of the smallest Bellman-invariant
sup-norm radius `M_U/(1 − β_S)` and the pinned slope `K_S` (the latter only so
that the affine generator `y ↦ K_S·y` fits inside its own ball). -/
def MS : ℝ := max (StokeyLucas.bellmanNormBound E.βS E.stageNormS) E.KS

/-- Target carrier radius, same construction. -/
def MT : ℝ := max (StokeyLucas.bellmanNormBound E.βT E.stageNormT) E.gT

theorem KS_pos : 0 < E.KS := by
  simp only [KS, StokeyLucas.bellmanLipConstant_def, stageSlopeS]
  exact div_pos E.stageSlopeS_pos E.ΛS_pos

theorem gT_pos : 0 < E.gT := by
  simp only [gT, StokeyLucas.bellmanLipConstant_def, stageSlopeT]
  exact div_pos E.stageSlopeT_pos E.ΛT_pos

theorem KS_le_MS : E.KS ≤ E.MS := le_max_right _ _

theorem gT_le_MT : E.gT ≤ E.MT := le_max_right _ _

/-! ### 2c. The margins in value-slope form

The three division-free structure fields become the three quantities the
certificate actually consumes. -/

/-- **Implacability, in value-slope form**: `q + k − u₀ < β_S·δ·K_S`. -/
theorem corner_margin : E.q + E.k - E.u₀ < E.βS * E.δ * E.KS := by
  have hΛ := E.ΛS_pos
  have hEq : E.βS * E.δ * E.KS
      = E.βS * E.δ * E.stageSlopeS / (1 - E.βS * (1 - E.δ)) := by
    simp only [KS, StokeyLucas.bellmanLipConstant_def]; ring
  rw [hEq, lt_div_iff₀ hΛ]
  simpa only [stageSlopeS] using E.hCorner

/-- **Sender stage margin, in value-slope form**: `β_S·K_S·δ < m_S`, the
certificate's `hS_margin`. -/
theorem sender_stage_margin :
    E.βS * E.KS * E.δ < E.u₀ + E.r * E.xb - E.q * E.sbar := by
  have hΛ := E.ΛS_pos
  have hEq : E.βS * E.KS * E.δ
      = E.βS * E.δ * E.stageSlopeS / (1 - E.βS * (1 - E.δ)) := by
    simp only [KS, StokeyLucas.bellmanLipConstant_def]; ring
  rw [hEq, div_lt_iff₀ hΛ]
  simpa only [stageSlopeS] using E.hSMargin

/-- **Target loss offset, in value-slope form**: `c_T ≤ β_T·g_T·δ`, the Target
loss-offset margin `hT_loss_margin` (a certificate field until round BJ1.4,
2026-10-07, which deleted the Target loss-offset stack from the certificate). -/
theorem target_loss_margin :
    E.c - E.n * E.xb ≤ E.βT * E.gT * E.δ := by
  have hΛ := E.ΛT_pos
  have hEq : E.βT * E.gT * E.δ
      = E.βT * E.δ * E.stageSlopeT / (1 - E.βT * (1 - E.δ)) := by
    simp only [gT, StokeyLucas.bellmanLipConstant_def]; ring
  rw [hEq, le_div_iff₀ hΛ]
  simpa only [stageSlopeT] using E.hTMargin

/-! ## 3. The economy as a `Params` -/

/-- **The symbolic family's `Params`.** Every structural field is discharged
from the admissibility inequalities alone. -/
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
  F := AbstractGame.affineF E.δ
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨E.hδ0, E.hδ1⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨E.hδ0, E.hδ1⟩
  F_diag := AbstractGame.affineF_diag _

/-- **`E.toParams` has a continuous static Sender selector.** Affine-restricted: the
family's transition is `affineF E.δ`; derived from the closed form of its selector
(`symσ_continuous`), which does not read the transition. The proof is the one that was the
economy's `σ_continuous` field until round BJ5.1 (2026-10-07), when the condition left
`Params` for the class `Params.StaticSelectorContinuous`; the myopic-comparator and
static-Sender results can use it at this economy. -/
instance toParams_staticSelectorContinuous :
    E.toParams.StaticSelectorContinuous where
  σ_continuous := symσ_continuous _ _ _ _

@[simp] theorem toParams_U_S : E.toParams.U_S = symU_S E.q E.u₀ E.k E.r E.w := rfl
@[simp] theorem toParams_U_T : E.toParams.U_T = symU_T E.ℓ E.c E.n E.v := rfl
@[simp] theorem toParams_σ : E.toParams.σ = symσ E.q E.u₀ E.k E.r := rfl
@[simp] theorem toParams_δ : E.toParams.δ = E.δ := rfl
@[simp] theorem toParams_β_S : E.toParams.β_S = E.βS := rfl
@[simp] theorem toParams_β_T : E.toParams.β_T = E.βT := rfl

/-- Transition closed form. -/
theorem toParams_F_apply (x s : ℝ) :
    E.toParams.F x s = (1 - E.δ) * x + E.δ * s := rfl

/-- The corner-pinned transition `F(y, 1)`, written in the shape the
Stokey–Lucas closed-form carrier lemma expects (transition multiplier
`1 − δ`). -/
theorem toParams_F_one (y : ℝ) :
    E.toParams.F y 1 = (1 - E.δ) * y + (1 - (1 - E.δ)) := by
  rw [toParams_F_apply]; ring

theorem F_mem_Icc {x s : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (1 - E.δ) * x + E.δ * s ∈ Set.Icc (0 : ℝ) 1 := by
  have h := E.toParams.F_mem x s hx hs
  rwa [toParams_F_apply] at h

/-! ## 4. Carriers at the closed forms -/

/-- **Sender carrier**: the slope-pinned gain ball at the Stokey–Lucas closed
forms. Its members are exactly the affine functions of slope `K_S`. -/
def carrierS : Set Val := valLipGainBall E.MS E.KS E.KS 0

/-- **Target carrier**: same construction at `g_T`. -/
def carrierT : Set Val := valLipGainBall E.MT E.gT E.gT 0

theorem carrierS_nonempty : E.carrierS.Nonempty :=
  ⟨affineBCF E.KS, affineBCF_mem_gainBall E.KS_pos.le E.KS_le_MS⟩

theorem carrierT_nonempty : E.carrierT.Nonempty :=
  ⟨affineBCF E.gT, affineBCF_mem_gainBall E.gT_pos.le E.gT_le_MT⟩

/-- **Affine extraction on the Sender carrier**: carrier membership alone pins
the value difference between two political states. -/
theorem carrierS_diff {V : Val} (hV : V ∈ E.carrierS) {z₁ z₂ : ℝ}
    (h1 : z₁ ∈ Set.Icc (0 : ℝ) 1) (h2 : z₂ ∈ Set.Icc (0 : ℝ) 1) :
    V (Sanctions.clipS' z₂) - V (Sanctions.clipS' z₁) = E.KS * (z₂ - z₁) :=
  AbstractGame.Params.valLipGainBall_clip_diff E.KS_pos.le hV h1 h2

/-! ## 5. The Sender's derived response is the corner `σ_dyn ≡ 1` -/

/-- **The Sender's dynamic objective is strictly increasing in the sanction**
at every feasible state and every feasible compliance, for every value
function in the carrier. This is `hCorner` doing its work: the discounted
continuation gain `β_S·K_S·δ` outweighs the worst stage disincentive. -/
theorem senderObj_strictMonoOn {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    StrictMonoOn
      (fun s => E.toParams.U_S x a s
        + E.toParams.β_S * V_S (Sanctions.clipS' (E.toParams.F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hm₁ := E.F_mem_Icc hx hs₁
  have hm₂ := E.F_mem_Icc hx hs₂
  have hdiff := E.carrierS_diff hV_S hm₁ hm₂
  have hstep : (1 - E.δ) * x + E.δ * s₂ - ((1 - E.δ) * x + E.δ * s₁)
      = E.δ * (s₂ - s₁) := by ring
  rw [hstep] at hdiff
  have hbr : 0 < E.u₀ - E.k * a + E.r * x - E.q / 2 * (s₁ + s₂)
      + E.βS * E.δ * E.KS := by
    nlinarith [E.corner_margin, mul_nonneg E.k_pos.le (sub_nonneg.mpr ha.2),
      mul_nonneg E.r_pos.le hx.1,
      mul_nonneg E.hq.le (by linarith [hs₁.2, hs₂.2] : (0 : ℝ) ≤ 2 - s₁ - s₂)]
  have hprod := mul_pos (show (0 : ℝ) < s₂ - s₁ by linarith) hbr
  have hscaled : E.βS * V_S (Sanctions.clipS' ((1 - E.δ) * x + E.δ * s₂))
      - E.βS * V_S (Sanctions.clipS' ((1 - E.δ) * x + E.δ * s₁))
      = E.βS * (E.KS * (E.δ * (s₂ - s₁))) := by
    rw [← hdiff]; ring
  simp only [toParams_U_S, symU_S, toParams_β_S, toParams_F_apply]
  nlinarith [hprod, hscaled]

/-- **`σ_dyn` pinned at full sanctions** for every carrier value function, at
every feasible state and compliance. -/
theorem σ_dyn_eq_one {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    E.toParams.σ_dyn V_S x a = 1 :=
  WitnessKit.σ_dyn_eq_one_of_strictMonoOn (E.senderObj_strictMonoOn hV_S hx ha)

/-- **`σ_dyn_top` pinned at full sanctions**: the upper-selector Sender
response used by the top equilibrium's realised rule coincides with the
unique argmax `1`. -/
theorem σ_dyn_top_eq_one {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    E.toParams.σ_dyn_top V_S x a = 1 :=
  WitnessKit.σ_dyn_top_eq_one_of_strictMonoOn
    (E.senderObj_strictMonoOn hV_S hx ha)

/-! ## 6. State-local argmax uniqueness -/

/-- **Sender argmax uniqueness on the carrier.** On the state space the
Sender's dynamic objective is a strictly concave parabola in the sanction:
the clip is inactive and the carrier value function is exactly affine. -/
theorem DAU_on_carrier {V_S : Val} (hV_S : V_S ∈ E.carrierS) :
    E.toParams.DynamicArgmaxUnique V_S := by
  apply E.toParams.dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  set c₀ := V_S (Sanctions.clipS' 0) with hc₀
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hQ : ∀ s ∈ Sanctions.I,
      E.toParams.U_S x a s
          + E.toParams.β_S * V_S (Sanctions.clipS' (E.toParams.F x s))
        = -(E.q / 2) * s ^ 2
          + (E.u₀ - E.k * a + E.r * x + E.βS * E.KS * E.δ) * s
          + (E.w * x + E.βS * (c₀ + E.KS * ((1 - E.δ) * x))) := by
    intro s hs
    have hmem := E.F_mem_Icc hx hs
    have hdiff := E.carrierS_diff hV_S h0 hmem
    simp only [toParams_U_S, symU_S, toParams_β_S, toParams_F_apply]
    rw [hc₀]
    linear_combination E.βS * hdiff
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne p₁ p₂ hp hq hpq
  have hq_eq : p₂ = 1 - p₁ := by linarith
  subst hq_eq
  have hmid : p₁ * s₁ + (1 - p₁) * s₂ ∈ Sanctions.I :=
    ⟨by nlinarith [hs₁.1, hs₂.1, hp.le, hq.le],
     by nlinarith [hs₁.2, hs₂.2, hp.le, hq.le]⟩
  simp only [smul_eq_mul, hQ s₁ hs₁, hQ s₂ hs₂, hQ _ hmid]
  have hsq : (s₁ - s₂) ^ 2 > 0 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  nlinarith [mul_pos (mul_pos hp hq) hsq, E.hq]

/-- **The joint Target integrand in closed form** at every feasible state:
with `σ_dyn ≡ 1`, compliance only costs `ℓ` per unit and buys nothing. -/
theorem joint_T_integrand_eq (V_T : Val) {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    E.toParams.joint_T_integrand V_T V_S x a
      = -E.ℓ * a + (E.stageT0 + E.stageSlopeT * x)
        + E.βT * V_T (Sanctions.clipS' ((1 - E.δ) * x + (1 - (1 - E.δ)))) := by
  have hσ := E.σ_dyn_eq_one hV_S hx ha
  simp only [AbstractGame.Params.joint_T_integrand, hσ]
  rw [E.toParams_F_one x]
  simp only [toParams_U_T, symU_T, toParams_β_T, stageT0, stageSlopeT]
  ring

/-- **Target argmax uniqueness on the carriers**: the joint integrand is
strictly decreasing in compliance (`ℓ > 0`), so two mutually-dominating
maximisers coincide. -/
theorem TAU_on_carriers (V_T V_S : Val) (hV_S : V_S ∈ E.carrierS) :
    E.toParams.TargetArgmaxUnique V_T V_S :=
  WitnessKit.targetArgmaxUnique_of_strictAntiOn
    fun x hx a₁ ha₁ a₂ ha₂ hlt => by
      simp only [E.joint_T_integrand_eq V_T hV_S hx ha₁,
        E.joint_T_integrand_eq V_T hV_S hx ha₂]
      nlinarith [E.hℓ]

/-- **Full defiance is the Target's argmax** at every feasible state. -/
theorem zero_isMaxOn_joint (V_T : Val) {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IsMaxOn (fun a => E.toParams.joint_T_integrand V_T V_S x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [E.joint_T_integrand_eq V_T hV_S hx ha,
    E.joint_T_integrand_eq V_T hV_S hx
      (⟨le_refl 0, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I)]
  nlinarith [ha.1, E.hℓ]

/-! ## 7. The value class and its derived leader policy -/

/-- **The asymmetric value class of the symbolic family.** -/
def valueClass : E.toParams.ValueClass2 where
  carrier_T := E.carrierT
  carrier_S := E.carrierS
  isClosed_T := valLipGainBall_isClosed _ _ _ _
  isClosed_S := valLipGainBall_isClosed _ _ _ _
  nonempty_T := E.carrierT_nonempty
  nonempty_S := E.carrierS_nonempty
  sender_unique_on := fun _ hV_S => (E.DAU_on_carrier hV_S).toOnI
  target_unique_on := fun V_T _ V_S hV_S => E.TAU_on_carriers V_T V_S hV_S

/-- **The derived leader policy is the defiance corner, `α_on ≡ 0`.** Rule 1:
this is the *argmax* of the joint dynamic objective, pinned by state-local
uniqueness — nothing is assumed about the Target's behaviour. -/
theorem α_on_eq_zero (V_T : E.valueClass.CarrierT) (V_S : E.valueClass.CarrierS) :
    E.valueClass.α_on V_T V_S = fun _ => (0 : ℝ) :=
  WitnessKit.α_on_eq_zero_of_zero_isMaxOn V_T V_S fun y =>
    E.zero_isMaxOn_joint V_T.val V_S.property y.property

/-! ## 8. Bellman images in closed form, and carrier invariance -/

/-- **Target Bellman image in closed form**: the sSup over compliance
collapses at the defiance corner. -/
theorem jointTarget_image (V_T : E.valueClass.CarrierT)
    (V_S : E.valueClass.CarrierS) (y : ↥(Sanctions.S : Set ℝ)) :
    E.toParams.jointTarget_BCF_on_S V_T.val V_S.val
        (E.valueClass.sender_unique_on V_S.val V_S.property) y
      = E.stageT0 + E.stageSlopeT * y.val
        + E.βT * V_T.val
            (Sanctions.clipS' ((1 - E.δ) * y.val + (1 - (1 - E.δ)))) := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn V_T.val V_S.val
        (E.valueClass.sender_unique_on V_S.val V_S.property) y
        (⟨le_refl 0, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I)
        (E.zero_isMaxOn_joint V_T.val V_S.property y.property),
      E.joint_T_integrand_eq V_T.val V_S.property y.property
        (⟨le_refl 0, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I)]
  ring

/-- **Sender Bellman image in closed form** at the derived defiance policy:
the sSup over sanctions collapses at the corner `s = 1`. -/
theorem bellmanS_image {W : Val} (hW : W ∈ E.carrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    E.toParams.bellmanS_BCF (fun _ => 0) continuous_const W y
      = E.stageS0 + E.stageSlopeS * y.val
        + E.βS * W (Sanctions.clipS' ((1 - E.δ) * y.val + (1 - (1 - E.δ)))) := by
  have h1I : (1 : ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_refl 1⟩
  have hmono := E.senderObj_strictMonoOn hW y.property
    (⟨le_refl 0, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I)
  have hmax : IsMaxOn
      (fun s => E.toParams.U_S y.val 0 s
        + E.toParams.β_S * W (Sanctions.clipS' (E.toParams.F y.val s)))
      Sanctions.I 1 := by
    rw [isMaxOn_iff]
    intro s hs
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · rw [heq]
    · exact le_of_lt (hmono hs h1I hlt)
  rw [WitnessKit.bellmanS_image_of_isMaxOn (p := E.toParams)
      continuous_const W y h1I hmax, E.toParams_F_one y.val]
  simp only [toParams_U_S, symU_S, toParams_β_S, stageS0, stageSlopeS]
  ring

/-- **Heterogeneous carrier invariance**, discharged by the general
two-sided-band lemma `mem_valLipGainBall_bellman_chord`: the transition
enters only through `CornerStateChord F glo ghi`, here at the degenerate
band `glo = ghi = 1 − δ`, so no step forces the Bellman image's successor
to be an exact affine expression. (The family's own `F` is still
`affineF δ` by construction — see `SymbolicCertifiedFamilyGeneralF` for
the general-`F` sibling of this family.) Both Bellman images are
corner-pinned affine, so each
re-enters *the same* ball: the image slope is `g_U + β·K·(1 − δ)`, which is
`K` exactly because `K` is the SLP closed form, and the image sup-norm is at
most `M_U + β·M`, which is at most `M` exactly because `M` dominates the
radius closed form. -/
theorem valueClass_IsInvariant : E.valueClass.IsInvariant := by
  have hδ0 : (0 : ℝ) ≤ 1 - E.δ := by linarith [E.hδ1]
  have hβghiT : E.βT * (1 - E.δ) < 1 := by linarith [E.ΛT_pos]
  have hβghiS : E.βS * (1 - E.δ) < 1 := by linarith [E.ΛS_pos]
  have hFmem : ∀ y ∈ Set.Icc (0 : ℝ) 1, E.toParams.F y 1 ∈ Set.Icc (0 : ℝ) 1 :=
    fun y hy => E.toParams.F_mem y 1 hy ⟨zero_le_one, le_refl 1⟩
  have hband : Sanctions.TransitionChords.CornerStateChord E.toParams.F
      (1 - E.δ) (1 - E.δ) := by
    intro y₁ y₂ _ _ hle
    rw [E.toParams_F_one y₁, E.toParams_F_one y₂]
    constructor <;> nlinarith [sub_nonneg.mpr hle]
  intro V_T V_S
  constructor
  · change E.toParams.jointTarget_BCF_on_S V_T.val V_S.val
        (E.valueClass.sender_unique_on V_S.val V_S.property) ∈ E.carrierT
    refine AbstractGame.Params.mem_valLipGainBall_bellman_chord
      (β := E.βT) (glo := 1 - E.δ) (ghi := 1 - E.δ) (c₀ := E.stageT0)
      (L_U := E.stageSlopeT) (g_U := E.stageSlopeT) (M_U := E.stageNormT)
      (stage := fun y => E.stageSlopeT * y) (F := E.toParams.F)
      E.hβT0 E.hβT1 hδ0 hβghiT E.stageSlopeT_pos.le E.gT_pos.le
      (fun z hz => abs_affine_le_max_endpoints E.stageSlopeT_pos.le hz) ?_ ?_
      hFmem hband (le_max_left _ _) le_rfl
      (le_of_eq (StokeyLucas.bellmanLowerSlopeConstant_eq_bellmanLipConstant _ _ _).symm)
      V_T.property ?_
    · intro y₁ _ y₂ _
      rw [show E.stageSlopeT * y₂ - E.stageSlopeT * y₁
          = E.stageSlopeT * (y₂ - y₁) by ring, abs_mul,
        abs_of_nonneg (show (0:ℝ) ≤ E.stageSlopeT from
          E.stageSlopeT_pos.le)]
    · intro y₁ _ y₂ _ _
      exact le_of_eq (by ring)
    · intro y
      rw [E.toParams_F_one y.val]
      exact E.jointTarget_image V_T V_S y
  · change E.toParams.bellmanS_BCF (E.valueClass.α_on V_T V_S)
        (E.valueClass.α_on_continuous V_T V_S) V_S.val ∈ E.carrierS
    rw [WitnessKit.bellmanS_BCF_congr_α (E.α_on_eq_zero V_T V_S)
        (E.valueClass.α_on_continuous V_T V_S) continuous_const V_S.val]
    refine AbstractGame.Params.mem_valLipGainBall_bellman_chord
      (β := E.βS) (glo := 1 - E.δ) (ghi := 1 - E.δ) (c₀ := E.stageS0)
      (L_U := E.stageSlopeS) (g_U := E.stageSlopeS) (M_U := E.stageNormS)
      (stage := fun y => E.stageSlopeS * y) (F := E.toParams.F)
      E.hβS0 E.hβS1 hδ0 hβghiS E.stageSlopeS_pos.le E.KS_pos.le
      (fun z hz => abs_affine_le_max_endpoints E.stageSlopeS_pos.le hz) ?_ ?_
      hFmem hband (le_max_left _ _) le_rfl
      (le_of_eq (StokeyLucas.bellmanLowerSlopeConstant_eq_bellmanLipConstant _ _ _).symm)
      V_S.property ?_
    · intro y₁ _ y₂ _
      rw [show E.stageSlopeS * y₂ - E.stageSlopeS * y₁
          = E.stageSlopeS * (y₂ - y₁) by ring, abs_mul,
        abs_of_nonneg (show (0:ℝ) ≤ E.stageSlopeS from
          E.stageSlopeS_pos.le)]
    · intro y₁ _ y₂ _ _
      exact le_of_eq (by ring)
    · intro y
      rw [E.toParams_F_one y.val]
      exact E.bellmanS_image V_S.property y

/-! ## 8b. The equilibrium value functions in closed form

With an affine-quadratic stage payoff, an affine transition and a
corner-pinned policy pair, the Bellman fixed point is **affine**, and both of
its coefficients are closed forms in the primitives:

* the slope is the Stokey–Lucas constant already carrying the carrier,
  `K = g_U/(1 − β(1 − δ))`;
* the intercept solves the matching scalar linear equation
  `A = c₀ + β·(K·δ + A)`, i.e. `A = (c₀ + β·K·δ)/(1 − β)`.

This is the symbolic form of what appears at the numeric witnesses as
`V_S✶ = (16x + 17)/3` and `V_T✶ = (82x + 39)/11`: those two are not
independent facts but this one identity evaluated at a point. Here both
fixed-point proofs are `linear_combination` identities in the free
coefficients. -/

/-- The corner-pinned transition never leaves the state space. -/
theorem cornerNext_mem {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (1 - E.δ) * y + (1 - (1 - E.δ)) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> nlinarith [hy.1, hy.2, E.hδ0, E.hδ1]

/-- **The Stokey–Lucas Hinderer 4.2(c) slope margin at this economy**: the image slope
`g_U + β_S·K_S·(1 − δ)` re-enters at `K_S` exactly because `K_S` is the
closed form. -/
theorem KS_margin : E.stageSlopeS + E.βS * E.KS * (1 - E.δ) = E.KS := by
  have h := (StokeyLucas.bellman_closed_form_lipschitz_margin (β := E.βS)
      (γ := 1 - E.δ) (L_U := E.stageSlopeS) E.stageSlopeS_pos.le E.hβS0
      (by linarith [E.hδ1]) (by linarith [E.ΛS_pos])).2
  simpa only [KS, StokeyLucas.bellmanLipConstant_def] using h

/-- The same margin on the Target side. -/
theorem gT_margin : E.stageSlopeT + E.βT * E.gT * (1 - E.δ) = E.gT := by
  have h := (StokeyLucas.bellman_closed_form_lipschitz_margin (β := E.βT)
      (γ := 1 - E.δ) (L_U := E.stageSlopeT) E.stageSlopeT_pos.le E.hβT0
      (by linarith [E.hδ1]) (by linarith [E.ΛT_pos])).2
  simpa only [gT, StokeyLucas.bellmanLipConstant_def] using h

/-- **Sender equilibrium value intercept, closed form**:
`A_S = (c₀ + β_S·K_S·δ)/(1 − β_S)`. -/
def VSint : ℝ := (E.stageS0 + E.βS * E.KS * E.δ) / (1 - E.βS)

/-- **Target equilibrium value intercept, closed form**. -/
def VTint : ℝ := (E.stageT0 + E.βT * E.gT * E.δ) / (1 - E.βT)

theorem VSint_mul : E.VSint * (1 - E.βS) = E.stageS0 + E.βS * E.KS * E.δ := by
  have hne : (1 : ℝ) - E.βS ≠ 0 := ne_of_gt (by linarith [E.hβS1])
  simp only [VSint]
  field_simp

theorem VTint_mul : E.VTint * (1 - E.βT) = E.stageT0 + E.βT * E.gT * E.δ := by
  have hne : (1 : ℝ) - E.βT ≠ 0 := ne_of_gt (by linarith [E.hβT1])
  simp only [VTint]
  field_simp

theorem VSint_fix : E.stageS0 + E.βS * (E.KS * E.δ + E.VSint) = E.VSint := by
  linear_combination -E.VSint_mul

theorem VTint_fix : E.stageT0 + E.βT * (E.gT * E.δ + E.VTint) = E.VTint := by
  linear_combination -E.VTint_mul

theorem VSint_add_KS :
    E.VSint + E.KS = (E.stageS0 + E.stageSlopeS) / (1 - E.βS) := by
  have hne : (1 : ℝ) - E.βS ≠ 0 := ne_of_gt (by linarith [E.hβS1])
  rw [eq_div_iff hne]
  linear_combination E.VSint_mul - E.KS_margin

theorem VTint_add_gT :
    E.VTint + E.gT = (E.stageT0 + E.stageSlopeT) / (1 - E.βT) := by
  have hne : (1 : ℝ) - E.βT ≠ 0 := ne_of_gt (by linarith [E.hβT1])
  rw [eq_div_iff hne]
  linear_combination E.VTint_mul - E.gT_margin

/-- **The Sender's closed-form equilibrium value function**, `y ↦ A_S + K_S·y`. -/
def VSstar : Val := affineIntBCF E.VSint E.KS

/-- **The Target's closed-form equilibrium value function**. -/
def VTstar : Val := affineIntBCF E.VTint E.gT

theorem VSstar_mem : E.VSstar ∈ E.carrierS := by
  have hb : (0 : ℝ) < 1 - E.βS := by linarith [E.hβS1]
  have hN0 : |E.stageS0| ≤ E.stageNormS := le_max_left _ _
  have hN1 : |E.stageS0 + E.stageSlopeS| ≤ E.stageNormS := le_max_right _ _
  have hlow : -(E.stageNormS / (1 - E.βS)) ≤ E.VSint := by
    have h1 : E.stageS0 / (1 - E.βS) ≤ E.VSint := by
      rw [VSint, div_le_div_iff_of_pos_right hb]
      nlinarith [mul_nonneg (mul_nonneg E.hβS0 E.KS_pos.le) E.hδ0.le]
    have h2 : -(E.stageNormS / (1 - E.βS)) ≤ E.stageS0 / (1 - E.βS) := by
      rw [neg_div' , div_le_div_iff_of_pos_right hb]
      linarith [neg_abs_le E.stageS0]
    linarith
  have hhigh : E.VSint + E.KS ≤ E.stageNormS / (1 - E.βS) := by
    rw [VSint_add_KS, div_le_div_iff_of_pos_right hb]
    linarith [le_abs_self (E.stageS0 + E.stageSlopeS)]
  refine affineIntBCF_mem_gainBall E.KS_pos.le (fun y hy => ?_)
  have hmid1 : E.VSint ≤ E.VSint + E.KS * y := by
    nlinarith [E.KS_pos, hy.1]
  have hmid2 : E.VSint + E.KS * y ≤ E.VSint + E.KS := by
    nlinarith [E.KS_pos, hy.2]
  have hMS : E.stageNormS / (1 - E.βS) ≤ E.MS := by
    simpa only [MS, StokeyLucas.bellmanNormBound_def] using
      (le_max_left (E.stageNormS / (1 - E.βS)) E.KS)
  rw [abs_le]
  constructor <;> linarith

theorem VTstar_mem : E.VTstar ∈ E.carrierT := by
  have hb : (0 : ℝ) < 1 - E.βT := by linarith [E.hβT1]
  have hN0 : |E.stageT0| ≤ E.stageNormT := le_max_left _ _
  have hN1 : |E.stageT0 + E.stageSlopeT| ≤ E.stageNormT := le_max_right _ _
  have hlow : -(E.stageNormT / (1 - E.βT)) ≤ E.VTint := by
    have h1 : E.stageT0 / (1 - E.βT) ≤ E.VTint := by
      rw [VTint, div_le_div_iff_of_pos_right hb]
      nlinarith [mul_nonneg (mul_nonneg E.hβT0 E.gT_pos.le) E.hδ0.le]
    have h2 : -(E.stageNormT / (1 - E.βT)) ≤ E.stageT0 / (1 - E.βT) := by
      rw [neg_div', div_le_div_iff_of_pos_right hb]
      linarith [neg_abs_le E.stageT0]
    linarith
  have hhigh : E.VTint + E.gT ≤ E.stageNormT / (1 - E.βT) := by
    rw [VTint_add_gT, div_le_div_iff_of_pos_right hb]
    linarith [le_abs_self (E.stageT0 + E.stageSlopeT)]
  refine affineIntBCF_mem_gainBall E.gT_pos.le (fun y hy => ?_)
  have hmid1 : E.VTint ≤ E.VTint + E.gT * y := by
    nlinarith [E.gT_pos, hy.1]
  have hmid2 : E.VTint + E.gT * y ≤ E.VTint + E.gT := by
    nlinarith [E.gT_pos, hy.2]
  have hMT : E.stageNormT / (1 - E.βT) ≤ E.MT := by
    simpa only [MT, StokeyLucas.bellmanNormBound_def] using
      (le_max_left (E.stageNormT / (1 - E.βT)) E.gT)
  rw [abs_le]
  constructor <;> linarith

/-- **The Sender's closed-form value function is a Bellman fixed point** at
the derived defiance policy. Proved as a `linear_combination` of the slope
margin and the intercept equation — no numerics anywhere. -/
theorem VSstar_bellman_fix :
    E.toParams.bellmanS_BCF (fun _ => 0) continuous_const E.VSstar = E.VSstar := by
  ext y
  rw [E.bellmanS_image E.VSstar_mem y]
  simp only [VSstar, affineIntBCF_apply,
    clipS'_val_of_mem (E.cornerNext_mem y.property)]
  linear_combination y.val * E.KS_margin + E.VSint_fix

/-- **The Target's closed-form value function is a fixed point of the joint
Target Bellman operator**, at every Sender value in the carrier (the operator
is `V_S`-independent because `σ_dyn ≡ 1` there). -/
theorem VTstar_bellman_fix (V_S : E.valueClass.CarrierS) :
    E.toParams.jointTarget_BCF_on_S E.VTstar V_S.val
        (E.valueClass.sender_unique_on V_S.val V_S.property) = E.VTstar := by
  ext y
  rw [E.jointTarget_image ⟨E.VTstar, E.VTstar_mem⟩ V_S y]
  simp only [VTstar, affineIntBCF_apply,
    clipS'_val_of_mem (E.cornerNext_mem y.property)]
  linear_combination y.val * E.gT_margin + E.VTint_fix

/-! ## 9. Decoupled Schur rows -/

/-- **Target row**: self coefficient `β_T`, cross coefficient `L_TS = 0` (the
Target image is `V_S`-independent because `σ_dyn ≡ 1` on the carrier). -/
theorem hT_T_op (h_inv : E.valueClass.IsInvariant)
    (V V' : E.valueClass.CarrierT) (W W' : E.valueClass.CarrierS) :
    dist (E.valueClass.jointTargetOp_sub h_inv (V, W))
          (E.valueClass.jointTargetOp_sub h_inv (V', W'))
      ≤ E.βT * dist V V' + 0 * dist W W' :=
  WitnessKit.jointTargetOp_sub_dist_le_of_image h_inv
    (g := fun z => E.stageT0 + E.stageSlopeT * z)
    (φ := fun z => (1 - E.δ) * z + (1 - (1 - E.δ)))
    (fun V W y => E.jointTarget_image V W y) V V' W W'

/-- **Sender row**: self coefficient `β_S`, cross coefficient `L_ST = 0` (the
Sender operator is `V_T`-independent because the derived leader policy is the
constant `α_on ≡ 0` for every carrier pair). -/
theorem hT_S_op (h_inv : E.valueClass.IsInvariant)
    (V V' : E.valueClass.CarrierT) (W W' : E.valueClass.CarrierS) :
    dist (E.valueClass.jointSenderOp_sub h_inv (V, W))
          (E.valueClass.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + E.βS * dist W W' :=
  WitnessKit.jointSenderOp_sub_dist_le_of_defiance h_inv E.α_on_eq_zero V V' W W'

/-! ## 10. The myopic comparator

The *static* Sender is placable: its stage response `σ(x, a)` falls at rate
`k/q` in compliance. Because `u₀ + r ≤ k`, the myopic Target can always
afford to zero the sanction out entirely, and because `ℓ ≤ c − n` it wants
to. So the myopic regime realises **no sanctions at all** — against the
forward-looking regime's full sanctions. -/

/-- **The myopic Target's compliance**: exactly the amount that zeroes the
static Sender's sanction, `a = (u₀ + r·x)/k`. Proved optimal below. -/
def myopicAlpha (x : ℝ) : ℝ := (E.u₀ + E.r * x) / E.k

theorem myopicAlpha_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    E.myopicAlpha x ∈ Set.Icc (0 : ℝ) 1 := by
  have hk := E.k_pos
  change (E.u₀ + E.r * x) / E.k ∈ Set.Icc (0 : ℝ) 1
  constructor
  · exact div_nonneg (by nlinarith [E.hu₀, E.r_pos, hx.1]) hk.le
  · rw [div_le_one hk]
    nlinarith [E.hk, E.r_pos, hx.2]

/-- The myopic compliance zeroes the static Sender's sanction. -/
theorem myopic_sigma_eq_zero (x : ℝ) :
    E.toParams.σ x (E.myopicAlpha x) = 0 := by
  have hkne : E.k ≠ 0 := ne_of_gt E.k_pos
  have hz : E.u₀ - E.k * ((E.u₀ + E.r * x) / E.k) + E.r * x = 0 := by
    field_simp; ring
  change symσ E.q E.u₀ E.k E.r x (E.myopicAlpha x) = 0
  simp only [symσ, myopicAlpha, hz, zero_div]
  norm_num

/-- **The myopic feedback equilibrium.** Rule 1: `α_opt` proves the
compliance is the argmax of the Target's stage objective
`a ↦ U_T(x, a, σ(x, a))`, by the raw-coefficient lemma `symMyopic_isMaxOn`. -/
def symMyopic : E.toParams.MyopicFeedbackEquilibrium where
  α := E.myopicAlpha
  α_mem := fun _ hx => E.myopicAlpha_mem hx
  α_opt := by
    intro x hx
    change IsMaxOn (fun a => symU_T E.ℓ E.c E.n E.v x a (symσ E.q E.u₀ E.k E.r x a))
      Sanctions.I ((E.u₀ + E.r * x) / E.k)
    exact symMyopic_isMaxOn E.hq E.k_pos E.q_le_k E.hℓ
      (by nlinarith [E.hcn, mul_nonneg E.hn (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x)])
      (by nlinarith [E.hk, E.r_pos, hx.2])

/-- **The myopic regime imposes no sanctions at all**, at every feasible
state — against the forward-looking regime's full sanctions. -/
theorem myopicEquilibriumRule_eq_zero (x : ℝ) :
    E.toParams.myopicEquilibriumRule E.symMyopic x = 0 :=
  E.myopic_sigma_eq_zero x

/-! ## 11. The certificate's stage fields -/

/-- **Stage Target loss bound** at the derived (defiant) leader policy: the
loss rate `c − n·x` is at most `c_T = c − n·x̄` on the basin. -/
theorem h_stage_target_loss (V_T : E.valueClass.CarrierT)
    (V_S : E.valueClass.CarrierS) :
    ∀ x ∈ Set.Icc E.xb (1 : ℝ),
      LowerLossSlopeOn (fun s => E.toParams.U_T x (E.valueClass.α_on V_T V_S x) s)
        (Set.Icc (max x E.sbar) 1) (E.c - E.n * E.xb) := by
  intro x hx s₁ _ s₂ _ hle
  simp only [E.α_on_eq_zero V_T V_S, toParams_U_T, symU_T]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hle) E.hn)
    (sub_nonneg.mpr hx.1)]

/-- **Stage Sender slope** at the derived leader policy: the chord slope
`u₀ + r·x − (q/2)(s₁+s₂)` is at least `m_S = u₀ + r·x̄ − q·s̄` on
`[0, max(x, s̄)]` for every basin state. `q ≤ r` is what puts the minimum at
the basin bottom. -/
theorem h_stage_sender (V_T : E.valueClass.CarrierT)
    (V_S : E.valueClass.CarrierS) :
    ∀ x ∈ Set.Icc E.xb (1 : ℝ),
      LowerSlopeOn (fun s => E.toParams.U_S x (E.valueClass.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x E.sbar)) (E.u₀ + E.r * E.xb - E.q * E.sbar) := by
  intro x hx s₁ hs₁ s₂ hs₂ hle
  have hmax : E.r * E.xb - E.q * E.sbar ≤ E.r * x - E.q * max x E.sbar := by
    rcases max_cases x E.sbar with ⟨hm, hxs⟩ | ⟨hm, hxs⟩ <;> rw [hm]
    · nlinarith [mul_nonneg (sub_nonneg.mpr E.hqr) (sub_nonneg.mpr hxs),
        mul_nonneg E.r_pos.le (sub_nonneg.mpr E.hxbs)]
    · nlinarith [mul_nonneg E.r_pos.le (sub_nonneg.mpr hx.1)]
  have hsum : E.q / 2 * (s₁ + s₂) ≤ E.q * max x E.sbar := by
    nlinarith [hs₁.2, hs₂.2, E.hq]
  have hbr : 0 ≤ (E.u₀ + E.r * x - E.q / 2 * (s₁ + s₂))
      - (E.u₀ + E.r * E.xb - E.q * E.sbar) := by linarith
  simp only [E.α_on_eq_zero V_T V_S, toParams_U_S, symU_S]
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) hbr]

/-- **Carrier `V_T` gain on the basin**: restriction of the gain ball's
minimum upward slope from the whole state space to `[x̄, 1]`. -/
theorem hV_T_gain :
    ∀ V_T ∈ E.valueClass.carrier_T,
      LowerSlopeOnValueOn V_T (Set.Icc E.xb 1) E.gT := by
  intro V_T hV_T y₁ y₂ h1 h2 hle
  exact hV_T.2.2 y₁ y₂ ⟨by linarith [h1.1, E.hxb0], h1.2⟩
    ⟨by linarith [h2.1, E.hxb0], h2.2⟩ hle

/-- **Single crossing (trivial form)**: the Sender's dynamic objective is
strictly increasing in the sanction at every basin state, so both
single-crossing consequents hold unconditionally. -/
theorem hSC (V_T : E.valueClass.CarrierT) (V_S : E.valueClass.CarrierS) :
    Sanctions.MilgromShannon.SingleCrossingOn
      Sanctions.I (Set.Icc (max E.xb E.xb) 1)
      (fun s x => E.toParams.senderDynObjective V_S.val x
        (E.valueClass.α_on V_T V_S x) s) :=
  WitnessKit.singleCrossingOn_of_strictMonoOn
    fun t ht s₁ hs₁ s₂ hs₂ hlt => by
      simp only [E.α_on_eq_zero V_T V_S,
        AbstractGame.Params.senderDynObjective]
      refine E.senderObj_strictMonoOn V_S.property ?_
        (⟨le_refl 0, zero_le_one⟩ : (0 : ℝ) ∈ Sanctions.I) hs₁ hs₂ hlt
      rw [max_self] at ht
      exact ⟨le_trans E.hxb0 ht.1, ht.2⟩

/-! ## 12. THE CERTIFICATE -/

/-- **Every admissible member of the symbolic family carries a complete
`StandardComplianceLocalCoreCertificate`.**

All fourteen coefficients are free; every quantitative field is a closed form
in them:

* value class `D` — the slope-pinned gain-ball carriers at the Stokey–Lucas
  closed forms, with state-local Sender and Target argmax uniqueness;
* rows `(β_T, β_S, L_TS, L_ST) = (β_T, β_S, 0, 0)` — decoupled, because the
  derived Sender response is a corner and the derived leader policy a
  constant;
* basin `[x̄, 1]` with floor `s̄`;
* Sender stage margin `m_S = u₀ + r·x̄ − q·s̄` against the Sender value
  Lipschitz constant `K_S = (r + w)/(1 − β_S(1 − δ))`;
* the myopic comparator, whose realised sanction is identically zero.

The Target loss rate `c_T = c − n·x̄` against the Target value gain
`g_T = (n + v)/(1 − β_T(1 − δ))` (`target_loss_margin`) is no longer a
certificate field since round BJ1.4 (2026-10-07). -/
def certificate : E.toParams.StandardComplianceLocalCoreCertificate where
  D := E.valueClass
  h_inv := E.valueClass_IsInvariant
  β_T := E.βT
  β_S := E.βS
  L_TS := 0
  L_ST := 0
  hβ_T_nn := E.hβT0
  hβ_S_nn := E.hβS0
  hL_TS_nn := le_refl 0
  hL_ST_nn := le_refl 0
  hT_T_op := E.hT_T_op E.valueClass_IsInvariant
  hT_S_op := E.hT_S_op E.valueClass_IsInvariant
  hsuff_T := by simpa using E.hβT1
  hsuff_S := by simpa using E.hβS1
  xT := E.xb
  xS := E.xb
  sbar := E.sbar
  mS := E.u₀ + E.r * E.xb - E.q * E.sbar
  KS := E.KS
  hxT_mem := ⟨E.hxb0, E.xb_le_one⟩
  hxS_mem := ⟨E.hxb0, E.xb_le_one⟩
  hsbar_mem := ⟨E.hsbar0.le, E.hsbar1.le⟩
  d := E.toParams.δ
  hF_chord := E.toParams.affine_sender_chord_on rfl _ _
  hS_margin := E.sender_stage_margin
  hjoint_lt := by rw [max_self]; linarith [E.hxbs, E.hsbar1]
  hV_S_lip_carrier := fun _ hV_S => hV_S.2.1
  h_stage_sender_on := E.h_stage_sender
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn (E.hSC V_T V_S)
  M := E.symMyopic
  hMyoCeiling := fun x _ =>
    le_trans (le_of_eq (E.myopic_sigma_eq_zero x))
      (le_trans E.hsbar0.le (le_max_right _ _))

/-- **The Schur form of the same certificate.** -/
def certificateSchur : E.toParams.StandardComplianceLocalCoreCertificateSchur :=
  StandardComplianceLocalCoreCertificateSchur.ofRowSum E.toParams E.certificate

/-! ## 12a. The Milgrom–Shannon / general-`F` certificate

The two top headline rows — `standardCompliance_three_goals_local_MS` and its
minimum-drift general-transition companion — consume
`StandardComplianceLocalCoreCertificate_MS`, a *different* bundle from the
legacy one discharged above. Until this section that bundle had exactly one
inhabitant anywhere in the development: `eeCertCertificateMS`, at the numeric
economy `eeCertParams`. So both headlines were general theorems whose
hypothesis class was known non-empty only by a Rule-9 existence certificate.

This section removes that dependence. Three of the four extra fields follow
from material already proved above. The fourth, `hMyoCeiling`, is the one
genuinely new argument: the MS bundle pins the myopic comparator to
`myopicFeedbackEquilibrium_canonical`, whose policy is `Classical.choose` of
*some* stage argmax rather than the family's own `symMyopic`. So it is not
enough that the family's chosen myopic policy zeroes the sanction — **every**
stage argmax must, and that has to be proved.

One fact is needed that is strictly stronger than the corresponding
`SymbolicEconomy` field: a strictly interior basin bottom `0 < x̄` (the MS
bundle demands `max(x_T, x_S) ∈ (0,1)`, where the legacy bundle accepted the
closed interval). It is not added to the structure — it is taken as an
argument here and discharged in `symbolicEconomy_exists_strict` below, which
shows the existing Fourier–Motzkin chain already produces it. The assumption
surface of the final non-vacuity theorem is therefore unchanged.

**The strict placation margin `u₀ + r < k` is no longer needed (2026-10-06,
plan item BG3.7).** `certificateMS` used to take it as a second argument. It
was spent only on `hMyoCeiling`, and only to make the myopic compliance
`(u₀ + r·x)/k` interior at the top state `x = 1`. Below the top, `x < 1`
already gives `u₀ + r·x < u₀ + r ≤ k` from the structure's own non-strict
`hk`; at the top the ceiling asks only `σ ≤ max 1 x̄ = 1`, which is the
feasibility field `σ_mem`. So `canonical_myopic_ceiling` closes the field
with no margin, and the strict-margin lemmas below are kept as siblings for
the statements that really do need `σ = 0` at `x = 1`. -/

/-- `q < k`: the Sender's sanction-cost curvature is strictly below the
placation rate. Derived from `q ≤ r`, `u₀ > 0` and `u₀ + r ≤ k`. -/
theorem q_lt_k : E.q < E.k := by linarith [E.hqr, E.hk, E.hu₀]

/-- `x̄ < 1`: the basin bottom is strictly below the top state. -/
theorem xb_lt_one : E.xb < 1 := lt_of_le_of_lt E.hxbs E.hsbar1

/-- **The myopic compliance is interior below the top state, with no strict
placation margin.** Transition-free: `a₂ = (u₀ + r·x)/k` never reads the
transition. For `x < 1`, `r > 0` gives `u₀ + r·x < u₀ + r`, and the
structure's own non-strict `hk : u₀ + r ≤ k` finishes. The strict margin
`u₀ + r < k` that `myopicAlpha_lt_one_of_strict` uses is not needed. -/
theorem myopicAlpha_lt_one_of_lt_one {x : ℝ} (hx1 : x < 1) :
    E.myopicAlpha x < 1 := by
  rw [myopicAlpha, div_lt_one E.k_pos]
  linarith [mul_lt_of_lt_one_right E.r_pos hx1, E.hk]

/-- **The myopic compliance is interior at every feasible state, under the
strict placation margin `u₀ + r < k`.** Transition-free. This is the only
place the strict margin enters the myopic argument. -/
theorem myopicAlpha_lt_one_of_strict (hk_strict : E.u₀ + E.r < E.k)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : E.myopicAlpha x < 1 := by
  rw [myopicAlpha, div_lt_one E.k_pos]
  linarith [mul_le_of_le_one_right E.r_pos.le hx.2, hk_strict]

/-- **Every myopic stage argmax zeroes the sanction, wherever the myopic
compliance is interior.**

Not just the family's own comparator `symMyopic`, but *any* maximiser of the
Target's static objective `a ↦ U_T(x, a, σ(x, a))`. This is what the MS
certificate needs, because it pins the comparator to an opaque
`Classical.choose` selection. Transition-free: the myopic problem never reads
the transition.

The argument is the strict form of `symMyopic.α_opt`. Write `a₂ = (u₀+r·x)/k`
for the compliance that exactly zeroes the static Sender's sanction. Optimality
of a candidate `a` against `a₂` gives `σ(x,a)·(c − n·x) ≤ ℓ·(a₂ − a)`: the
sanction pain the candidate suffers is covered by the compliance cost it saves.
The reverse strict inequality holds whenever `a < a₂`, in both clipping
regimes — below the clip because `ℓ·q < k·(c − n·x)`, which is exactly
`q < k` together with `ℓ ≤ c − n·x`; at the clip because `a₂ < 1`, which is
the hypothesis `hα1`. So no maximiser lies below `a₂`, and above `a₂` the
static Sender's marginal benefit is non-positive, i.e. the sanction is zero.

**What `hα1` replaces (plan item BG3.7).** The original lemma,
`myopic_argmax_sigma_eq_zero`, took the strict placation margin `u₀ + r < k`
and spent it only here. `hα1` holds at every `x < 1` with no margin
(`myopicAlpha_lt_one_of_lt_one`). It can fail only at the top state `x = 1`
when `u₀ + r = k`, and there the conclusion can fail too: if also
`ℓ = c − n`, full compliance `a = 1` and zero compliance `a = 0` tie in the
Target's static objective, and `a = 0` draws the full sanction. -/
theorem myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hα1 : E.myopicAlpha x < 1)
    {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun a' => E.toParams.U_T x a' (E.toParams.σ x a'))
              Sanctions.I a) :
    E.toParams.σ x a = 0 := by
  have hk := E.k_pos
  have hq := E.hq
  -- The Target's per-unit sanction pain is at least its compliance cost.
  have hψ : E.ℓ ≤ E.c - E.n * x := by
    nlinarith [E.hcn, mul_nonneg E.hn (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x)]
  have hψ0 : (0 : ℝ) < E.c - E.n * x := lt_of_lt_of_le E.hℓ hψ
  have hka : E.k * E.myopicAlpha x = E.u₀ + E.r * x := by
    simp only [myopicAlpha]; field_simp
  rcases le_or_gt (E.u₀ - E.k * a + E.r * x) 0 with hsign | hsign
  · -- The static Sender's marginal benefit is already non-positive: clipped
    -- at the floor, so the realised sanction is zero.
    have ht : (E.u₀ - E.k * a + E.r * x) / E.q ≤ 0 := by
      rw [div_le_iff₀ hq]; linarith
    change symσ E.q E.u₀ E.k E.r x a = 0
    simp only [symσ, min_eq_right (le_trans ht zero_le_one), max_eq_left ht]
  · exfalso
    -- The candidate sits strictly below the sanction-zeroing compliance.
    have ha_lt : a < E.myopicAlpha x := by
      have hmul : E.k * a < E.k * E.myopicAlpha x := by rw [hka]; linarith
      exact lt_of_mul_lt_mul_left hmul E.k_pos.le
    have hgap : (0 : ℝ) < E.myopicAlpha x - a := by linarith
    -- Optimality of `a` against the sanction-zeroing compliance.
    have hJ := isMaxOn_iff.mp hmax (E.myopicAlpha x) (E.myopicAlpha_mem hx)
    rw [E.myopic_sigma_eq_zero x] at hJ
    simp only [toParams_U_T, symU_T, toParams_σ] at hJ
    have hbound : symσ E.q E.u₀ E.k E.r x a * (E.c - E.n * x)
        ≤ E.ℓ * (E.myopicAlpha x - a) := by nlinarith [hJ]
    -- The strict reverse inequality, in both clipping regimes.
    have hstrict : E.ℓ * (E.myopicAlpha x - a)
        < symσ E.q E.u₀ E.k E.r x a * (E.c - E.n * x) := by
      have hnum : E.u₀ - E.k * a + E.r * x = E.k * (E.myopicAlpha x - a) := by
        rw [mul_sub, hka]; ring
      have hpos : (0 : ℝ) < (E.u₀ - E.k * a + E.r * x) / E.q := div_pos hsign hq
      rcases le_or_gt ((E.u₀ - E.k * a + E.r * x) / E.q) 1 with ht1 | ht1
      · -- Below the clip: the sanction falls at rate `k/q > 1` in compliance.
        have hσ : symσ E.q E.u₀ E.k E.r x a
            = (E.u₀ - E.k * a + E.r * x) / E.q := by
          simp only [symσ, min_eq_right ht1, max_eq_right hpos.le]
        have hlq : E.ℓ * E.q < E.k * (E.c - E.n * x) := by
          nlinarith [E.q_lt_k, E.hℓ, hψ, hk, hq]
        rw [hσ, hnum, div_mul_eq_mul_div, lt_div_iff₀ hq]
        nlinarith [mul_lt_mul_of_pos_right hlq hgap]
      · -- At the clip: full sanctions, and `a₂ < 1` makes the loss strict.
        have hσ : symσ E.q E.u₀ E.k E.r x a = 1 := by
          simp only [symσ, min_eq_left ht1.le, max_eq_right zero_le_one]
        rw [hσ, one_mul]
        nlinarith [E.hℓ, ha.1, hα1]
    linarith

/-- **Every myopic stage argmax zeroes the sanction**, at every feasible state,
under the strict placation margin `u₀ + r < k`. Transition-free. The original
statement, kept as a one-line corollary of
`myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one`: the margin is used only to
make the myopic compliance interior (`myopicAlpha_lt_one_of_strict`). -/
theorem myopic_argmax_sigma_eq_zero (hk_strict : E.u₀ + E.r < E.k)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun a' => E.toParams.U_T x a' (E.toParams.σ x a'))
              Sanctions.I a) :
    E.toParams.σ x a = 0 :=
  E.myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one hx
    (E.myopicAlpha_lt_one_of_strict hk_strict hx) ha hmax

/-- **The canonical myopic comparator realises no sanction**, at every feasible
state. Immediate from `myopic_argmax_sigma_eq_zero`, since the canonical
comparator's policy is by construction a stage argmax. -/
theorem canonical_myopic_sigma_eq_zero (hk_strict : E.u₀ + E.r < E.k)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    E.toParams.σ x (E.toParams.myopicFeedbackEquilibrium_canonical.α x) = 0 :=
  E.myopic_argmax_sigma_eq_zero hk_strict hx
    (E.toParams.myopicFeedbackEquilibrium_canonical.α_mem x hx)
    (E.toParams.myopicFeedbackEquilibrium_canonical.α_opt x hx)

/-- **The canonical myopic comparator realises no sanction below the top
state, with no strict placation margin.** Transition-free. This is
`canonical_myopic_sigma_eq_zero` with the hypothesis `u₀ + r < k` dropped, at
the price of `x < 1`: below the top the myopic compliance is interior from the
structure's non-strict `hk` alone (`myopicAlpha_lt_one_of_lt_one`). -/
theorem canonical_myopic_sigma_eq_zero_of_lt_one {x : ℝ} (hx : x ∈ Sanctions.S)
    (hx1 : x < 1) :
    E.toParams.σ x (E.toParams.myopicFeedbackEquilibrium_canonical.α x) = 0 :=
  E.myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one hx
    (E.myopicAlpha_lt_one_of_lt_one hx1)
    (E.toParams.myopicFeedbackEquilibrium_canonical.α_mem x hx)
    (E.toParams.myopicFeedbackEquilibrium_canonical.α_opt x hx)

/-- **The canonical myopic ceiling, with no strict placation margin.**
Transition-free. On the basin `[x̄, 1]` the canonical myopic comparator's
sanction is at most `max x x̄`, which is what the MS certificate's
`hMyoCeiling` field asks. Below the top state the sanction is zero
(`canonical_myopic_sigma_eq_zero_of_lt_one`); at the top state `x = 1` the
bound is `max 1 x̄ = 1`, and every static sanction is at most `1` by the
feasibility field `σ_mem`. So the strict margin `u₀ + r < k`, which
`certificateMS` used to take for this field, is not needed. -/
theorem canonical_myopic_ceiling {x : ℝ} (hx : x ∈ Set.Icc E.xb 1) :
    E.toParams.σ x (E.toParams.myopicFeedbackEquilibrium_canonical.α x)
      ≤ max x E.xb := by
  rcases hx.2.lt_or_eq with hx1 | rfl
  · rw [E.canonical_myopic_sigma_eq_zero_of_lt_one ⟨le_trans E.hxb0 hx.1, hx.2⟩ hx1]
    exact le_trans E.hxb0 (le_max_right x E.xb)
  · exact le_trans (E.toParams.σ_mem 1 _).2 (le_max_left 1 E.xb)

/-- **Target stage loss bound on an arbitrary sanction domain.** Same content
as `h_stage_target_loss`; the MS certificate's combined chord is stated over a
different sanction interval (floor `max(x_T, x_S)` rather than `s̄`), and the
bound never used the domain. -/
theorem h_stage_target_loss_any (V_T : E.valueClass.CarrierT)
    (V_S : E.valueClass.CarrierS) (D : Set ℝ) :
    ∀ x ∈ Set.Icc E.xb (1 : ℝ),
      LowerLossSlopeOn (fun s => E.toParams.U_T x (E.valueClass.α_on V_T V_S x) s)
        D (E.c - E.n * E.xb) := by
  intro x hx s₁ _ s₂ _ hle
  simp only [E.α_on_eq_zero V_T V_S, toParams_U_T, symU_T]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hle) E.hn)
    (sub_nonneg.mpr hx.1)]

/-- **Strict stage-Sender monotonicity on the MS sanction range.** The
positive stage chord slope `m_S = u₀ + r·x̄ − q·s̄` upgrades the legacy
lower-slope bound to strict monotonicity; the MS range `[0, max(x, x̄)]` sits
inside the legacy range `[0, max(x, s̄)]` because `x̄ ≤ s̄`. -/
theorem h_stage_sender_strictMonoOn (V_T : E.valueClass.CarrierT)
    (V_S : E.valueClass.CarrierS) :
    ∀ x ∈ Set.Icc E.xb (1 : ℝ),
      StrictMonoOn (fun s => E.toParams.U_S x (E.valueClass.α_on V_T V_S x) s)
        (Set.Icc (0 : ℝ) (max x (max E.xb E.xb))) := by
  intro x hx s₁ hs₁ s₂ hs₂ hlt
  have hsub : max x (max E.xb E.xb) ≤ max x E.sbar := by
    rw [max_self]; exact max_le_max le_rfl E.hxbs
  have h := E.h_stage_sender V_T V_S x hx
    s₁ ⟨hs₁.1, le_trans hs₁.2 hsub⟩ s₂ ⟨hs₂.1, le_trans hs₂.2 hsub⟩ hlt.le
  have hpos : (0 : ℝ) < (E.u₀ + E.r * E.xb - E.q * E.sbar) * (s₂ - s₁) :=
    mul_pos E.mS_pos (by linarith)
  linarith

/-- **Every admissible member with a strictly interior basin bottom carries a
complete MS / general-`F` certificate.**

This is the bundle the two top headline theorems consume. Every field is a
closed form in the fourteen free coefficients; no numeral appears.
Affine-restricted: `SymbolicEconomy` fixes `F := affineF δ` (the general-`F`
sibling is `SymbolicEconomyF.certificateMS`).

**Dropped hypothesis (plan item BG3.7, 2026-10-06).** The constructor used to
take the strict placation margin `hk_strict : u₀ + r < k` as well. It fed only
`hMyoCeiling`, which `canonical_myopic_ceiling` now closes with no margin:
the myopic sanction is zero below the top state and at most `1` at the top. So
every member whose basin bottom is strictly positive is certified, including
members that sit exactly on the placation boundary `u₀ + r = k`. -/
def certificateMS (hxb_pos : 0 < E.xb) :
    E.toParams.StandardComplianceLocalCoreCertificate_MS where
  D := E.valueClass
  h_inv := E.valueClass_IsInvariant
  β_T := E.βT
  β_S := E.βS
  L_TS := 0
  L_ST := 0
  hβ_T_nn := E.hβT0
  hβ_S_nn := E.hβS0
  hL_TS_nn := le_refl 0
  hL_ST_nn := le_refl 0
  hT_T_op := E.hT_T_op E.valueClass_IsInvariant
  hT_S_op := E.hT_S_op E.valueClass_IsInvariant
  hsuff_T := by simpa using E.hβT1
  hsuff_S := by simpa using E.hβS1
  xT := E.xb
  xS := E.xb
  hxT_mem := ⟨E.hxb0, E.xb_le_one⟩
  hxS_mem := ⟨E.hxb0, E.xb_le_one⟩
  hpivot_mem := by rw [max_self]; exact ⟨hxb_pos, E.xb_lt_one⟩
  h_stage_sender_strictMono := E.h_stage_sender_strictMonoOn
  hIDO_on := fun V_T V_S =>
    Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn (E.hSC V_T V_S)
  h_target_combined :=
    E.toParams.Target_combined_chord_of_decomposition_lowerChord
      (D := E.valueClass) ⟨E.hxb0, E.xb_le_one⟩
      (dlo := E.δ)
      (E.toParams.affine_transitionChordPack (δ := E.δ) rfl).1
      E.gT_pos.le E.target_loss_margin
      (fun V_T V_S x hx =>
        E.h_stage_target_loss_any V_T V_S
          (Set.Icc (max x (max E.xb E.xb)) 1) x hx)
      E.hV_T_gain
  hV_S_mono_carrier := fun _ hV_S =>
    monotone_of_mem_valLipGainBall E.KS_pos.le hV_S
  hMyoCeiling := fun x hx => by
    rw [max_self] at hx ⊢
    exact E.canonical_myopic_ceiling hx

/-! ## 13. Headline consequences, symbolically -/

/-- **Unconditional three-goals dominance at every admissible member.** A
forward-looking feedback Stackelberg equilibrium exists in the certified
carriers, and on the whole basin its realised sanction dominates the myopic
regime's. -/
theorem three_goals_dominance :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT ∧ Eq.V_S ∈ E.carrierS
      ∧ (∀ x ∈ Set.Icc (max E.xb E.xb) 1,
           E.toParams.σ x (E.symMyopic.α x)
             ≤ E.toParams.dynamicTopRealizedRule Eq.V_S Eq.α x) := by
  obtain ⟨Eq, hVT, hVS, _hG1, hG2, _hG3⟩ :=
    E.certificate.three_goals_local_uniform_starts (p := E.toParams) rfl
  exact ⟨Eq, hVT, hVS, hG2⟩

/-- **Maximal regime separation at every admissible member.** There is a
forward-looking equilibrium in the carriers whose realised sanction is the
top corner at every feasible state, while the independently optimal myopic
regime realises no sanction at all. Affine-restricted; the general-family form,
against the same myopic comparator and with no side condition, is
`SymbolicEconomyF.regime_separation_symMyopic` (plan item BJ4.6). -/
theorem regime_separation :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT ∧ Eq.V_S ∈ E.carrierS
      ∧ ∀ x ∈ Sanctions.S,
          E.toParams.myopicEquilibriumRule E.symMyopic x = 0
          ∧ E.toParams.dynamicEquilibriumRule Eq x = 1 := by
  obtain ⟨Eq, hVT, hVS, _hG1, _hG2, _hG3⟩ :=
    E.certificate.three_goals_local_uniform_starts (p := E.toParams) rfl
  refine ⟨Eq, hVT, hVS, fun x hx => ⟨E.myopicEquilibriumRule_eq_zero x, ?_⟩⟩
  exact E.σ_dyn_top_eq_one hVS hx (Eq.α_mem x hx)

/-- **Directional sign witness (Rule 16a).** The comparative static points the
economically intended way: at every feasible state the forward-looking
regime's realised sanction *strictly exceeds* the myopic regime's, at every
admissible member of the family. -/
theorem regime_separation_strict :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.S,
        E.toParams.myopicEquilibriumRule E.symMyopic x
          < E.toParams.dynamicEquilibriumRule Eq x := by
  obtain ⟨Eq, _hVT, _hVS, h⟩ := E.regime_separation
  refine ⟨Eq, fun x hx => ?_⟩
  rw [(h x hx).1, (h x hx).2]
  exact zero_lt_one

/-- **Within-carrier uniqueness at every admissible member.** -/
theorem unique_in_carrier
    (Eq Eq' : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVT : Eq.V_T ∈ E.carrierT) (hVS : Eq.V_S ∈ E.carrierS)
    (hVT' : Eq'.V_T ∈ E.carrierT) (hVS' : Eq'.V_S ∈ E.carrierS)
    (hαE : Eq.α = E.valueClass.α_on ⟨Eq.V_T, hVT⟩ ⟨Eq.V_S, hVS⟩)
    (hαE' : Eq'.α = E.valueClass.α_on ⟨Eq'.V_T, hVT'⟩ ⟨Eq'.V_S, hVS'⟩) :
    Eq.V_T = Eq'.V_T ∧ Eq.V_S = Eq'.V_S ∧ Eq.α = Eq'.α :=
  E.certificateSchur.unique_in_carrier (p := E.toParams)
    Eq Eq' hVT hVS hVT' hVS' hαE hαE'

/-- **Within-carrier uniqueness at every admissible member, with no selector
hypothesis (round BH1.1, 2026-10-06).** Sibling of `unique_in_carrier` without
`hαE`, `hαE'`: any two top-selector feedback Stackelberg equilibria whose values
lie in the member's carriers share both value functions, and their policies
agree at every feasible state. Every quantitative input comes from
`certificateSchur`. The family runs the affine law; the theorem it instantiates
is general in `F`. -/
theorem unique_in_carrier_of_mem
    (Eq Eq' : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVT : Eq.V_T ∈ E.carrierT) (hVS : Eq.V_S ∈ E.carrierS)
    (hVT' : Eq'.V_T ∈ E.carrierT) (hVS' : Eq'.V_S ∈ E.carrierS) :
    Eq.V_T = Eq'.V_T ∧ Eq.V_S = Eq'.V_S ∧ Set.EqOn Eq.α Eq'.α Sanctions.S :=
  E.certificateSchur.unique_in_carrier_of_mem (p := E.toParams)
    Eq Eq' hVT hVS hVT' hVS'

end SymbolicEconomy

/-! ## 13a. Equilibrium comparative statics in Sender patience, symbolically

The four `eeCertB_*` comparative-statics results were stated on a numeric
economy over the hand-computed patience window `β_S ∈ [6/13, 4/7)`. Every one of
them is an identity in the closed forms above, so none of them needs either the
window or the numerals. The lifted versions below compare **two members of the
family that agree on the primitives each result actually depends on**, and let
the Sender discount factor differ freely — which is what a comparative static
in Sender patience means when no parameter is a chosen magnitude. -/

namespace SymbolicEconomy

variable (E : SymbolicEconomy)

/-- The equilibrium Sender value as a scalar function of the state:
`v_S(y) = A_S + K_S·y`, the coefficients being the closed forms of §7. -/
def vS (y : ℝ) : ℝ := E.VSint + E.KS * y

/-- The corner-pinned next state `F(y, 1) = (1 − δ)·y + δ`: where the state goes
in one period when the forward-looking Sender plays its derived corner. -/
def nextS (y : ℝ) : ℝ := (1 - E.δ) * y + E.δ

@[simp] theorem VSstar_eq_vS (y : ↥(Sanctions.S : Set ℝ)) :
    E.VSstar y = E.vS y.val := rfl

/-- **Scalar Bellman equation for the Sender's equilibrium value.** The same
identity as `VSstar_bellman_fix`, in a form that can be differenced across two
economies: current corner stage payoff plus discounted continuation at the
corner-pinned next state. -/
theorem vS_bellman (y : ℝ) :
    E.vS y = (E.stageS0 + E.stageSlopeS * y) + E.βS * E.vS (E.nextS y) := by
  simp only [vS, nextS]
  linear_combination (-y) * E.KS_margin - E.VSint_fix

/-- **Lock-in value**: the Sender's equilibrium value at the absorbing top
state `x = 1`, where the state is maximal, the Target fully defiant and the
sanction at its corner. -/
def lockinValue : ℝ := E.vS 1

/-- The corner stage payoff `U_S(1, 0, 1) = (u₀ − q/2) + (r + w)` — what the
Sender collects each period once locked in. -/
def cornerStagePayoff : ℝ := E.stageS0 + E.stageSlopeS

/-- **The two Sender margins force `q < u₀`.** The implacability margin bounds
the continuation gain `β_S·δ·(r+w)` from below by the worst stage disincentive
and the stage margin bounds it from above by the basin chord slope; chaining
them and cancelling the common positive factor `1 − β_S(1−δ)` gives
`q + k − u₀ < u₀ + r·x̄ − q·s̄`. With `u₀ + r ≤ k` this rearranges to
`u₀ > q(1 + s̄) + r(1 − x̄)`, which is the Fourier–Motzkin threshold that
`symbolicEconomy_exists_strict` selects `u₀` above — and it is strictly more
than `q`. -/
theorem q_lt_u₀ : E.q < E.u₀ := by
  have hchain : (E.q + E.k - E.u₀) * (1 - E.βS * (1 - E.δ))
      < (E.u₀ + E.r * E.xb - E.q * E.sbar) * (1 - E.βS * (1 - E.δ)) :=
    lt_trans E.hCorner E.hSMargin
  have h1 : E.q + E.k - E.u₀ < E.u₀ + E.r * E.xb - E.q * E.sbar :=
    lt_of_mul_lt_mul_right hchain E.ΛS_pos.le
  linarith [E.hk, mul_pos E.hq E.hsbar0,
    mul_nonneg E.r_pos.le (sub_nonneg.mpr E.xb_le_one)]

/-- **The corner stage payoff is strictly positive at every admissible member.**

This is *not* a free-standing sign assumption — it is forced by the same two
margins that pin the corner. `q < u₀` gives `u₀ − q/2 > q/2 > 0`, and the
stage state-slope `r + w` is positive because the certificate's Sender chord
slope is. Economically: an economy in which the forward-looking Sender is
implacable enough to corner cannot simultaneously be one in which cornering
loses it money at the top state.

Affine-restricted. The general family proves the same sign from the
implacability margin alone (`SymbolicEconomyF.cornerStagePayoff_pos`, plan
item BJ4.6), since it no longer carries the Sender stage margin. -/
theorem cornerStagePayoff_pos : 0 < E.cornerStagePayoff := by
  simp only [cornerStagePayoff, stageS0, stageSlopeS]
  linarith [E.q_lt_u₀, E.stageSlopeS_pos, E.hq]

/-- **Closed form of the lock-in value**: the perpetuity value of the corner
stage payoff. This is the symbolic content of the numeric witness's
`(11/2)/(1 − β)`: the numerator is not an independent constant but the corner
stage payoff evaluated at that economy. -/
theorem lockinValue_eq :
    E.lockinValue = E.cornerStagePayoff / (1 - E.βS) := by
  have hne : (1 : ℝ) - E.βS ≠ 0 := by linarith [E.hβS1]
  have h := E.vS_bellman 1
  have hfix : E.nextS 1 = 1 := by simp only [nextS]; ring
  rw [hfix] at h
  rw [eq_div_iff hne]
  change E.vS 1 * (1 - E.βS) = E.stageS0 + E.stageSlopeS
  linear_combination h

end SymbolicEconomy

/-- **Equilibrium feedback decomposition, symbolically.** For two family
members that agree on the Sender's corner stage payoff and on the adjustment
rate — so that only Sender patience differs — the change in the Sender's
equilibrium value at any state splits exactly into a **direct patience effect**
(the more patient Sender applies the higher weight `β₂ − β₁` to the *same*
continuation) and a **continuation feedback effect** (the old weight `β₁`
applied to the change in the continuation value itself).

This is the number-free form of `eeCertB_equilibrium_feedback_decomposition`;
the numeric version's `(y + 1)/2` is `nextS` at `δ = 1/2`.

Affine-restricted. The general-family form, with "share `δ`" replaced by
"share `F`" and stated for any carrier equilibria, is
`SymbolicEconomyF.equilibrium_feedback_decomposition` (plan item BJ4.6). -/
theorem symbolic_equilibrium_feedback_decomposition
    (E₁ E₂ : SymbolicEconomy)
    (hδ : E₁.δ = E₂.δ)
    (h0 : E₁.stageS0 = E₂.stageS0) (hsl : E₁.stageSlopeS = E₂.stageSlopeS)
    (y : ℝ) :
    E₂.vS y - E₁.vS y
      = (E₂.βS - E₁.βS) * E₂.vS (E₂.nextS y)
        + E₁.βS * (E₂.vS (E₂.nextS y) - E₁.vS (E₁.nextS y)) := by
  have hnext : E₁.nextS y = E₂.nextS y := by
    simp only [SymbolicEconomy.nextS, hδ]
  have h₁ := E₁.vS_bellman y
  have h₂ := E₂.vS_bellman y
  rw [hnext] at h₁
  rw [h0, hsl] at h₁
  rw [hnext]
  linarith [h₁, h₂]

/-- **Lock-in amplification, symbolically.** An unconditional identity: the
gain in lock-in value from extra Sender patience, scaled by the *old* horizon
factor `1 − β₁`, equals the patience increment times the *new* lock-in value.
The mechanism is the geometric horizon, and it needs no sign assumption
whatsoever — the number-free form of `eeCertB_lockin_amplification`.
Affine-restricted; the general-family form is
`SymbolicEconomyF.lockin_amplification` (plan item BJ4.6). -/
theorem symbolic_lockin_amplification
    (E₁ E₂ : SymbolicEconomy)
    (hC : E₁.cornerStagePayoff = E₂.cornerStagePayoff) :
    (1 - E₁.βS) * (E₂.lockinValue - E₁.lockinValue)
      = (E₂.βS - E₁.βS) * E₂.lockinValue := by
  have hne₁ : (1 : ℝ) - E₁.βS ≠ 0 := by linarith [E₁.hβS1]
  have hne₂ : (1 : ℝ) - E₂.βS ≠ 0 := by linarith [E₂.hβS1]
  rw [E₁.lockinValue_eq, E₂.lockinValue_eq, hC]
  field_simp
  ring

/-- **Lock-in monotonicity in Sender patience is exactly a sign condition.**
Stated as an `iff`, so it carries no assumption at all: a strictly more patient
Sender is strictly better off at the lock-in corner **if and only if** the
corner stage payoff is positive.

The `iff` isolates what the ranking actually rests on. A Sender locked into
sanctioning at a net stage loss would be made strictly *worse* off by patience,
because patience lengthens the horizon over which it bears that loss; the
lock-in trap and the lock-in prize are one geometric mechanism with opposite
signs. On *this* family the trap branch is unreachable —
`cornerStagePayoff_pos` shows the corner payoff is forced positive by the two
Sender margins — so the unconditional ranking `symbolic_lockin_strict` follows.
The equivalence is kept because it is the sharper statement: it says the sign
of the corner payoff is the whole content of the comparative static, which the
unconditional corollary hides. Affine-restricted; the general-family form is
`SymbolicEconomyF.lockin_strict_iff` (plan item BJ4.6). -/
theorem symbolic_lockin_strict_iff
    (E₁ E₂ : SymbolicEconomy)
    (hC : E₁.cornerStagePayoff = E₂.cornerStagePayoff)
    (hβ : E₁.βS < E₂.βS) :
    E₁.lockinValue < E₂.lockinValue ↔ 0 < E₁.cornerStagePayoff := by
  have hne₁ : (0 : ℝ) < 1 - E₁.βS := by linarith [E₁.hβS1]
  have hne₂ : (0 : ℝ) < 1 - E₂.βS := by linarith [E₂.hβS1]
  rw [E₁.lockinValue_eq, E₂.lockinValue_eq, hC, div_lt_div_iff₀ hne₁ hne₂]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **Patience strictly raises the lock-in value, unconditionally on the
family.** The number-free counterpart of `eeCertB_equilibrium_lockin_strict`:
the numeric version's strict ranking was not an artefact of its calibration,
because `cornerStagePayoff_pos` discharges the sign condition at every
admissible member. Affine-restricted; the general-family form is
`SymbolicEconomyF.lockin_strict` (plan item BJ4.6). -/
theorem symbolic_lockin_strict
    (E₁ E₂ : SymbolicEconomy)
    (hC : E₁.cornerStagePayoff = E₂.cornerStagePayoff)
    (hβ : E₁.βS < E₂.βS) :
    E₁.lockinValue < E₂.lockinValue :=
  (symbolic_lockin_strict_iff E₁ E₂ hC hβ).mpr E₁.cornerStagePayoff_pos

/-- **The Target's equilibrium value is invariant to Sender patience.**

Note what is *absent* from the hypothesis list: nothing relates `E₁.βS` to
`E₂.βS`. Two family members may have arbitrarily different Sender discount
factors; provided they share the adjustment rate, the Target discount factor
and the Target's corner stage payoff, their Target equilibrium value functions
are literally equal. The reason is structural rather than numerical: on the
carrier the Sender's derived response is the corner `σ_dyn ≡ 1` whatever its
continuation value, so the Target's Bellman operator never sees `β_S`.

Number-free form of `eeCertB_VT_star_βS_invariant`. Affine-restricted; the
general-family form, sharing `F` in place of `δ`, is
`SymbolicEconomyF.VT_βS_invariant` (plan item BJ4.6). -/
theorem symbolic_VTstar_βS_invariant
    (E₁ E₂ : SymbolicEconomy)
    (hδ : E₁.δ = E₂.δ) (hβT : E₁.βT = E₂.βT)
    (hT0 : E₁.stageT0 = E₂.stageT0) (hTsl : E₁.stageSlopeT = E₂.stageSlopeT) :
    E₁.VTstar = E₂.VTstar := by
  have hg : E₁.gT = E₂.gT := by
    simp only [SymbolicEconomy.gT, StokeyLucas.bellmanLipConstant, hδ, hβT, hTsl]
  have hi : E₁.VTint = E₂.VTint := by
    simp only [SymbolicEconomy.VTint, hδ, hβT, hT0, hg]
  simp only [SymbolicEconomy.VTstar, hi, hg]

/-! ## 14. The admissible region is non-empty — by inequality chaining only

Backwards Fourier–Motzkin: each coefficient is produced by `exists_between` or
`exists_gt` applied to bounds built from the coefficients already chosen. No
numeral other than the structural `0` and `1` appears, and no point is
named. -/

/-- **The admissible region is non-empty.** Every coefficient is obtained from
`exists_between` / `exists_gt` against a threshold assembled from the
previously chosen coefficients; nothing is a chosen magnitude.

The order of elimination — the reverse of the dependency order — is:
the discount factors and the adjustment rate; the basin floor and bottom;
the Sender's curvature `q` and rally slope `r > q`; the Sender's baseline
`u₀` above the Fourier–Motzkin threshold `q(1 + s̄) + r(1 − x̄)` that the two
Sender margins jointly force; the placation rate `k` in the window that
threshold opens; the Target's rally slope `n`, compliance cost `ℓ` and
sanction pain `c > ℓ + n`; and finally the two state valuations `w`, `v`,
each pinned into the window its own margin opens.

The two extra conjuncts record that the chain already delivers a **strictly**
interior basin bottom and a **strict** placation margin — `xb` is produced by
`exists_between` strictly above `0`, and `k` strictly above `u₀ + r` — which
the corresponding `SymbolicEconomy` fields, stated with `≤`, do not by
themselves supply. Since plan item BG3.7 `certificateMS` needs only the first;
the second is kept for the strict-margin siblings
(`myopic_argmax_sigma_eq_zero`, `canonical_myopic_sigma_eq_zero`). -/
theorem symbolicEconomy_exists_strict :
    ∃ E : SymbolicEconomy, 0 < E.xb ∧ E.u₀ + E.r < E.k := by
  obtain ⟨δ, hδ0, hδ1⟩ := exists_between (zero_lt_one (α := ℝ))
  obtain ⟨βS, hβS0, hβS1⟩ := exists_between (zero_lt_one (α := ℝ))
  obtain ⟨βT, hβT0, hβT1⟩ := exists_between (zero_lt_one (α := ℝ))
  obtain ⟨sbar, hsbar0, hsbar1⟩ := exists_between (zero_lt_one (α := ℝ))
  obtain ⟨xb, hxb0, hxbs⟩ := exists_between hsbar0
  obtain ⟨q, hq⟩ := exists_gt (0 : ℝ)
  obtain ⟨r, hqr⟩ := exists_gt q
  obtain ⟨u₀, hu₀gt⟩ := exists_gt (q * (1 + sbar) + r * (1 - xb))
  obtain ⟨n, hn0⟩ := exists_gt (0 : ℝ)
  obtain ⟨ℓ, hℓ0⟩ := exists_gt (0 : ℝ)
  obtain ⟨c, hc⟩ := exists_gt (ℓ + n)
  -- Positivity bookkeeping.
  have hr0 : (0 : ℝ) < r := lt_trans hq hqr
  have hxb1 : xb < 1 := lt_trans hxbs hsbar1
  have hthr : (0 : ℝ) < q * (1 + sbar) + r * (1 - xb) := by
    nlinarith [hq, hr0, hsbar0, hxb1]
  have hu₀ : (0 : ℝ) < u₀ := lt_trans hthr hu₀gt
  -- The placation window opened by the Fourier–Motzkin threshold.
  have hkwin : u₀ + r < 2 * u₀ + r * xb - q * sbar - q := by nlinarith [hu₀gt]
  obtain ⟨k, hk1, hk2⟩ := exists_between hkwin
  -- The Sender state valuation: its discounted continuation gain is pinned
  -- strictly between the two Sender margins, and `w` is then read off.
  have hΛS : (0 : ℝ) < 1 - βS * (1 - δ) := by nlinarith [hβS0, hβS1, hδ0, hδ1]
  have hβSδ : (0 : ℝ) < βS * δ := mul_pos hβS0 hδ0
  have hβSδne : βS * δ ≠ 0 := ne_of_gt hβSδ
  have hLR : (q + k - u₀) * (1 - βS * (1 - δ))
      < (u₀ + r * xb - q * sbar) * (1 - βS * (1 - δ)) :=
    mul_lt_mul_of_pos_right (by linarith [hk2]) hΛS
  obtain ⟨z, hz1, hz2⟩ := exists_between hLR
  -- The Target state valuation: its discounted continuation gain is pinned
  -- strictly above the loss-offset margin, and `v` is then read off.
  have hΛT : (0 : ℝ) < 1 - βT * (1 - δ) := by nlinarith [hβT0, hβT1, hδ0, hδ1]
  have hβTδ : (0 : ℝ) < βT * δ := mul_pos hβT0 hδ0
  have hβTδne : βT * δ ≠ 0 := ne_of_gt hβTδ
  obtain ⟨y, hy⟩ := exists_gt ((c - n * xb) * (1 - βT * (1 - δ)))
  refine ⟨{ δ := δ, βS := βS, βT := βT, q := q, u₀ := u₀, k := k, r := r,
            w := z / (βS * δ) - r, ℓ := ℓ, c := c, n := n,
            v := y / (βT * δ) - n, xb := xb, sbar := sbar
            hδ0 := hδ0, hδ1 := hδ1
            hβS0 := hβS0.le, hβS1 := hβS1
            hβT0 := hβT0.le, hβT1 := hβT1
            hq := hq, hqr := hqr.le, hu₀ := hu₀, hk := hk1.le
            hn := hn0.le, hℓ := hℓ0, hcn := by linarith
            hxb0 := hxb0.le, hxbs := hxbs.le
            hsbar0 := hsbar0, hsbar1 := hsbar1
            hCorner := ?_, hSMargin := ?_, hTMargin := ?_ }, hxb0, hk1⟩
  · have hw : βS * δ * (r + (z / (βS * δ) - r)) = z := by field_simp; ring
    rw [hw]; exact hz1
  · have hw : βS * δ * (r + (z / (βS * δ) - r)) = z := by field_simp; ring
    rw [hw]; exact hz2
  · have hv : βT * δ * (n + (y / (βT * δ) - n)) = y := by field_simp; ring
    rw [hv]; exact hy.le

/-- **The admissible region is non-empty.** One-line corollary of
`symbolicEconomy_exists_strict`, retaining the original name. -/
theorem symbolicEconomy_nonempty : Nonempty SymbolicEconomy :=
  let ⟨E, _, _⟩ := symbolicEconomy_exists_strict; ⟨E⟩

/-- **The MS / general-`F` certificate class is inhabited, with no parameter
vector named.** This is the theorem that takes the two top headline rows —
`standardCompliance_three_goals_local_MS` and
`standardCompliance_three_goals_local_MS_generalF_min_drift_shock` — off their
dependence on the numeric witness `eeCertCertificateMS` for non-vacuity.

Note the statement has no hypotheses: the strict basin bottom that
`certificateMS` consumes is discharged inside, from the same inequality chain
that proves the family non-empty. -/
theorem symbolic_MS_certified_family_nonvacuous :
    ∃ E : SymbolicEconomy,
      Nonempty E.toParams.StandardComplianceLocalCoreCertificate_MS := by
  obtain ⟨E, hxb, _⟩ := symbolicEconomy_exists_strict
  exact ⟨E, ⟨E.certificateMS hxb⟩⟩

/-- **The MS headline is non-vacuously instantiated, symbolically.** Feeding
the symbolic MS certificate to the headline theorem produces a forward-looking
feedback Stackelberg equilibrium living in the closed-form carriers, at an
economy no coefficient of which is a chosen magnitude. -/
theorem symbolic_MS_headline_equilibrium :
    ∃ E : SymbolicEconomy,
      ∃ C : E.toParams.StandardComplianceLocalCoreCertificate_MS,
        ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
          Eq.V_T ∈ C.D.carrier_T ∧ Eq.V_S ∈ C.D.carrier_S := by
  obtain ⟨E, hxb, _⟩ := symbolicEconomy_exists_strict
  obtain ⟨Eq, hVT, hVS, _⟩ :=
    AbstractGame.Params.standardCompliance_three_goals_local_MS_generalF
      E.toParams (E.certificateMS hxb)
      (AbstractGame.affineF_hF_top ⟨E.hδ0, E.hδ1⟩)
  exact ⟨E, E.certificateMS hxb, Eq, hVT, hVS⟩

/-- **The main deliverable: a symbolic, non-empty, certificate-bearing
family.** There is an admissible member — and hence, by the theorem above,
the whole admissible region is inhabited — and *every* admissible member
carries a complete compliance certificate, a forward-looking equilibrium in
the closed-form carriers, and the maximal regime separation (myopic sanction
identically `0`, forward-looking sanction identically `1`). -/
theorem symbolic_certified_family_nonvacuous :
    ∃ E : SymbolicEconomy,
      Nonempty E.toParams.StandardComplianceLocalCoreCertificate
      ∧ ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
          Eq.V_T ∈ E.carrierT ∧ Eq.V_S ∈ E.carrierS
          ∧ ∀ x ∈ Sanctions.S,
              E.toParams.myopicEquilibriumRule E.symMyopic x = 0
              ∧ E.toParams.dynamicEquilibriumRule Eq x = 1 := by
  obtain ⟨E⟩ := symbolicEconomy_nonempty
  exact ⟨E, ⟨E.certificate⟩, E.regime_separation⟩

/-! ## Axiom hygiene (Rule 10) -/

#print axioms SymbolicEconomy.certificate
#print axioms SymbolicEconomy.certificateMS
#print axioms SymbolicEconomy.myopic_argmax_sigma_eq_zero
#print axioms SymbolicEconomy.myopic_argmax_sigma_eq_zero_of_myopicAlpha_lt_one
#print axioms SymbolicEconomy.canonical_myopic_ceiling
#print axioms SymbolicEconomy.lockinValue_eq
#print axioms symbolic_equilibrium_feedback_decomposition
#print axioms symbolic_lockin_amplification
#print axioms SymbolicEconomy.cornerStagePayoff_pos
#print axioms symbolic_lockin_strict
#print axioms symbolic_lockin_strict_iff
#print axioms symbolic_VTstar_βS_invariant
#print axioms symbolicEconomy_exists_strict
#print axioms symbolic_MS_certified_family_nonvacuous
#print axioms symbolic_MS_headline_equilibrium
#print axioms SymbolicEconomy.certificateSchur
#print axioms SymbolicEconomy.valueClass_IsInvariant
#print axioms SymbolicEconomy.VSstar_bellman_fix
#print axioms SymbolicEconomy.VTstar_bellman_fix
#print axioms SymbolicEconomy.σ_dyn_top_eq_one
#print axioms SymbolicEconomy.α_on_eq_zero
#print axioms SymbolicEconomy.symMyopic
#print axioms symMyopic_isMaxOn
#print axioms SymbolicEconomy.three_goals_dominance
#print axioms SymbolicEconomy.regime_separation
#print axioms SymbolicEconomy.unique_in_carrier
#print axioms SymbolicEconomy.unique_in_carrier_of_mem
#print axioms symbolicEconomy_nonempty
#print axioms symbolic_certified_family_nonvacuous

end

end Examples

end Sanctions
