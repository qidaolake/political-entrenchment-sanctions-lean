/-
# B2 non-monotone-continuation witness — the "designed-slice" economy

The FIRST economy in the non-monotone-continuation regime: the Sender's
continuation value peaks at the basin threshold and declines beyond it
(hardline consolidation backfires for the Sender), Milgrom–Shannon single
crossing PROVABLY FAILS on the basin (`b2f_not_singleCrossingOn`), yet the
B2 pair — per-state quasiconcavity + `MonotoneTransferOn` — holds, so the
certificate `hIDO_on` field is dischargeable through
`hIDO_on_of_quasiconcave_monotoneTransfer` (the 2026-07-02 user-approved
route), which has zero consumers before this file.

## Design (exact rationals; numeric probe: scratchpad `b2_probe.py`)

δ = 1/2, β_S = 1/2, β_T = 9/10; basin `xT = xS = s̄ = 1/2`; `F = affineF (1/2)`.

Slice family `f(s,x) = base(x) + hump(s,x)`:
* `base(y) = 8 − 2(y − 1/2)²` — the Sender carrier's pinned shape:
  interior-peaked at the basin threshold `y = 1/2`, hence NON-monotone on
  the state space (Lipschitz constant `KS = 2`).
* `hump(·,x)`: two-piece parabola in `s`, C¹ at the state-dependent vertex
  `p̃(x) = 7/8 + (4/3)(x − 5/8)⁺` (flat, then rising), left curvature
  `λ(x) = 4 − (x − 1/2)⁺ ∈ [7/2, 4]`, right curvature
  `ρ(x) = 1 + 40(x − 1/2)⁺ ∈ [1, 21]` — the right wing steepens in the
  state, which is what breaks single crossing at straddling pairs while
  the peak itself never falls (so `MonotoneTransferOn` survives).
* compensator `(λ/2)((p̃ − 1)⁺)²` makes `max_{s∈[0,1]} hump(s,x) = 0`
  EXACTLY, so the Sender Bellman image of a carrier member is closed-form.

`U_S(x,a,s) = f(s,x) − 2as − (1/2)·base((x+s)/2)` is reverse-engineered so
that the Sender dynamic objective at carrier member `base + t` is exactly
`f(s,x) − 2as + t/2`: the `−(1/2)·base∘F` stage term cancels the
`β_S·(base + t)∘F` continuation, making carrier invariance exact algebra.

`U_T(x,a,s) = 5x − (9/2)·((x+s)/2) + (1/2)(s − p(x)) − a/50` with
`p = min 1 p̃`: the `−(9/2)·F` term cancels `β_T·5·F` of the affine
slope-5 Target carrier, and the leader integrand strictly decreases in
`a` (slope ≤ −1/50), pinning the derived leader policy at `a = 0`.

Stage-1 content (this file section): primitives, bounds, the two-branch
chord calculus for the static Sender response `b2σ` (clipped vertex of the
two-piece concave stage objective), the `Params` instance, and the
Rule-11 single-crossing refutation at the slice family.
-/

import Sanctions.Theory.Certificates.StandardComplianceLocal
import Sanctions.Theory.Certificates.StandardComplianceLocalDischargers
import Sanctions.Examples.Math.TwoBranchQuadraticSlice
import Sanctions.Examples.EECertWitness
import Sanctions.Examples.WitnessKit
-- `affine_sender_chord_on`, which discharges this economy's `hF_chord` field.
import Sanctions.Examples.AffineInstance.Certificates
import Sanctions.Examples.AffineInstance.TransitionChords

namespace Sanctions
namespace Examples

open AbstractGame.Params

noncomputable section

/-! ## 1. Primitives -/

/-- State clip: all state-dependent coefficients read the state through
`[0,1]`, so every bound below holds for ALL real `x` (as the `Params`
field signatures require). -/
def b2clip (x : ℝ) : ℝ := min (max x 0) 1

/-- Left curvature `λ(x) = 4 − (x − 1/2)⁺ ∈ [7/2, 4]`. -/
def b2lam (x : ℝ) : ℝ := 4 - max (b2clip x - 1/2) 0

/-- Right curvature `ρ(x) = 1 + 40(x − 1/2)⁺ ∈ [1, 21]`. -/
def b2rho (x : ℝ) : ℝ := 1 + 40 * max (b2clip x - 1/2) 0

/-- Slice vertex `p̃(x) = 7/8 + (4/3)(x − 5/8)⁺ ∈ [7/8, 11/8]`:
flat on `[0, 5/8]`, rising after, exceeding `1` for `x > 23/32`. -/
def b2pt (x : ℝ) : ℝ := 7/8 + (4/3) * max (b2clip x - 5/8) 0

/-- Realized (clipped) slice peak `p(x) = min 1 p̃(x)`. -/
def b2p (x : ℝ) : ℝ := min 1 (b2pt x)

/-- The Sender carrier's pinned shape: interior-peaked, non-monotone. -/
def b2base (y : ℝ) : ℝ := 8 - 2 * (y - 1/2)^2

/-- Compensator making `max_{s ∈ [0,1]} hump(s,x) = 0` exactly. -/
def b2comp (x : ℝ) : ℝ := (b2lam x / 2) * (max (b2pt x - 1) 0)^2

/-- Two-piece parabola in `s` (C¹ at `p̃(x)`), plus compensator. -/
def b2hump (s x : ℝ) : ℝ :=
  -(b2lam x / 2) * (max (b2pt x - s) 0)^2
    - (b2rho x / 2) * (max (s - b2pt x) 0)^2 + b2comp x

/-- The designed slice family: the Sender dynamic objective at the
equilibrium leader action and carrier member `t = 0`. -/
def b2f (s x : ℝ) : ℝ := b2base x + b2hump s x

/-- Sender stage payoff (reverse-engineered: `−(1/2)·base∘F` cancels the
carrier continuation exactly). -/
def b2U_S (x a s : ℝ) : ℝ := b2f s x - 2*a*s - (1/2) * b2base ((x + s)/2)

/-- Target stage payoff (the `−(9/2)·F` term cancels the affine slope-5
Target carrier continuation exactly; compliance cost `1/50`). -/
def b2U_T (x a s : ℝ) : ℝ :=
  5*x - (9/2) * ((x + s)/2) + (1/2) * (s - b2p x) - a/50

/-- Stage-objective derivative at the vertex `p̃` (both branches agree):
`e = (x + p̃)/2 − 1/2 − 2a`. Sign decides which branch carries the max. -/
def b2e (x a : ℝ) : ℝ := (x + b2pt x)/2 - 1/2 - 2*a

/-- Unclipped stage argmax: `p̃ + e⁻/(λ − 1/2) + e⁺/(ρ − 1/2)`. -/
def b2vertex (x a : ℝ) : ℝ :=
  b2pt x + min (b2e x a) 0 / (b2lam x - 1/2) + max (b2e x a) 0 / (b2rho x - 1/2)

/-- Static Sender response: the clipped vertex. -/
def b2σ (x a : ℝ) : ℝ := min 1 (max 0 (b2vertex x a))

/-! ## 2. Coefficient bounds -/

theorem b2clip_mem (x : ℝ) : b2clip x ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_min (le_max_right x 0) zero_le_one, min_le_right _ _⟩

theorem b2lam_lb (x : ℝ) : (7:ℝ)/2 ≤ b2lam x := by
  have h := (b2clip_mem x).2
  have : max (b2clip x - 1/2) 0 ≤ 1/2 := max_le (by linarith) (by norm_num)
  unfold b2lam; linarith

theorem b2lam_ub (x : ℝ) : b2lam x ≤ 4 := by
  have : (0:ℝ) ≤ max (b2clip x - 1/2) 0 := le_max_right _ _
  unfold b2lam; linarith

theorem b2rho_lb (x : ℝ) : (1:ℝ) ≤ b2rho x := by
  have : (0:ℝ) ≤ max (b2clip x - 1/2) 0 := le_max_right _ _
  unfold b2rho; linarith

theorem b2rho_ub (x : ℝ) : b2rho x ≤ 21 := by
  have h := (b2clip_mem x).2
  have : max (b2clip x - 1/2) 0 ≤ 1/2 := max_le (by linarith) (by norm_num)
  unfold b2rho; linarith

theorem b2pt_lb (x : ℝ) : (7:ℝ)/8 ≤ b2pt x := by
  have : (0:ℝ) ≤ max (b2clip x - 5/8) 0 := le_max_right _ _
  unfold b2pt; linarith

theorem b2pt_ub (x : ℝ) : b2pt x ≤ 11/8 := by
  have h := (b2clip_mem x).2
  have : max (b2clip x - 5/8) 0 ≤ 3/8 := max_le (by linarith) (by norm_num)
  unfold b2pt; linarith

theorem b2lam_half_pos (x : ℝ) : (0:ℝ) < b2lam x - 1/2 := by
  have := b2lam_lb x; linarith

theorem b2rho_half_pos (x : ℝ) : (0:ℝ) < b2rho x - 1/2 := by
  have := b2rho_lb x; linarith

/-! ## 3. Branch formulas and chord identities

On each side of the vertex the stage objective is an explicit quadratic;
every monotonicity fact below reduces to a chord identity (pure `ring`,
no divisions) plus a sign argument.  -/

theorem b2e_def (x a : ℝ) : b2e x a = (x + b2pt x)/2 - 1/2 - 2*a := rfl

/-- Left-branch closed form (`s ≤ p̃`). -/
theorem b2U_S_left (x a : ℝ) {s : ℝ} (h : s ≤ b2pt x) :
    b2U_S x a s
      = b2base x + b2comp x - 4 - (b2lam x / 2) * (b2pt x - s)^2
        - 2*a*s + ((x + s)/2 - 1/2)^2 := by
  unfold b2U_S b2f b2hump
  rw [max_eq_left (by linarith : (0:ℝ) ≤ b2pt x - s),
      max_eq_right (by linarith : s - b2pt x ≤ 0)]
  unfold b2base; ring

/-- Right-branch closed form (`p̃ ≤ s`). -/
theorem b2U_S_right (x a : ℝ) {s : ℝ} (h : b2pt x ≤ s) :
    b2U_S x a s
      = b2base x + b2comp x - 4 - (b2rho x / 2) * (s - b2pt x)^2
        - 2*a*s + ((x + s)/2 - 1/2)^2 := by
  unfold b2U_S b2f b2hump
  rw [max_eq_right (by linarith : b2pt x - s ≤ 0),
      max_eq_left (by linarith : (0:ℝ) ≤ s - b2pt x)]
  unfold b2base; ring

/-- Left-branch chord identity: for `s, s' ≤ p̃`,
`U_S(s') − U_S(s) = (s' − s)·[(λ − 1/2)(p̃ − (s+s')/2) + e]`. -/
theorem b2_left_chord (x a : ℝ) {s s' : ℝ}
    (hs : s ≤ b2pt x) (hs' : s' ≤ b2pt x) :
    b2U_S x a s' - b2U_S x a s
      = (s' - s) * ((b2lam x - 1/2) * (b2pt x - (s + s')/2) + b2e x a) := by
  rw [b2U_S_left x a hs, b2U_S_left x a hs', b2e_def]; ring

/-- Right-branch chord identity: for `p̃ ≤ s, s'`,
`U_S(s') − U_S(s) = (s' − s)·[(ρ − 1/2)(p̃ − (s+s')/2) + e]`. -/
theorem b2_right_chord (x a : ℝ) {s s' : ℝ}
    (hs : b2pt x ≤ s) (hs' : b2pt x ≤ s') :
    b2U_S x a s' - b2U_S x a s
      = (s' - s) * ((b2rho x - 1/2) * (b2pt x - (s + s')/2) + b2e x a) := by
  rw [b2U_S_right x a hs, b2U_S_right x a hs', b2e_def]; ring

/-! ## 4. Vertex case formulas -/

theorem b2vertex_of_nonpos (x a : ℝ) (he : b2e x a ≤ 0) :
    b2vertex x a = b2pt x + b2e x a / (b2lam x - 1/2) := by
  unfold b2vertex
  rw [min_eq_left he, max_eq_right he, zero_div, add_zero]

theorem b2vertex_of_nonneg (x a : ℝ) (he : 0 ≤ b2e x a) :
    b2vertex x a = b2pt x + b2e x a / (b2rho x - 1/2) := by
  unfold b2vertex
  rw [min_eq_right he, max_eq_left he, zero_div, add_zero]

/-! ## 5. Stage-objective monotonicity on the two sides of the vertex -/

/-- The stage objective is nondecreasing up to the (unclipped) vertex. -/
theorem b2U_S_mono_up (x a : ℝ) {s s' : ℝ}
    (h1 : s ≤ s') (h2 : s' ≤ b2vertex x a) :
    b2U_S x a s ≤ b2U_S x a s' := by
  have hlamPos := b2lam_half_pos x
  have hrhoPos := b2rho_half_pos x
  rcases le_total (b2e x a) 0 with he | he
  · -- vertex on the left branch: both points below the kink
    have hveq := b2vertex_of_nonpos x a he
    have hdivnp : b2e x a / (b2lam x - 1/2) ≤ 0 := by
      have h0 : 0 ≤ -b2e x a / (b2lam x - 1/2) :=
        div_nonneg (neg_nonneg.2 he) hlamPos.le
      rw [neg_div] at h0
      linarith
    have hv_pt : b2vertex x a ≤ b2pt x := by rw [hveq]; linarith
    have hkey : (s' - b2pt x) * (b2lam x - 1/2) ≤ b2e x a := by
      have h2' : s' - b2pt x ≤ b2e x a / (b2lam x - 1/2) := by
        rw [hveq] at h2; linarith
      have := mul_le_mul_of_nonneg_right h2' hlamPos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hlamPos)] at this
    have hD := b2_left_chord x a
      (le_trans h1 (le_trans h2 hv_pt)) (le_trans h2 hv_pt)
    have h3 : (s' - s) * ((s' - b2pt x) * (b2lam x - 1/2))
        ≤ (s' - s) * b2e x a :=
      mul_le_mul_of_nonneg_left hkey (by linarith)
    nlinarith [hD, h3,
      mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1)) hlamPos.le]
  · -- vertex on the right branch
    have hveq := b2vertex_of_nonneg x a he
    have hkeyR : (s' - b2pt x) * (b2rho x - 1/2) ≤ b2e x a := by
      have h2' : s' - b2pt x ≤ b2e x a / (b2rho x - 1/2) := by
        rw [hveq] at h2; linarith
      have := mul_le_mul_of_nonneg_right h2' hrhoPos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hrhoPos)] at this
    rcases le_total s' (b2pt x) with hs'pt | hs'pt
    · -- both on the left branch, vertex still to the right: `e > 0`
      have hD := b2_left_chord x a (le_trans h1 hs'pt) hs'pt
      nlinarith [hD,
        mul_nonneg (sub_nonneg.2 h1)
          (mul_nonneg hlamPos.le
            (by linarith : (0:ℝ) ≤ b2pt x - (s + s')/2)),
        mul_nonneg (sub_nonneg.2 h1) he]
    · rcases le_total (b2pt x) s with hspt | hspt
      · -- both on the right branch
        have hD := b2_right_chord x a hspt hs'pt
        have h3 : (s' - s) * ((s' - b2pt x) * (b2rho x - 1/2))
            ≤ (s' - s) * b2e x a :=
          mul_le_mul_of_nonneg_left hkeyR (by linarith)
        nlinarith [hD, h3,
          mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1))
            hrhoPos.le]
      · -- straddle: `s ≤ p̃ ≤ s'` — pass through the kink
        have step1 : b2U_S x a s ≤ b2U_S x a (b2pt x) := by
          have hD := b2_left_chord x a hspt (le_refl (b2pt x))
          nlinarith [hD,
            mul_nonneg (sub_nonneg.2 hspt)
              (mul_nonneg hlamPos.le
                (by linarith : (0:ℝ) ≤ b2pt x - (s + b2pt x)/2)),
            mul_nonneg (sub_nonneg.2 hspt) he]
        have step2 : b2U_S x a (b2pt x) ≤ b2U_S x a s' := by
          have hD := b2_right_chord x a (le_refl (b2pt x)) hs'pt
          have h3 : (s' - b2pt x) * ((s' - b2pt x) * (b2rho x - 1/2))
              ≤ (s' - b2pt x) * b2e x a :=
            mul_le_mul_of_nonneg_left hkeyR (sub_nonneg.2 hs'pt)
          nlinarith [hD, h3,
            mul_nonneg (mul_nonneg (sub_nonneg.2 hs'pt)
              (sub_nonneg.2 hs'pt)) hrhoPos.le]
        exact le_trans step1 step2

/-- The stage objective is nonincreasing beyond the (unclipped) vertex. -/
theorem b2U_S_mono_down (x a : ℝ) {s s' : ℝ}
    (h1 : b2vertex x a ≤ s') (h2 : s' ≤ s) :
    b2U_S x a s ≤ b2U_S x a s' := by
  have hlamPos := b2lam_half_pos x
  have hrhoPos := b2rho_half_pos x
  rcases le_total (b2e x a) 0 with he | he
  · -- vertex on the left branch
    have hveq := b2vertex_of_nonpos x a he
    have hkeyL : b2e x a ≤ (s' - b2pt x) * (b2lam x - 1/2) := by
      have h1' : b2e x a / (b2lam x - 1/2) ≤ s' - b2pt x := by
        rw [hveq] at h1; linarith
      have := mul_le_mul_of_nonneg_right h1' hlamPos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hlamPos)] at this
    rcases le_total s (b2pt x) with hspt | hspt
    · -- both on the left branch
      have hD := b2_left_chord x a hspt (le_trans h2 hspt)
      have h3 : (s' - b2pt x) * (b2lam x - 1/2) * (s' - s)
          ≤ b2e x a * (s' - s) := by
        nlinarith [hkeyL, sub_nonneg.2 h2]
      nlinarith [hD, h3,
        mul_nonneg (mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2)) hlamPos.le]
    · rcases le_total (b2pt x) s' with hs'pt | hs'pt
      · -- both on the right branch: `p̃ ≤ s' ≤ s`, `e ≤ 0`
        have hD := b2_right_chord x a hspt hs'pt
        nlinarith [hD,
          mul_nonneg (sub_nonneg.2 h2)
            (mul_nonneg hrhoPos.le
              (by linarith : (0:ℝ) ≤ (s + s')/2 - b2pt x)),
          mul_nonneg (sub_nonneg.2 h2) (neg_nonneg.2 he)]
      · -- straddle: `s' ≤ p̃ ≤ s`
        have step1 : b2U_S x a s ≤ b2U_S x a (b2pt x) := by
          have hD := b2_right_chord x a hspt (le_refl (b2pt x))
          nlinarith [hD,
            mul_nonneg (sub_nonneg.2 hspt)
              (mul_nonneg hrhoPos.le
                (by linarith : (0:ℝ) ≤ (s + b2pt x)/2 - b2pt x)),
            mul_nonneg (sub_nonneg.2 hspt) (neg_nonneg.2 he)]
        have step2 : b2U_S x a (b2pt x) ≤ b2U_S x a s' := by
          have hD := b2_left_chord x a (le_refl (b2pt x)) hs'pt
          have h3 : b2e x a * (b2pt x - s')
              ≤ (s' - b2pt x) * (b2lam x - 1/2) * (b2pt x - s') :=
            mul_le_mul_of_nonneg_right hkeyL (sub_nonneg.2 hs'pt)
          nlinarith [hD, h3,
            mul_nonneg (mul_nonneg (sub_nonneg.2 hs'pt)
              (sub_nonneg.2 hs'pt)) hlamPos.le]
        exact le_trans step1 step2
  · -- vertex on the right branch: both points above the kink
    have hveq := b2vertex_of_nonneg x a he
    have hdivnn : 0 ≤ b2e x a / (b2rho x - 1/2) := div_nonneg he hrhoPos.le
    have hpt_v : b2pt x ≤ b2vertex x a := by rw [hveq]; linarith
    have hkeyR : b2e x a ≤ (s' - b2pt x) * (b2rho x - 1/2) := by
      have h1' : b2e x a / (b2rho x - 1/2) ≤ s' - b2pt x := by
        rw [hveq] at h1; linarith
      have := mul_le_mul_of_nonneg_right h1' hrhoPos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hrhoPos)] at this
    have hD := b2_right_chord x a
      (le_trans (le_trans hpt_v h1) h2) (le_trans hpt_v h1)
    have h3 : (s' - b2pt x) * (b2rho x - 1/2) * (s' - s)
        ≤ b2e x a * (s' - s) := by
      nlinarith [hkeyR, sub_nonneg.2 h2]
    nlinarith [hD, h3,
      mul_nonneg (mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2)) hrhoPos.le]

/-! ## 6. The static response: feasibility, optimality, continuity -/

theorem b2σ_mem (x a : ℝ) : b2σ x a ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left 0 _), min_le_left _ _⟩

/-- **Rule-1 coupling**: `b2σ x a` is the stage argmax of `U_S(x,a,·)`
on `[0,1]` — the clipped vertex of the two-piece concave objective. -/
theorem b2σ_isMaxOn (x a : ℝ) :
    IsMaxOn (fun s => b2U_S x a s) (Set.Icc (0:ℝ) 1) (b2σ x a) := by
  rw [isMaxOn_iff]
  intro s hs
  rcases le_total (b2vertex x a) 0 with hv | hv
  · -- clipped at 0
    have hσ : b2σ x a = 0 := by
      unfold b2σ; rw [max_eq_left hv, min_eq_right zero_le_one]
    calc b2U_S x a s ≤ b2U_S x a 0 := b2U_S_mono_down x a hv hs.1
    _ = b2U_S x a (b2σ x a) := by rw [hσ]
  · rcases le_total 1 (b2vertex x a) with hv1 | hv1
    · -- clipped at 1
      have hσ : b2σ x a = 1 := by
        unfold b2σ; rw [max_eq_right hv, min_eq_left hv1]
      calc b2U_S x a s ≤ b2U_S x a 1 := b2U_S_mono_up x a hs.2 hv1
      _ = b2U_S x a (b2σ x a) := by rw [hσ]
    · -- interior vertex
      have hσ : b2σ x a = b2vertex x a := by
        unfold b2σ; rw [max_eq_right hv, min_eq_right hv1]
      rcases le_total s (b2vertex x a) with hsv | hsv
      · calc b2U_S x a s ≤ b2U_S x a (b2vertex x a) :=
              b2U_S_mono_up x a hsv (le_refl _)
        _ = b2U_S x a (b2σ x a) := by rw [hσ]
      · calc b2U_S x a s ≤ b2U_S x a (b2vertex x a) :=
              b2U_S_mono_down x a (le_refl _) hsv
        _ = b2U_S x a (b2σ x a) := by rw [hσ]

theorem b2σ_continuous :
    Continuous (fun xa : ℝ × ℝ => b2σ xa.1 xa.2) := by
  have hpt : Continuous fun xa : ℝ × ℝ => b2pt xa.1 := by
    unfold b2pt b2clip; fun_prop
  have he : Continuous fun xa : ℝ × ℝ => b2e xa.1 xa.2 := by
    unfold b2e b2pt b2clip; fun_prop
  have hlam : Continuous fun xa : ℝ × ℝ => b2lam xa.1 - 1/2 := by
    unfold b2lam b2clip; fun_prop
  have hrho : Continuous fun xa : ℝ × ℝ => b2rho xa.1 - 1/2 := by
    unfold b2rho b2clip; fun_prop
  have h1 : Continuous fun xa : ℝ × ℝ =>
      min (b2e xa.1 xa.2) 0 / (b2lam xa.1 - 1/2) :=
    (he.min continuous_const).div hlam
      (fun xa => ne_of_gt (b2lam_half_pos xa.1))
  have h2 : Continuous fun xa : ℝ × ℝ =>
      max (b2e xa.1 xa.2) 0 / (b2rho xa.1 - 1/2) :=
    (he.max continuous_const).div hrho
      (fun xa => ne_of_gt (b2rho_half_pos xa.1))
  unfold b2σ b2vertex
  exact continuous_const.min
    (continuous_const.max ((hpt.add h1).add h2))

theorem b2U_S_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => b2U_S xas.1 xas.2.1 xas.2.2) := by
  unfold b2U_S b2f b2hump b2comp b2base b2lam b2rho b2pt b2clip
  fun_prop

theorem b2U_T_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => b2U_T xas.1 xas.2.1 xas.2.2) := by
  unfold b2U_T b2p b2pt b2clip
  fun_prop

/-! ## 7. The `Params` instance -/

/-- **The B2 witness `Params` (designed-slice economy).** -/
def b2Params : AbstractGame.Params where
  δ := 1/2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 9/10
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1/2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := b2U_T
  U_S := b2U_S
  σ := b2σ
  σ_mem := b2σ_mem
  σ_isMaxOn_U_S := b2σ_isMaxOn
  U_T_continuous := b2U_T_continuous
  U_S_continuous := b2U_S_continuous
  F := AbstractGame.affineF (1/2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := AbstractGame.affineF_diag _

/-- **`b2Params` has a continuous static Sender selector.** Affine-restricted: a concrete
member with the affine transition `affineF (1/2)`; the selector itself does not read the
transition. The proof is the one that was the economy's `σ_continuous` field until round
BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance b2Params_staticSelectorContinuous :
    b2Params.StaticSelectorContinuous where
  σ_continuous := b2σ_continuous

@[simp] theorem b2Params_U_S : b2Params.U_S = b2U_S := rfl
@[simp] theorem b2Params_U_T : b2Params.U_T = b2U_T := rfl
@[simp] theorem b2Params_σ : b2Params.σ = b2σ := rfl
@[simp] theorem b2Params_δ : b2Params.δ = 1/2 := rfl
@[simp] theorem b2Params_β_S : b2Params.β_S = 1/2 := rfl
@[simp] theorem b2Params_β_T : b2Params.β_T = 9/10 := rfl

/-- Transition closed form: `F(x,s) = (x+s)/2`. -/
theorem b2Params_F (x s : ℝ) : b2Params.F x s = (x + s)/2 := by
  show AbstractGame.affineF (1/2) x s = (x + s)/2
  unfold AbstractGame.affineF; ring

/-! ## 8. Rule-11 exhibit: single crossing FAILS at the slice family

The designed slice family is an instance of the general **two-branch
quadratic slice family** of `Foundations/TwoBranchQuadraticSlice.lean`:
a state-only level term, minus a quadratic loss away from a
state-dependent peak, with left curvature `λ(x)` and right curvature
`ρ(x)`.  The single-crossing refutation here, and the branch forms,
single-peakedness and monotonicity-transfer facts of §9, are therefore
specialisations of theorems proved there over symbolic `λ, ρ, p` — no
numeric configuration is doing the work (Rule 5).

The general separation result says: monotone peaks plus positive
curvatures always deliver the ordinal interval-dominance input
(`MonotoneTransferOn`, §9), while single crossing is refuted as soon as
the **curvature ratio** `ρ/λ` strictly increases across a parameter pair
whose peak is unchanged.  At this economy the pair `(1/2, 5/8)` has the
common peak `p̃ = 7/8` and ratios `ρ/λ = 1/4` at `x = 1/2` against
`48/31` at `x = 5/8`, so the refutation applies: the right wing has
steepened while the peak stayed put.  The offending low choice is not
picked by hand — the general theorem constructs it as
`p̃ − √(ρ/λ)·(s'' − p̃)`, the point on the left branch that the LOW state
finds exactly as good as the top sanction `s'' = 1`.  Hence the weak
Milgrom–Shannon transfer clause fails on the exact certificate rectangle
`I × [1/2, 1]`, and the SC upcast route to the certificate's `hIDO_on`
field is provably unavailable at this economy: the B2 discharger is the
sole route. -/

/-- **The designed slice family IS the general two-branch quadratic
family** with left curvature `λ = b2lam`, right curvature `ρ = b2rho`,
peak `p = b2pt`, and state-only level `base + compensator`.  This is the
bridge that turns every §8/§9 fact about `b2f` into a one-line
specialisation of a symbolic theorem. -/
theorem b2f_eq_slice :
    (fun s x => b2f s x)
      = Sanctions.TwoBranchQuadratic.slice
          (fun x => b2base x + b2comp x) b2lam b2rho b2pt := by
  funext s x
  unfold b2f b2hump Sanctions.TwoBranchQuadratic.slice
  ring

/-- Pointwise form of `b2f_eq_slice`. -/
theorem b2f_eq_slice_apply (s x : ℝ) :
    b2f s x = Sanctions.TwoBranchQuadratic.slice
      (fun x => b2base x + b2comp x) b2lam b2rho b2pt s x :=
  congrFun (congrFun b2f_eq_slice s) x

/-- Closed forms on the **flat-peak stretch** `[1/2, 5/8]` — the states
at or above the basin threshold but below the kink in `p̃`.  There the
peak is pinned at `7/8`, the left curvature falls linearly and the right
curvature rises linearly in the state. -/
private theorem b2_flatPeak_forms {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 2 : ℝ) (5 / 8)) :
    b2pt x = 7/8 ∧ b2lam x = 4 - (x - 1/2) ∧ b2rho x = 1 + 40*(x - 1/2) := by
  obtain ⟨hlo, hhi⟩ := hx
  have hclip : b2clip x = x := by
    unfold b2clip
    rw [max_eq_left (by linarith : (0:ℝ) ≤ x), min_eq_left (by linarith : x ≤ 1)]
  refine ⟨?_, ?_, ?_⟩
  · unfold b2pt
    rw [hclip, max_eq_right (by linarith : x - 5/8 ≤ 0)]; ring
  · unfold b2lam
    rw [hclip, max_eq_left (by linarith : (0:ℝ) ≤ x - 1/2)]
  · unfold b2rho
    rw [hclip, max_eq_left (by linarith : (0:ℝ) ≤ x - 1/2)]

/-- **Single crossing fails at EVERY ordered pair of distinct states on
the flat-peak stretch** `[1/2, 5/8]` — the failure is a structural
feature of the designed slice family, not a numeric coincidence at one
hand-picked pair.

On `[1/2, 5/8]` the peak is pinned at `p̃ = 7/8` (the kink in `p̃` sits at
`5/8`) while the curvature ratio
`ρ(x)/λ(x) = (1 + 40(x − 1/2)) / (4 − (x − 1/2))` is strictly increasing
in the state: the right wing steepens relative to the left wing while
the peak stays put.  That is exactly the hypothesis of the general
refutation `TwoBranchQuadratic.not_singleCrossingOn_slice_of_ratio_lt`,
which then builds the offending pair of sanctions for us — the top
sanction `s'' = 1` against the left-branch point
`p̃ − √(ρ(x₁)/λ(x₁))·(1 − p̃)` that the LOW state finds exactly as good.
No sanction level and no state is chosen by hand here. -/
theorem b2f_not_singleCrossingOn_of_flatPeak {x₁ x₂ : ℝ}
    (h₁ : x₁ ∈ Set.Icc (1 / 2 : ℝ) (5 / 8))
    (h₂ : x₂ ∈ Set.Icc (1 / 2 : ℝ) (5 / 8)) (hlt : x₁ < x₂) :
    ¬ Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc (1/2 : ℝ) 1) (fun s x => b2f s x) := by
  obtain ⟨hp₁, hl₁, hr₁⟩ := b2_flatPeak_forms h₁
  obtain ⟨hp₂, hl₂, hr₂⟩ := b2_flatPeak_forms h₂
  have hlpos₁ : (0:ℝ) < b2lam x₁ := by have := b2lam_lb x₁; linarith
  have hlpos₂ : (0:ℝ) < b2lam x₂ := by have := b2lam_lb x₂; linarith
  have hrnn₁ : (0:ℝ) ≤ b2rho x₁ := by have := b2rho_lb x₁; linarith
  -- the curvature ratio strictly increases across the pair
  have hratio : b2rho x₁ / b2lam x₁ < b2rho x₂ / b2lam x₂ := by
    rw [hl₁, hl₂, hr₁, hr₂,
      div_lt_div_iff₀ (by linarith [h₁.2] : (0:ℝ) < 4 - (x₁ - 1/2))
        (by linarith [h₂.2] : (0:ℝ) < 4 - (x₂ - 1/2))]
    nlinarith
  -- the constructed left-branch sanction is feasible
  have hq0 : 0 ≤ Real.sqrt (b2rho x₁ / b2lam x₁) := Real.sqrt_nonneg _
  have hq7 : Real.sqrt (b2rho x₁ / b2lam x₁) < 7 := by
    have hb : b2rho x₁ / b2lam x₁ < 7 ^ 2 := by
      rw [div_lt_iff₀ hlpos₁]
      nlinarith [b2rho_ub x₁, b2lam_lb x₁]
    exact (Real.sqrt_lt' (by norm_num)).2 hb
  rw [b2f_eq_slice]
  exact Sanctions.TwoBranchQuadratic.not_singleCrossingOn_slice_of_ratio_lt
    (x₁ := x₁) (x₂ := x₂) (s'' := 1)
    ⟨h₁.1, by linarith [h₁.2]⟩ ⟨h₂.1, by linarith [h₂.2]⟩ hlt.le
    ⟨by norm_num, le_refl _⟩
    (by rw [hp₁]; exact ⟨by linarith, by linarith⟩)
    (by rw [hp₁, hp₂]) hlpos₁ hlpos₂ hrnn₁ hratio (by rw [hp₁]; norm_num)

/-- The single-crossing refutation at the certificate's own state pair:
a one-line specialisation (Rule 5) of the flat-peak-stretch theorem at
the basin threshold `1/2` and the peak kink `5/8`. -/
theorem b2f_not_singleCrossingOn :
    ¬ Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc (1/2 : ℝ) 1) (fun s x => b2f s x) :=
  b2f_not_singleCrossingOn_of_flatPeak
    ⟨le_refl _, by norm_num⟩ ⟨by norm_num, le_refl _⟩ (by norm_num)

/-! ## 9. Slice kernel: branch forms, monotonicity, the MT proof

The B2 pair lives here: the slice peak `p̃` never falls in the state
(`b2pt_mono`), each slice strictly rises left of its peak and strictly
falls right of it, so on any choice interval where a LOWER slice is
monotone the interval sits left of that slice's peak — and hence left of
every HIGHER slice's peak, where the higher slice strictly rises. That
is `MonotoneTransferOn`, proved analytically (no grid). Single crossing
fails anyway (§8) because the right wing steepens: level comparisons at
straddling pairs reverse even though the peak never falls. -/

theorem b2f_left_eq (x : ℝ) {s : ℝ} (h : s ≤ b2pt x) :
    b2f s x = b2base x + b2comp x - (b2lam x / 2) * (b2pt x - s)^2 := by
  rw [b2f_eq_slice_apply]
  exact Sanctions.TwoBranchQuadratic.slice_left x h

theorem b2f_right_eq (x : ℝ) {s : ℝ} (h : b2pt x ≤ s) :
    b2f s x = b2base x + b2comp x - (b2rho x / 2) * (s - b2pt x)^2 := by
  rw [b2f_eq_slice_apply]
  exact Sanctions.TwoBranchQuadratic.slice_right x h

/-- The slice peak is nondecreasing in the state. -/
theorem b2pt_mono : Monotone b2pt := by
  intro a b hab
  have hclip : b2clip a ≤ b2clip b :=
    min_le_min (max_le_max hab (le_refl 0)) (le_refl 1)
  have hmax : max (b2clip a - 5/8) 0 ≤ max (b2clip b - 5/8) 0 :=
    max_le_max (by linarith) (le_refl 0)
  unfold b2pt
  linarith

/-- Each slice strictly rises left of its peak. -/
theorem b2f_left_lt (x : ℝ) {u v : ℝ} (hv : v ≤ b2pt x) (huv : u < v) :
    b2f u x < b2f v x := by
  simp only [b2f_eq_slice_apply]
  exact Sanctions.TwoBranchQuadratic.slice_lt_of_le_peak x
    (by linarith [b2lam_lb x]) hv huv

/-- Each slice strictly falls right of its peak. -/
theorem b2f_right_lt (x : ℝ) {u v : ℝ} (hu : b2pt x ≤ u) (huv : u < v) :
    b2f v x < b2f u x := by
  simp only [b2f_eq_slice_apply]
  exact Sanctions.TwoBranchQuadratic.slice_lt_of_peak_le x
    (by linarith [b2rho_lb x]) hu huv

/-- **`MonotoneTransferOn` HOLDS at the designed slice family** — the
Rule-3 regime primitive, proved outright at this concrete economy (the
"derive per payoff class" discharge plan of
`Foundations/IntervalDominanceOrder.lean` §6). One-line specialisation
(Rule 5) of `TwoBranchQuadratic.monotoneTransferOn_slice`, which proves
it for EVERY two-branch quadratic slice family with strictly positive
curvatures and a nondecreasing peak: the `MonotoneOn` gate forces the
choice interval left of the lower slice's peak (else the right wing
strictly falls), the peak never falls in the state, and every slice
strictly rises left of its own peak. No comparison between the
curvatures at different states is used — which is exactly why this
survives while single crossing (§8) does not. -/
theorem b2f_monotoneTransferOn :
    Sanctions.IntervalDominanceOrder.MonotoneTransferOn
      Sanctions.I (Set.Icc (1/2 : ℝ) 1) (fun s x => b2f s x) := by
  rw [b2f_eq_slice]
  exact Sanctions.TwoBranchQuadratic.monotoneTransferOn_slice
    (fun x _ => by linarith [b2lam_lb x]) (fun x _ => by linarith [b2rho_lb x])
    (b2pt_mono.monotoneOn _)

/-! ## 10. Strict concavity of every slice (plus any affine tilt)

The two-piece parabola with curvatures `−λ ≤ −7/2` (left) and
`−ρ ≤ −1` (right), glued C¹ at the peak, is strictly concave; adding
an affine function of `s` (the placation `−2as` and any carrier shift)
preserves this. Feeds both per-state quasiconcavity (`hQC`, via
concave ⇒ quasiconcave) and Sender argmax uniqueness (DAU). -/

private theorem b2gap_aux (x : ℝ) {u v p q : ℝ} (huv : u < v)
    (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1) (c₁ c₀ : ℝ) :
    p * (b2f u x + c₁*u + c₀) + q * (b2f v x + c₁*v + c₀)
      < b2f (p*u + q*v) x + c₁*(p*u + q*v) + c₀ := by
  have hq1 : q = 1 - p := by linarith
  subst hq1
  have hm_lt : p*u + (1-p)*v < v := by nlinarith
  have hm_gt : u < p*u + (1-p)*v := by nlinarith
  have hA := b2lam_lb x
  have hB := b2rho_lb x
  rcases le_total v (b2pt x) with hvpt | hvpt
  · -- all three points on the left branch
    have hu_pt : u ≤ b2pt x := le_trans huv.le hvpt
    have hm_pt : p*u + (1-p)*v ≤ b2pt x := le_trans hm_lt.le hvpt
    rw [b2f_left_eq x hu_pt, b2f_left_eq x hvpt, b2f_left_eq x hm_pt]
    nlinarith [mul_pos (mul_pos hp hq)
      (mul_pos (sub_pos.2 huv) (sub_pos.2 huv))]
  · rcases le_total (b2pt x) u with hupt | hupt
    · -- all three points on the right branch
      have hv_pt : b2pt x ≤ v := le_trans hupt huv.le
      have hm_pt : b2pt x ≤ p*u + (1-p)*v := le_trans hupt hm_gt.le
      rw [b2f_right_eq x hupt, b2f_right_eq x hv_pt, b2f_right_eq x hm_pt]
      nlinarith [mul_pos (mul_pos hp hq)
        (mul_pos (sub_pos.2 huv) (sub_pos.2 huv))]
    · -- straddle: `u ≤ p̃ ≤ v`
      rcases le_total (p*u + (1-p)*v) (b2pt x) with hmpt | hmpt
      · -- combination lands on the left branch
        have hU : (0:ℝ) < b2pt x - u := by nlinarith
        have hV : (0:ℝ) ≤ v - b2pt x := by linarith
        have hW : (1-p)*(v - b2pt x) ≤ p*(b2pt x - u) := by nlinarith
        have hkey := mul_le_mul_of_nonneg_left hW
          (mul_nonneg (by linarith : (0:ℝ) ≤ b2lam x)
            (mul_nonneg hq.le hV))
        rw [b2f_left_eq x hupt, b2f_right_eq x hvpt, b2f_left_eq x hmpt]
        nlinarith [hkey,
          mul_pos (mul_pos (show (0:ℝ) < b2lam x by linarith)
            (mul_pos hp hq)) (mul_pos hU hU),
          mul_nonneg (mul_nonneg (mul_nonneg
            (show (0:ℝ) ≤ b2lam x by linarith) hp.le) hq.le)
            (mul_nonneg hU.le hV),
          mul_nonneg (mul_nonneg (show (0:ℝ) ≤ b2rho x by linarith) hq.le)
            (mul_nonneg hV hV)]
      · -- combination lands on the right branch
        have hV : (0:ℝ) < v - b2pt x := by nlinarith
        have hU : (0:ℝ) ≤ b2pt x - u := by linarith
        have hW : p*(b2pt x - u) ≤ (1-p)*(v - b2pt x) := by nlinarith
        have hkey := mul_le_mul_of_nonneg_left hW
          (mul_nonneg (by linarith : (0:ℝ) ≤ b2rho x)
            (mul_nonneg hp.le hU))
        rw [b2f_left_eq x hupt, b2f_right_eq x hvpt, b2f_right_eq x hmpt]
        nlinarith [hkey,
          mul_pos (mul_pos (show (0:ℝ) < b2rho x by linarith)
            (mul_pos hp hq)) (mul_pos hV hV),
          mul_nonneg (mul_nonneg (mul_nonneg
            (show (0:ℝ) ≤ b2rho x by linarith) hp.le) hq.le)
            (mul_nonneg hU hV.le),
          mul_nonneg (mul_nonneg (show (0:ℝ) ≤ b2lam x by linarith) hp.le)
            (mul_nonneg hU hU)]

/-- Every slice, plus any affine tilt in the sanction, is strictly
concave on `[0,1]`. Kernel for both `hQC` and DAU. -/
theorem b2dynObj_strictConcaveOn (x c₁ c₀ : ℝ) :
    StrictConcaveOn ℝ (Set.Icc (0:ℝ) 1)
      (fun s => b2f s x + c₁*s + c₀) := by
  constructor
  · exact convex_Icc 0 1
  · intro u _hu v _hv huv p q hp hq hpq
    simp only [smul_eq_mul]
    rcases lt_or_gt_of_ne huv with h | h
    · exact b2gap_aux x h hp hq hpq c₁ c₀
    · have haux := b2gap_aux x h hq hp (by linarith) c₁ c₀
      have harg : q*v + p*u = p*u + q*v := by ring
      rw [harg] at haux
      linarith

/-! ## 11. Congruence helpers -/

/-- Strict concavity transports across pointwise equality on the set. -/
theorem b2_strictConcaveOn_congr {D : Set ℝ} {f g : ℝ → ℝ}
    (hD : Convex ℝ D) (hfg : ∀ z ∈ D, f z = g z)
    (hg : StrictConcaveOn ℝ D g) : StrictConcaveOn ℝ D f := by
  constructor
  · exact hD
  · intro u hu v hv huv p q hp hq hpq
    have hm : p • u + q • v ∈ D := hD hu hv hp.le hq.le hpq
    rw [hfg u hu, hfg v hv, hfg _ hm]
    exact hg.2 hu hv huv hp hq hpq

/-- `IsMaxOn` transports across pointwise equality on the set. -/
theorem b2_isMaxOn_congr {D : Set ℝ} {f g : ℝ → ℝ} {z : ℝ}
    (hz : z ∈ D) (hfg : ∀ w ∈ D, f w = g w)
    (hg : IsMaxOn g D z) : IsMaxOn f D z := by
  rw [isMaxOn_iff] at hg ⊢
  intro w hw
  rw [hfg w hw, hfg z hz]
  exact hg w hw

/-! ## 12. The dynamic Sender response in closed form

At any carrier member the Sender dynamic objective on `I` is
`f(s,x) − 2as + t/2` (§13 below): a two-piece parabola with curvatures
`λ, ρ` and tilt `−2a`. For `a ≥ 0` the tilt pulls the peak LEFT along
the left branch, so the argmax is `min 1 (p̃ − 2a/λ)` — interior on
part of the basin (the first witness with a state-varying interior
forward-looking response). -/

/-- Dynamic-response closed form (valid for `a ≥ 0`). -/
def b2sdyn (x a : ℝ) : ℝ := min 1 (b2pt x - 2*a/b2lam x)

/-- The pure dynamic objective (carrier shift dropped). -/
def b2dg (x a s : ℝ) : ℝ := b2f s x - 2*a*s

/-- The division bound `2a/λ ≤ 4/7` for `a ∈ [0,1]` (uses `λ ≥ 7/2`). -/
theorem b2sdyn_div_bounds (x : ℝ) {a : ℝ} (ha : a ∈ Sanctions.I) :
    0 ≤ 2*a/b2lam x ∧ 2*a/b2lam x ≤ 4/7 := by
  have hL := b2lam_lb x
  have hLpos0 : (0:ℝ) < b2lam x := by linarith
  have hd0 : 0 ≤ 2*a/b2lam x :=
    div_nonneg (by linarith [ha.1]) hLpos0.le
  have hdm : (2*a/b2lam x) * b2lam x = 2*a :=
    div_mul_cancel₀ _ (ne_of_gt hLpos0)
  refine ⟨hd0, ?_⟩
  nlinarith [ha.2, mul_nonneg hd0 (by linarith : (0:ℝ) ≤ b2lam x - 7/2)]

theorem b2sdyn_mem (x : ℝ) {a : ℝ} (ha : a ∈ Sanctions.I) :
    b2sdyn x a ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨hd0, hd7⟩ := b2sdyn_div_bounds x ha
  have hpt := b2pt_lb x
  exact ⟨le_min (by norm_num) (by linarith), min_le_left _ _⟩

theorem b2sdyn_le_pt (x : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    b2sdyn x a ≤ b2pt x := by
  have hL := b2lam_lb x
  have hdiv : 0 ≤ 2*a/b2lam x :=
    div_nonneg (by linarith) (by linarith)
  exact le_trans (min_le_right _ _) (by linarith)

/-- The dynamic response is nonincreasing in the compliance action. -/
theorem b2sdyn_anti (x : ℝ) {a₁ a₂ : ℝ} (h : a₁ ≤ a₂) :
    b2sdyn x a₂ ≤ b2sdyn x a₁ := by
  have hL := b2lam_lb x
  have hLpos0 : (0:ℝ) < b2lam x := by linarith
  apply min_le_min (le_refl 1)
  have hmul : 2*a₁ * (b2lam x)⁻¹ ≤ 2*a₂ * (b2lam x)⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith)
      (inv_nonneg.2 hLpos0.le)
  simp only [div_eq_mul_inv]
  linarith

/-- Left-branch dynamic chord. -/
theorem b2dg_left_chord (x a : ℝ) {s s' : ℝ}
    (hs : s ≤ b2pt x) (hs' : s' ≤ b2pt x) :
    b2dg x a s' - b2dg x a s
      = (s' - s) * (b2lam x * (b2pt x - (s + s')/2) - 2*a) := by
  unfold b2dg
  rw [b2f_left_eq x hs, b2f_left_eq x hs']
  ring

/-- Right-branch dynamic chord. -/
theorem b2dg_right_chord (x a : ℝ) {s s' : ℝ}
    (hs : b2pt x ≤ s) (hs' : b2pt x ≤ s') :
    b2dg x a s' - b2dg x a s
      = (s' - s) * (b2rho x * (b2pt x - (s + s')/2) - 2*a) := by
  unfold b2dg
  rw [b2f_right_eq x hs, b2f_right_eq x hs']
  ring

/-- The dynamic objective is maximized at `b2sdyn` on `[0,1]`
(for `a ≥ 0`). -/
theorem b2dg_isMaxOn (x : ℝ) {a : ℝ} (ha : a ∈ Sanctions.I) :
    IsMaxOn (fun s => b2dg x a s) (Set.Icc (0:ℝ) 1) (b2sdyn x a) := by
  have hLpos0 : (0:ℝ) < b2lam x := by have := b2lam_lb x; linarith
  have hRpos0 : (0:ℝ) < b2rho x := by have := b2rho_lb x; linarith
  rw [isMaxOn_iff]
  intro s hs
  -- key vertex identity: `(2a/λ)·λ = 2a`
  have hvid : (2*a/b2lam x) * b2lam x = 2*a :=
    div_mul_cancel₀ _ (ne_of_gt hLpos0)
  rcases le_total s (b2sdyn x a) with hcase | hcase
  · -- climb from `s` up to the response: all left branch
    have hs_pt : s ≤ b2pt x := le_trans hcase (b2sdyn_le_pt x ha.1)
    have hsd_pt : b2sdyn x a ≤ b2pt x := b2sdyn_le_pt x ha.1
    have hD := b2dg_left_chord x a hs_pt hsd_pt
    have hsd_v : b2sdyn x a ≤ b2pt x - 2*a/b2lam x := min_le_right _ _
    have hbr : 0 ≤ b2lam x * (b2pt x - (s + b2sdyn x a)/2) - 2*a := by
      have hmid : (s + b2sdyn x a)/2 ≤ b2pt x - 2*a/b2lam x := by
        have := le_trans hcase hsd_v
        linarith [hsd_v]
      nlinarith [hvid, mul_le_mul_of_nonneg_left hmid hLpos0.le]
    nlinarith [hD, mul_nonneg (sub_nonneg.2 hcase) hbr]
  · -- descend from `s` down to the response
    rcases le_total s (b2pt x) with hs_pt | hs_pt
    · -- both left of the kink
      have hsd_pt : b2sdyn x a ≤ b2pt x := b2sdyn_le_pt x ha.1
      have hD := b2dg_left_chord x a hs_pt hsd_pt
      rcases le_total 1 (b2pt x - 2*a/b2lam x) with hclip | hclip
      · -- response clipped at 1; `s ≤ 1 = response` forces equality
        have h1 : b2sdyn x a = 1 := min_eq_left hclip
        have hse : s = b2sdyn x a := le_antisymm (by rw [h1]; exact hs.2) hcase
        rw [hse]
      · -- response = unclipped vertex; mid right of vertex ⇒ bracket ≤ 0
        have hv : b2sdyn x a = b2pt x - 2*a/b2lam x := min_eq_right hclip
        have hbr : b2lam x * (b2pt x - (s + b2sdyn x a)/2) - 2*a ≤ 0 := by
          have hmid : b2pt x - 2*a/b2lam x ≤ (s + b2sdyn x a)/2 := by
            rw [hv] at hcase ⊢; linarith
          nlinarith [hvid, mul_le_mul_of_nonneg_left hmid hLpos0.le]
        nlinarith [hD, mul_nonneg
          (neg_nonneg.2 (by linarith : b2sdyn x a - s ≤ 0))
          (neg_nonneg.2 hbr)]
    · -- `s` beyond the kink: descend to the kink, then to the response
      have hsd_pt : b2sdyn x a ≤ b2pt x := b2sdyn_le_pt x ha.1
      have step1 : b2dg x a s ≤ b2dg x a (b2pt x) := by
        have hD := b2dg_right_chord x a hs_pt (le_refl (b2pt x))
        have hbr : b2rho x * (b2pt x - (b2pt x + s)/2) - 2*a ≤ 0 := by
          nlinarith [mul_nonneg hRpos0.le
            (by linarith : (0:ℝ) ≤ (b2pt x + s)/2 - b2pt x), ha.1]
        nlinarith [hD, mul_nonneg (sub_nonneg.2 hs_pt) (neg_nonneg.2 hbr)]
      have step2 : b2dg x a (b2pt x) ≤ b2dg x a (b2sdyn x a) := by
        have hD := b2dg_left_chord x a (le_refl (b2pt x)) hsd_pt
        rcases le_total 1 (b2pt x - 2*a/b2lam x) with hclip | hclip
        · -- response clipped at 1 while `σ ≤ p̃ ≤ s ≤ 1`: degenerate
          have h1 : b2sdyn x a = 1 := min_eq_left hclip
          have hpt1 : b2pt x = b2sdyn x a := by
            rw [h1] at hsd_pt ⊢
            exact le_antisymm (by linarith [hs.2, hs_pt]) hsd_pt
          rw [hpt1]
        · -- response = unclipped vertex ≤ kink: bracket ≤ 0 on the chord
          have hv : b2sdyn x a = b2pt x - 2*a/b2lam x := min_eq_right hclip
          have hbr : b2lam x * (b2pt x - (b2pt x + b2sdyn x a)/2) - 2*a ≤ 0 := by
            have hmid : b2pt x - 2*a/b2lam x ≤ (b2pt x + b2sdyn x a)/2 := by
              rw [hv]
              have hvpt : b2pt x - 2*a/b2lam x ≤ b2pt x := by
                rw [← hv]; exact hsd_pt
              linarith
            nlinarith [hvid, mul_le_mul_of_nonneg_left hmid hLpos0.le]
          nlinarith [hD, mul_nonneg
            (neg_nonneg.2 (sub_nonpos.2 hsd_pt)) (neg_nonneg.2 hbr)]
      exact le_trans step1 step2

/-! ## 13. Shift-pinned carriers

`carrier_S` = vertical shifts of the interior-peaked `base` (members
NON-monotone: the Sender continuation value peaks at the basin
threshold and declines beyond — hardline consolidation backfires);
`carrier_T` = vertical shifts of the affine slope-5 hawk value. Both
are preimages of the degenerate gain ball `valLipGainBall M 0 0 0`
(zero Lipschitz constant = constant difference), so closedness is
inherited and every member is `base + t` / `5y + t` exactly. -/

/-- The Sender carrier's pinned shape as a BCF. -/
def b2baseBCF : Val :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => b2base y.val)
      (by unfold b2base; fun_prop))

@[simp] theorem b2baseBCF_apply (y : ↥(Sanctions.S : Set ℝ)) :
    b2baseBCF y = b2base y.val := rfl

/-- Sender carrier: vertical shifts of `base`, shift radius 8. -/
def b2CarrierS : Set Val := {V : Val | V - b2baseBCF ∈ valLipGainBall 8 0 0 0}

/-- Target carrier: vertical shifts of the affine slope-5 value,
shift radius 8. -/
def b2CarrierT : Set Val := {V : Val | V - affineBCF 5 ∈ valLipGainBall 8 0 0 0}

theorem b2CarrierS_isClosed : IsClosed b2CarrierS :=
  (valLipGainBall_isClosed _ _ _ _).preimage
    (continuous_id.sub continuous_const)

theorem b2CarrierT_isClosed : IsClosed b2CarrierT :=
  (valLipGainBall_isClosed _ _ _ _).preimage
    (continuous_id.sub continuous_const)

theorem b2_zero_shift_mem {W₀ : Val} : W₀ - W₀ ∈ valLipGainBall 8 0 0 0 := by
  rw [sub_self]
  refine ⟨by simp, ?_, ?_⟩
  · intro y₁ y₂
    simp
  · intro y₁ y₂ _ _ _
    simp

theorem b2CarrierS_nonempty : b2CarrierS.Nonempty :=
  ⟨b2baseBCF, b2_zero_shift_mem⟩

theorem b2CarrierT_nonempty : b2CarrierT.Nonempty :=
  ⟨affineBCF 5, b2_zero_shift_mem⟩

/-- **Shift extraction (Sender).** Every Sender-carrier member is
exactly `base + t` on the state space. -/
theorem b2CarrierS_apply {W : Val} (hW : W ∈ b2CarrierS)
    {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    W (Sanctions.clipS' z)
      = b2base z + (W (Sanctions.clipS' 0) - b2base 0) := by
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hd := gainBall_clip_diff (le_refl (0:ℝ)) hW hz h0
  simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
    b2baseBCF_apply, zero_mul] at hd
  have hz' : (Sanctions.clipS' z).val = z := clipS'_val_of_mem hz
  have h0' : (Sanctions.clipS' 0).val = 0 := clipS'_val_of_mem h0
  rw [hz', h0'] at hd
  linarith [hd]

/-- **Shift extraction (Target).** Every Target-carrier member is
exactly `5y + t` on the state space. -/
theorem b2CarrierT_apply {V : Val} (hV : V ∈ b2CarrierT)
    {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    V (Sanctions.clipS' z) = 5*z + V (Sanctions.clipS' 0) := by
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hd := gainBall_clip_diff (le_refl (0:ℝ)) hV hz h0
  simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
    affineBCF_apply, zero_mul] at hd
  have hz' : (Sanctions.clipS' z).val = z := clipS'_val_of_mem hz
  have h0' : (Sanctions.clipS' 0).val = 0 := clipS'_val_of_mem h0
  rw [hz', h0'] at hd
  linarith [hd]

/-! ## 14. The dynamic objective at carrier members; σ_dyn pinned;
argmax uniqueness on both sides -/

/-- At any Sender-carrier member the dynamic objective on `I` is
exactly the pure two-piece objective plus half the member's shift:
the reverse-engineered `−(1/2)·base∘F` stage term cancels the
continuation. -/
theorem b2dynObj_eq {W : Val} (hW : W ∈ b2CarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (a : ℝ)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    b2Params.U_S x a s + b2Params.β_S * W (Sanctions.clipS' (b2Params.F x s))
      = b2dg x a s + (W (Sanctions.clipS' 0) - b2base 0)/2 := by
  have hFm : (x + s)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hx.1, hs.1], by nlinarith [hx.2, hs.2]⟩
  rw [b2Params_U_S, b2Params_β_S, b2Params_F, b2CarrierS_apply hW hFm]
  unfold b2U_S b2dg
  ring

/-- Strict concavity of the REAL dynamic objective at carrier members. -/
theorem b2dynObj_strictConcaveOn_real {W : Val} (hW : W ∈ b2CarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (a : ℝ) :
    StrictConcaveOn ℝ (Set.Icc (0:ℝ) 1)
      (fun s => b2Params.U_S x a s
        + b2Params.β_S * W (Sanctions.clipS' (b2Params.F x s))) := by
  refine b2_strictConcaveOn_congr (convex_Icc 0 1) ?_
    (b2dynObj_strictConcaveOn x (-(2*a))
      ((W (Sanctions.clipS' 0) - b2base 0)/2))
  intro s hs
  rw [b2dynObj_eq hW hx a hs]
  unfold b2dg
  ring

/-- **State-local Sender argmax uniqueness on the carrier** (DAU). -/
theorem b2_DAU_on_carrier {W : Val} (hW : W ∈ b2CarrierS) :
    b2Params.DynamicArgmaxUnique W := by
  apply b2Params.dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  exact b2dynObj_strictConcaveOn_real hW hx a

/-- **σ_dyn pinned at the closed-form interior response** — the first
witness whose forward-looking Sender response is a state-varying
interior selector rather than a corner. -/
theorem b2_σ_dyn_eq {W : Val} (hW : W ∈ b2CarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    b2Params.σ_dyn W x a = b2sdyn x a := by
  have hmax : IsMaxOn
      (fun s => b2Params.U_S x a s
        + b2Params.β_S * W (Sanctions.clipS' (b2Params.F x s)))
      (Set.Icc (0:ℝ) 1) (b2sdyn x a) := by
    rw [isMaxOn_iff]
    intro w hw
    rw [b2dynObj_eq hW hx a hw, b2dynObj_eq hW hx a (b2sdyn_mem x ha)]
    have hd := isMaxOn_iff.mp (b2dg_isMaxOn x ha) w hw
    linarith
  exact isMaxOn_unique_of_strictConcaveOn
    (b2dynObj_strictConcaveOn_real hW hx a)
    (b2Params.σ_dyn_mem W x a) (b2sdyn_mem x ha)
    (b2Params.σ_dyn_isMaxOn W x a) hmax

/-- **Leader integrand in closed form**: the sanction response enters
with coefficient `+1/2`, compliance costs `1/50`, and the Target
carrier shift rides along with weight `9/10`. -/
theorem b2_joint_T_integrand_eq {V : Val} (hV : V ∈ b2CarrierT)
    {W : Val} (hW : W ∈ b2CarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    b2Params.joint_T_integrand V W x a
      = 5*x + (1/2) * b2sdyn x a - (1/2) * b2p x - a/50
        + (9/10) * V (Sanctions.clipS' 0) := by
  rw [show b2Params.joint_T_integrand V W x a
      = b2Params.U_T x a (b2Params.σ_dyn W x a)
        + b2Params.β_T * V (Sanctions.clipS' (b2Params.F x (b2Params.σ_dyn W x a)))
    from rfl]
  rw [b2_σ_dyn_eq hW hx ha]
  have hsd := b2sdyn_mem x ha
  have hFm : (x + b2sdyn x a)/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by nlinarith [hx.1, hsd.1], by nlinarith [hx.2, hsd.2]⟩
  rw [b2Params_U_T, b2Params_β_T, b2Params_F, b2CarrierT_apply hV hFm]
  unfold b2U_T
  ring

/-- **Leader argmax uniqueness on the carriers** (TAU): the integrand
strictly decreases in compliance (slope at most `−1/50`). -/
theorem b2_TAU_on_carriers {V W : Val}
    (hV : V ∈ b2CarrierT) (hW : W ∈ b2CarrierS) :
    b2Params.TargetArgmaxUnique V W := by
  apply WitnessKit.targetArgmaxUnique_of_strictAntiOn
  intro x hx b₁ hb₁ b₂ hb₂ hb
  show b2Params.joint_T_integrand V W x b₂
      < b2Params.joint_T_integrand V W x b₁
  rw [b2_joint_T_integrand_eq hV hW hx hb₁,
      b2_joint_T_integrand_eq hV hW hx hb₂]
  have hanti := b2sdyn_anti x hb.le
  linarith

/-- **Full defiance is the leader argmax** at every physical state. -/
theorem b2_zero_isMaxOn_joint {V W : Val}
    (hV : V ∈ b2CarrierT) (hW : W ∈ b2CarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    IsMaxOn (fun a => b2Params.joint_T_integrand V W x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [b2_joint_T_integrand_eq hV hW hx ha,
      b2_joint_T_integrand_eq hV hW hx
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)]
  have hanti := b2sdyn_anti x ha.1
  linarith [ha.1]

/-! ## 15. The asymmetric value class and the derived leader policy -/

/-- **The `ValueClass2` at the B2 witness**: a NON-monotone Sender
carrier (vertical shifts of the interior-peaked `base`) and an affine
Target carrier, with state-local argmax uniqueness on both sides. -/
def b2Class : b2Params.ValueClass2 where
  carrier_T := b2CarrierT
  carrier_S := b2CarrierS
  isClosed_T := b2CarrierT_isClosed
  isClosed_S := b2CarrierS_isClosed
  nonempty_T := b2CarrierT_nonempty
  nonempty_S := b2CarrierS_nonempty
  sender_unique_on := fun _ hW => (b2_DAU_on_carrier hW).toOnI
  target_unique_on := fun _ hV _ hW => b2_TAU_on_carriers hV hW

/-- **The derived leader policy is full defiance: `α_on ≡ 0`** (Rule 1:
the derived argmax of the joint dynamic objective, pinned by
state-local uniqueness). -/
theorem b2_α_on_eq_zero (V : b2Class.CarrierT) (W : b2Class.CarrierS) :
    b2Class.α_on V W = fun _ => (0:ℝ) := by
  exact WitnessKit.α_on_eq_zero_of_zero_isMaxOn V W fun y =>
    b2_zero_isMaxOn_joint V.property W.property y.property

/-! ## 16. Bellman images, exact invariance, decoupled Schur rows

The reverse-engineering pays off here: at `α_on ≡ 0` the Sender
Bellman image of `base + t` is EXACTLY `base + t/2`, and at
`σ_dyn(·, 0) = p(·)` the Target image of `5y + t` is EXACTLY
`5y + (9/10)t` — invariance and both operator rows are pure algebra. -/

theorem b2sdyn_zero (x : ℝ) : b2sdyn x 0 = b2p x := by
  unfold b2sdyn b2p
  rw [mul_zero, zero_div, sub_zero]

/-- Every slice is dominated by its state's `base` value on `[0,1]`
(the compensator's job). -/
theorem b2f_le_base (x : ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    b2f s x ≤ b2base x := by
  rcases le_total s (b2pt x) with h | h
  · rw [b2f_left_eq x h]
    have hm : max (b2pt x - 1) 0 ≤ b2pt x - s :=
      max_le (by linarith [hs.2]) (by linarith)
    have h0m : (0:ℝ) ≤ max (b2pt x - 1) 0 := le_max_right _ _
    have hsq : (max (b2pt x - 1) 0)^2 ≤ (b2pt x - s)^2 := by
      nlinarith [hm, h0m]
    have hL : (0:ℝ) ≤ b2lam x / 2 := by linarith [b2lam_lb x]
    unfold b2comp
    nlinarith [mul_le_mul_of_nonneg_left hsq hL]
  · rw [b2f_right_eq x h]
    have hpt1 : b2pt x ≤ 1 := le_trans h hs.2
    have hc : max (b2pt x - 1) 0 = 0 := max_eq_right (by linarith)
    unfold b2comp
    rw [hc]
    nlinarith [b2rho_lb x, sq_nonneg (s - b2pt x)]

/-- The dominance is attained at the realized peak `p(x)`. -/
theorem b2f_attains (x : ℝ) : b2f (b2p x) x = b2base x := by
  rcases le_total (b2pt x) 1 with h1 | h1
  · have hp : b2p x = b2pt x := min_eq_right h1
    rw [hp, b2f_left_eq x (le_refl _)]
    unfold b2comp
    rw [max_eq_right (by linarith : b2pt x - 1 ≤ 0)]
    ring
  · have hp : b2p x = 1 := min_eq_left h1
    rw [hp, b2f_left_eq x h1]
    unfold b2comp
    rw [max_eq_left (by linarith : (0:ℝ) ≤ b2pt x - 1)]
    ring

theorem b2p_mem (x : ℝ) : b2p x ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_min zero_le_one (by linarith [b2pt_lb x]), min_le_left _ _⟩

/-- **Target Bellman image in closed form.** -/
theorem b2_jointTarget_image (V : b2Class.CarrierT) (W : b2Class.CarrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    b2Params.jointTarget_BCF_on_S V.val W.val
      (b2Class.sender_unique_on W.val W.property) y
      = 5*y.val + 9/10 * V.val (Sanctions.clipS' 0) := by
  have h0I : (0:ℝ) ∈ Sanctions.I := ⟨le_refl 0, by norm_num⟩
  rw [WitnessKit.jointTarget_image_of_isMaxOn V.val W.val
        (b2Class.sender_unique_on W.val W.property) y h0I
        (b2_zero_isMaxOn_joint V.property W.property y.property),
      b2_joint_T_integrand_eq V.property W.property y.property h0I,
      b2sdyn_zero]
  ring

/-- **Sender Bellman image in closed form** at the defiance policy:
the sSup collapses at the interior peak `p(y)` — the first witness
whose Bellman sup is attained at a state-varying interior point. -/
theorem b2_bellmanS_image {W : Val} (hW : W ∈ b2CarrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    b2Params.bellmanS_BCF (fun _ => 0) continuous_const W y
      = b2base y.val + (W (Sanctions.clipS' 0) - b2base 0)/2 := by
  have hpI : b2p y.val ∈ Sanctions.I := b2p_mem y.val
  have hmax : IsMaxOn
      (fun s => b2Params.U_S y.val 0 s
        + b2Params.β_S * W (Sanctions.clipS' (b2Params.F y.val s)))
      Sanctions.I (b2p y.val) := by
    rw [isMaxOn_iff]
    intro s hs
    rw [b2dynObj_eq hW y.property 0 hs, b2dynObj_eq hW y.property 0 hpI]
    unfold b2dg
    have h1 := b2f_le_base y.val hs
    have h2 := b2f_attains y.val
    nlinarith [h1, h2]
  rw [WitnessKit.bellmanS_image_of_isMaxOn (α := fun _ => (0:ℝ))
        continuous_const W y hpI hmax]
  show b2Params.U_S y.val 0 (b2p y.val)
      + b2Params.β_S * W (Sanctions.clipS' (b2Params.F y.val (b2p y.val)))
      = _
  rw [b2dynObj_eq hW y.property 0 hpI]
  unfold b2dg
  rw [b2f_attains y.val]
  ring

/-- Constant-difference membership helper for the shift carriers. -/
theorem b2_shift_const_mem {D : Val} {c : ℝ} (hc : |c| ≤ 8)
    (hD : ∀ y, D y = c) : D ∈ valLipGainBall 8 0 0 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ) ≤ 8)]
    intro y
    rw [hD y, Real.norm_eq_abs]
    exact hc
  · intro y₁ y₂
    rw [hD y₁, hD y₂]
    simp
  · intro y₁ y₂ _ _ _
    rw [hD y₁, hD y₂]
    simp

/-- Pointwise bound for a carrier shift read at any state. -/
theorem b2_shift_abs_le {V W₀ : Val} (h : V - W₀ ∈ valLipGainBall 8 0 0 0)
    (y : ↥(Sanctions.S : Set ℝ)) : |V y - W₀ y| ≤ 8 := by
  have h1 := BoundedContinuousFunction.norm_coe_le_norm (V - W₀) y
  simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
    Real.norm_eq_abs] at h1
  exact le_trans h1 h.1

/-- **Exact carrier invariance** — the joint Bellman pair maps the
shift carriers into themselves by construction (shifts contract with
factors `9/10` and `1/2`). -/
theorem b2Class_IsInvariant : b2Class.IsInvariant := by
  intro V W
  have h0S : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
  constructor
  · -- Target leg
    show b2Class.jointTarget_BCF_on V W - affineBCF 5 ∈ valLipGainBall 8 0 0 0
    have hb : |V.val (Sanctions.clipS' 0)| ≤ 8 := by
      have h1 := b2_shift_abs_le V.property (Sanctions.clipS' 0)
      rw [affineBCF_apply, clipS'_val_of_mem h0S, mul_zero, sub_zero] at h1
      exact h1
    refine b2_shift_const_mem (c := 9/10 * V.val (Sanctions.clipS' 0)) ?_ ?_
    · rw [abs_mul, show |(9:ℝ)/10| = 9/10 by norm_num]
      nlinarith [hb, abs_nonneg (V.val (Sanctions.clipS' 0))]
    · intro y
      simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
        affineBCF_apply]
      rw [show b2Class.jointTarget_BCF_on V W y
          = b2Params.jointTarget_BCF_on_S V.val W.val
              (b2Class.sender_unique_on W.val W.property) y from rfl,
          b2_jointTarget_image V W y]
      ring
  · -- Sender leg
    show b2Class.jointSender_BCF_on V W - b2baseBCF ∈ valLipGainBall 8 0 0 0
    have hop : b2Class.jointSender_BCF_on V W
        = b2Params.bellmanS_BCF (fun _ => (0:ℝ)) continuous_const W.val := by
      show b2Params.bellmanS_BCF (b2Class.α_on V W)
          (b2Class.α_on_continuous V W) W.val = _
      exact WitnessKit.bellmanS_BCF_congr_α (b2_α_on_eq_zero V W) _ continuous_const W.val
    have hb : |W.val (Sanctions.clipS' 0) - b2base 0| ≤ 8 := by
      have h1 := b2_shift_abs_le W.property (Sanctions.clipS' 0)
      rw [b2baseBCF_apply, clipS'_val_of_mem h0S] at h1
      exact h1
    rw [hop]
    refine b2_shift_const_mem
      (c := (W.val (Sanctions.clipS' 0) - b2base 0)/2) ?_ ?_
    · rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
      linarith [hb]
    · intro y
      simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
        b2baseBCF_apply]
      rw [b2_bellmanS_image W.property y]
      ring

/-- **Target-row bound**: `β_T = 9/10`, cross coefficient `L_TS = 0`. -/
theorem b2Class_hT_T_op (h_inv : b2Class.IsInvariant)
    (V V' : b2Class.CarrierT) (W W' : b2Class.CarrierS) :
    dist (b2Class.jointTargetOp_sub h_inv (V, W))
          (b2Class.jointTargetOp_sub h_inv (V', W'))
      ≤ (9/10 : ℝ) * dist V V' + 0 * dist W W' := by
  exact WitnessKit.jointTargetOp_sub_dist_le_of_image h_inv
    (g := fun y => 5 * y) (φ := fun _ => 0)
    (fun V W y => b2_jointTarget_image V W y) V V' W W'

/-- **Sender-row bound**: `β_S = 1/2`, cross coefficient `L_ST = 0`
(the derived leader policy is the constant `α_on ≡ 0` for every
carrier pair). -/
theorem b2Class_hT_S_op (h_inv : b2Class.IsInvariant)
    (V V' : b2Class.CarrierT) (W W' : b2Class.CarrierS) :
    dist (b2Class.jointSenderOp_sub h_inv (V, W))
          (b2Class.jointSenderOp_sub h_inv (V', W'))
      ≤ 0 * dist V V' + (1/2 : ℝ) * dist W W' := by
  exact WitnessKit.jointSenderOp_sub_dist_le_of_defiance h_inv
    b2_α_on_eq_zero V V' W W'

/-! ## 17. Vertex bounds for the myopic leg -/

theorem b2clip_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : b2clip x = x := by
  unfold b2clip
  rw [max_eq_left hx.1, min_eq_left hx.2]

theorem b2pt_ge_self {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : x ≤ b2pt x := by
  have hc := b2clip_of_mem hx
  unfold b2pt
  rw [hc]
  rcases le_total x (5/8) with h | h
  · rw [max_eq_right (by linarith)]; linarith
  · rw [max_eq_left (by linarith)]; linarith

/-- Generic division lower bound used for the vertex-drop rate. -/
theorem b2_div_lb {d c : ℝ} (hd : 0 ≤ d) (hc0 : 0 < c) (hc : c ≤ 41/2) :
    (2/41)*d ≤ d/c := by
  have hdm : (d/c)*c = d := div_mul_cancel₀ _ (ne_of_gt hc0)
  have hd0 : 0 ≤ d/c := div_nonneg hd hc0.le
  nlinarith [mul_le_mul_of_nonneg_left hc hd0]

/-- **Vertex drop rate**: raising compliance from `a'` to `a` moves the
static response down by at least `(4/41)·(a − a')`. -/
theorem b2vertex_diff (x : ℝ) {a a' : ℝ} (h : a' ≤ a) :
    (4/41)*(a - a') ≤ b2vertex x a' - b2vertex x a := by
  have hee : b2e x a ≤ b2e x a' := by
    rw [b2e_def, b2e_def]; linarith
  have hesum : (min (b2e x a') 0 - min (b2e x a) 0)
      + (max (b2e x a') 0 - max (b2e x a) 0) = 2*(a - a') := by
    have h2 := min_add_max (b2e x a') (0:ℝ)
    have h1 := min_add_max (b2e x a) (0:ℝ)
    have he : b2e x a' - b2e x a = 2*(a - a') := by
      rw [b2e_def, b2e_def]; ring
    linarith
  have hdmin : 0 ≤ min (b2e x a') 0 - min (b2e x a) 0 :=
    sub_nonneg.2 (min_le_min hee (le_refl 0))
  have hdmax : 0 ≤ max (b2e x a') 0 - max (b2e x a) 0 :=
    sub_nonneg.2 (max_le_max hee (le_refl 0))
  have hb1 := b2_div_lb hdmin (b2lam_half_pos x)
    (by linarith [b2lam_ub x] : b2lam x - 1/2 ≤ 41/2)
  have hb2 := b2_div_lb hdmax (b2rho_half_pos x)
    (by linarith [b2rho_ub x] : b2rho x - 1/2 ≤ 41/2)
  have key : b2vertex x a' - b2vertex x a
      = (min (b2e x a') 0 - min (b2e x a) 0)/(b2lam x - 1/2)
        + (max (b2e x a') 0 - max (b2e x a) 0)/(b2rho x - 1/2) := by
    unfold b2vertex
    ring
  linarith [key ▸ le_refl (b2vertex x a' - b2vertex x a), hb1, hb2, hesum,
    key.ge, key.le]

/-- The unclipped vertex never falls below `3/16` on the physical
domain — the lower clip is always inactive. -/
theorem b2vertex_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    {a : ℝ} (ha : a ∈ Sanctions.I) : 0 ≤ b2vertex x a := by
  rcases le_total (b2e x a) 0 with he | he
  · rw [b2vertex_of_nonpos x a he]
    have hLpos := b2lam_half_pos x
    have hel : -(33/16) ≤ b2e x a := by
      rw [b2e_def]
      have := b2pt_lb x
      linarith [hx.1, ha.2]
    have hd0 : b2e x a / (b2lam x - 1/2) ≤ 0 := by
      have h0 : 0 ≤ -b2e x a / (b2lam x - 1/2) :=
        div_nonneg (by linarith) hLpos.le
      rw [neg_div] at h0
      linarith
    have hdm : (b2e x a / (b2lam x - 1/2)) * (b2lam x - 1/2) = b2e x a :=
      div_mul_cancel₀ _ (ne_of_gt hLpos)
    have hkey : 0 ≤ (-(b2e x a / (b2lam x - 1/2))) * (b2lam x - 1/2 - 3) :=
      mul_nonneg (neg_nonneg.2 hd0) (by linarith [b2lam_lb x])
    have h3d : 3 * (b2e x a / (b2lam x - 1/2)) ≥ b2e x a := by
      nlinarith [hkey, hdm]
    linarith [b2pt_lb x, h3d, hel]
  · rw [b2vertex_of_nonneg x a he]
    have : 0 ≤ b2e x a / (b2rho x - 1/2) :=
      div_nonneg he (b2rho_half_pos x).le
    linarith [b2pt_lb x]

/-- At full compliance the vertex sits at most at `15/16` — the myopic
response is never clipped at the top. -/
theorem b2vertex_at_one_le {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    b2vertex x 1 ≤ 15/16 := by
  have he : b2e x 1 ≤ 0 := by
    rw [b2e_def]
    have := b2pt_ub x
    linarith [hx.2]
  rw [b2vertex_of_nonpos x 1 he]
  have hclip := b2clip_of_mem hx
  have hLpos := b2lam_half_pos x
  have hd0 : b2e x 1 / (b2lam x - 1/2) ≤ 0 := by
    have h0 : 0 ≤ -b2e x 1 / (b2lam x - 1/2) :=
      div_nonneg (by linarith) hLpos.le
    rw [neg_div] at h0
    linarith
  rcases le_total x (5/8) with h58 | h58
  · have hpt_eq : b2pt x = 7/8 := by
      unfold b2pt
      rw [hclip, max_eq_right (by linarith)]
      ring
    rw [hpt_eq]
    linarith
  · have hk : max (b2clip x - 1/2) 0 = x - 1/2 := by
      rw [hclip]; exact max_eq_left (by linarith)
    have hm : max (b2clip x - 5/8) 0 = x - 5/8 := by
      rw [hclip]; exact max_eq_left (by linarith)
    have hpt_eq : b2pt x = 7/8 + (4/3)*(x - 5/8) := by
      unfold b2pt; rw [hm]
    have hlam_eq : b2lam x - 1/2 = 4 - x := by
      unfold b2lam; rw [hk]; ring
    have hpos : (0:ℝ) < 4 - x := by linarith [hx.2]
    have hpoly : b2e x 1 ≤ (15/16 - b2pt x) * (4 - x) := by
      rw [b2e_def, hpt_eq]
      nlinarith [mul_nonneg (by linarith [hx.2] : (0:ℝ) ≤ 1 - x)
        (by linarith [hx.2] : (0:ℝ) ≤ 291 - 64*x)]
    have hdm : (b2e x 1 / (b2lam x - 1/2)) * (4 - x) = b2e x 1 := by
      have := div_mul_cancel₀ (b2e x 1) (ne_of_gt hLpos)
      rw [hlam_eq] at this ⊢
      exact this
    nlinarith [hdm, hpoly, hpos]

/-- On the basin the full-compliance response sits below the state:
the myopic Sender never sanctions above the inherited hardline level. -/
theorem b2vertex_le_basin {x : ℝ} (hx : x ∈ Set.Icc (1/2:ℝ) 1) :
    b2vertex x 1 ≤ x := by
  have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have he : b2e x 1 ≤ 0 := by
    rw [b2e_def]
    have := b2pt_ub x
    linarith [hx.2]
  rw [b2vertex_of_nonpos x 1 he]
  have hclip := b2clip_of_mem hx'
  have hLpos := b2lam_half_pos x
  have hk : max (b2clip x - 1/2) 0 = x - 1/2 := by
    rw [hclip]; exact max_eq_left (by linarith [hx.1])
  have hlam_eq : b2lam x - 1/2 = 4 - x := by
    unfold b2lam; rw [hk]; ring
  have hpos : (0:ℝ) < 4 - x := by linarith [hx.2]
  have hdm : (b2e x 1 / (b2lam x - 1/2)) * (4 - x) = b2e x 1 := by
    have := div_mul_cancel₀ (b2e x 1) (ne_of_gt hLpos)
    rw [hlam_eq] at this ⊢
    exact this
  rcases le_total x (5/8) with h58 | h58
  · have hpt_eq : b2pt x = 7/8 := by
      unfold b2pt
      rw [hclip, max_eq_right (by linarith)]
      ring
    have hpoly : b2e x 1 ≤ (x - b2pt x) * (4 - x) := by
      rw [b2e_def, hpt_eq]
      nlinarith [mul_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x - 1/2)
        (by linarith : (0:ℝ) ≤ 5/8 - x)]
    rw [hpt_eq] at hpoly ⊢
    nlinarith [hdm, hpoly, hpos]
  · have hm : max (b2clip x - 5/8) 0 = x - 5/8 := by
      rw [hclip]; exact max_eq_left (by linarith)
    have hpt_eq : b2pt x = 7/8 + (4/3)*(x - 5/8) := by
      unfold b2pt; rw [hm]
    have hpoly : b2e x 1 ≤ (x - b2pt x) * (4 - x) := by
      rw [b2e_def, hpt_eq]
      nlinarith [sq_nonneg (x - 1), hx.2]
    nlinarith [hdm, hpoly, hpos]

/-! ## 18. The myopic comparator: full compliance, placated response -/

/-- **The myopic feedback equilibrium at the B2 witness**: the myopic
Target corners at full compliance (the placation channel drops the
sanction by at least `4/41` per unit of compliance while a unit costs
only `1/50`; when the response is clipped at the top, the
full-compliance response is uniformly `1/16` below the clip). -/
def b2Myopic : b2Params.MyopicFeedbackEquilibrium where
  α := fun _ => 1
  α_mem := fun _ _ => ⟨zero_le_one, le_refl 1⟩
  α_opt := by
    intro x hx
    rw [isMaxOn_iff]
    intro a ha
    show b2U_T x a (b2σ x a) ≤ b2U_T x 1 (b2σ x 1)
    have hobj : ∀ b s : ℝ, b2U_T x b s
        = 5*x - (9/4)*x - (1/2)*(b2p x) - b/50 - (7/4)*s := by
      intro b s
      unfold b2U_T
      ring
    rw [hobj a (b2σ x a), hobj 1 (b2σ x 1)]
    have h1I : (1:ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_refl 1⟩
    have hva := b2vertex_nonneg hx ha
    have hv1 := b2vertex_nonneg hx h1I
    have hσa : b2σ x a = min 1 (b2vertex x a) := by
      unfold b2σ; rw [max_eq_right hva]
    have hσ1 : b2σ x 1 = b2vertex x 1 := by
      unfold b2σ
      rw [max_eq_right hv1,
        min_eq_right (le_trans (b2vertex_at_one_le hx) (by norm_num))]
    rw [hσa, hσ1]
    rcases le_total (b2vertex x a) 1 with hc | hc
    · rw [min_eq_right hc]
      have hd := b2vertex_diff x ha.2
      linarith [ha.2]
    · rw [min_eq_left hc]
      have h15 := b2vertex_at_one_le hx
      linarith [ha.1]

/-- **Myopic ceiling on the basin**: the myopic realized sanction never
exceeds `max(x, s̄)`. -/
theorem b2_hMyoCeiling :
    ∀ x ∈ Set.Icc (max (1/2:ℝ) (1/2)) 1,
      b2Params.σ x (b2Myopic.α x) ≤ max x (1/2:ℝ) := by
  intro x hx
  rw [max_self] at hx
  show b2σ x 1 ≤ max x (1/2:ℝ)
  have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have h1I : (1:ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_refl 1⟩
  have hv1 := b2vertex_nonneg hx' h1I
  calc b2σ x 1 ≤ max 0 (b2vertex x 1) := min_le_right _ _
  _ = b2vertex x 1 := max_eq_right hv1
  _ ≤ x := b2vertex_le_basin hx
  _ ≤ max x (1/2:ℝ) := le_max_left _ _

/-! ## 19. Stage fields at the derived defiance policy -/

/-- Carrier-local Sender Lipschitz (`KS = 2`): shift members inherit
`base`'s exact Lipschitz constant. -/
theorem b2_hV_S_lip : ∀ W ∈ b2Class.carrier_S, ValueLipschitzWith W 2 := by
  intro W hW y₁ y₂
  have h0 : (W - b2baseBCF) y₂ - (W - b2baseBCF) y₁ = 0 := by
    have h := hW.2.1 y₁ y₂
    rw [zero_mul] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
    b2baseBCF_apply] at h0
  have heq : W y₂ - W y₁ = b2base y₂.val - b2base y₁.val := by linarith
  rw [heq]
  have h1 := y₁.property
  have h2 := y₂.property
  have h1' : y₁.val ∈ Set.Icc (0:ℝ) 1 := h1
  have h2' : y₂.val ∈ Set.Icc (0:ℝ) 1 := h2
  rw [Subtype.dist_eq, Real.dist_eq]
  unfold b2base
  rw [show (8 - 2*(y₂.val - 1/2)^2) - (8 - 2*(y₁.val - 1/2)^2)
      = -2*(y₂.val - y₁.val)*(y₂.val + y₁.val - 1) from by ring]
  rw [abs_mul, abs_mul, show |(-2:ℝ)| = 2 by norm_num]
  have hm : |y₂.val + y₁.val - 1| ≤ 1 :=
    abs_le.2 ⟨by linarith [h1'.1, h2'.1], by linarith [h1'.2, h2'.2]⟩
  have hd : |y₂.val - y₁.val| = |y₁.val - y₂.val| := abs_sub_comm _ _
  nlinarith [abs_nonneg (y₂.val - y₁.val), hm, hd.ge, hd.le]

/-- Carrier-local Target minimum upward slope (`gT = 5`, exact). -/
theorem b2_hV_T_gain :
    ∀ V ∈ b2Class.carrier_T,
      LowerSlopeOnValueOn V (Set.Icc (1/2:ℝ) 1) 5 := by
  intro V hV y₁ y₂ _ _ hle
  have h0 : (V - affineBCF 5) y₂ - (V - affineBCF 5) y₁ = 0 := by
    have h := hV.2.1 y₁ y₂
    rw [zero_mul] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
    affineBCF_apply] at h0
  have hvle : y₁.val ≤ y₂.val := Subtype.coe_le_coe.2 hle
  rw [Subtype.dist_eq, Real.dist_eq,
    abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
  linarith

/-- Stage Target loss (`cT = 7/4`, exact linear slope `−7/4`). -/
theorem b2_h_stage_target_loss
    (V : b2Class.CarrierT) (W : b2Class.CarrierS) :
    ∀ x ∈ Set.Icc (1/2:ℝ) 1,
      LowerLossSlopeOn (fun s => b2Params.U_T x (b2Class.α_on V W x) s)
        (Set.Icc (max x (1/2:ℝ)) 1) (7/4) := by
  intro x _ s₁ _ s₂ _ hle
  simp only [b2_α_on_eq_zero V W, b2Params_U_T, b2U_T]
  linarith [hle]

/-- Stage Sender slope on the floor range (`mS = 3/4`): the chord
bracket `(λ − 1/2)(p̃ − mid) + e(x,0)` stays above `3/4` on the basin
because `mid ≤ x ≤ p̃`. -/
theorem b2_h_stage_sender
    (V : b2Class.CarrierT) (W : b2Class.CarrierS) :
    ∀ x ∈ Set.Icc (1/2:ℝ) 1,
      LowerSlopeOn (fun s => b2Params.U_S x (b2Class.α_on V W x) s)
        (Set.Icc (0:ℝ) (max x (1/2:ℝ))) (3/4) := by
  intro x hx s₁ hs₁ s₂ hs₂ hle
  have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hmax : max x (1/2:ℝ) = x := max_eq_left hx.1
  rw [hmax] at hs₁ hs₂
  have hptx := b2pt_ge_self hx'
  have h1pt : s₁ ≤ b2pt x := le_trans hs₁.2 hptx
  have h2pt : s₂ ≤ b2pt x := le_trans hs₂.2 hptx
  simp only [b2_α_on_eq_zero V W, b2Params_U_S]
  have hD := b2_left_chord x 0 h1pt h2pt
  have hclip := b2clip_of_mem hx'
  have hk : max (b2clip x - 1/2) 0 = x - 1/2 := by
    rw [hclip]; exact max_eq_left (by linarith [hx.1])
  have hlam_eq : b2lam x - 1/2 = 4 - x := by
    unfold b2lam; rw [hk]; ring
  have he0 : b2e x 0 = (x + b2pt x)/2 - 1/2 := by
    rw [b2e_def]; ring
  rcases le_total x (5/8) with h58 | h58
  · have hpt_eq : b2pt x = 7/8 := by
      unfold b2pt
      rw [hclip, max_eq_right (by linarith)]
      ring
    rw [hlam_eq, he0, hpt_eq] at hD
    have hbr : (3:ℝ)/4
        ≤ (4 - x) * (7/8 - (s₁ + s₂)/2) + ((x + 7/8)/2 - 1/2) := by
      nlinarith [mul_nonneg (by linarith [hx.2] : (0:ℝ) ≤ 4 - x)
          (by linarith [hs₁.2, hs₂.2] : (0:ℝ) ≤ x - (s₁ + s₂)/2),
        sq_nonneg (x - 9/16), h58]
    have hmul := mul_le_mul_of_nonneg_left hbr (sub_nonneg.2 hle)
    linarith [hD, hmul]
  · have hm : max (b2clip x - 5/8) 0 = x - 5/8 := by
      rw [hclip]; exact max_eq_left (by linarith)
    have hpt_eq : b2pt x = 7/8 + (4/3)*(x - 5/8) := by
      unfold b2pt; rw [hm]
    rw [hlam_eq, he0, hpt_eq] at hD
    have hbr : (3:ℝ)/4
        ≤ (4 - x) * ((7/8 + (4/3)*(x - 5/8)) - (s₁ + s₂)/2)
          + ((x + (7/8 + (4/3)*(x - 5/8)))/2 - 1/2) := by
      nlinarith [mul_nonneg (by linarith [hx.2] : (0:ℝ) ≤ 4 - x)
          (by linarith [hs₁.2, hs₂.2] : (0:ℝ) ≤ x - (s₁ + s₂)/2),
        mul_nonneg (by linarith : (0:ℝ) ≤ x - 5/8)
          (by linarith [hx.2] : (0:ℝ) ≤ 1 - x),
        h58, hx.2]
    have hmul := mul_le_mul_of_nonneg_left hbr (sub_nonneg.2 hle)
    linarith [hD, hmul]

/-! ## 20. The B2 pair at the certificate family — and the discharger's
first consumption -/

/-- Certificate-typed quasiconcavity (from strict concavity). -/
theorem b2_hQC (V : b2Class.CarrierT) (W : b2Class.CarrierS) :
    ∀ x ∈ Set.Icc (max (1/2:ℝ) (1/2)) 1,
      QuasiconcaveOn ℝ Sanctions.I
        (fun s => b2Params.senderDynObjective W.val x
          (b2Class.α_on V W x) s) := by
  intro x hx
  rw [max_self] at hx
  have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have h := (b2dynObj_strictConcaveOn_real W.property hx'
    (b2Class.α_on V W x)).concaveOn.quasiconcaveOn
  simpa only [AbstractGame.Params.senderDynObjective] using h

/-- Certificate-typed `MonotoneTransferOn` — transported from the pure
slice family (the carrier shift is a constant, the derived policy is
the defiance corner). -/
theorem b2_hMT (V : b2Class.CarrierT) (W : b2Class.CarrierS) :
    Sanctions.IntervalDominanceOrder.MonotoneTransferOn
      Sanctions.I (Set.Icc (max (1/2:ℝ) (1/2)) 1)
      (fun s x => b2Params.senderDynObjective W.val x
        (b2Class.α_on V W x) s) := by
  have hfam : ∀ s ∈ Sanctions.I, ∀ u ∈ Set.Icc (0:ℝ) 1,
      b2Params.senderDynObjective W.val u (b2Class.α_on V W u) s
        = b2f s u + (W.val (Sanctions.clipS' 0) - b2base 0)/2 := by
    intro s hs u hu
    show b2Params.U_S u (b2Class.α_on V W u) s
        + b2Params.β_S * W.val (Sanctions.clipS' (b2Params.F u s)) = _
    rw [show b2Class.α_on V W u = 0 from by rw [b2_α_on_eq_zero V W]]
    rw [b2dynObj_eq W.property hu 0 hs]
    unfold b2dg
    ring
  intro t t' ht ht' htt s' s'' hs' hs'' hss hmono
  rw [max_self] at ht ht'
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have ht'I : t' ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht'.1], ht'.2⟩
  have hmono' : MonotoneOn (fun s => b2f s t) (Set.Icc s' s'') := by
    intro u hu w hw huw
    have hu' : u ∈ Sanctions.I := ⟨le_trans hs'.1 hu.1, le_trans hu.2 hs''.2⟩
    have hw' : w ∈ Sanctions.I := ⟨le_trans hs'.1 hw.1, le_trans hw.2 hs''.2⟩
    have h := hmono hu hw huw
    simp only at h
    rw [hfam u hu' t htI, hfam w hw' t htI] at h
    simpa using h
  have hres := b2f_monotoneTransferOn ht ht' htt hs' hs'' hss hmono'
  constructor
  · have h1 := hres.1
    simp only
    rw [hfam s' hs' t' ht'I, hfam s'' hs'' t' ht'I]
    linarith
  · intro hstrict
    simp only at hstrict
    rw [hfam s' hs' t htI, hfam s'' hs'' t htI] at hstrict
    have h2 := hres.2 (by linarith)
    simp only
    rw [hfam s' hs' t' ht'I, hfam s'' hs'' t' ht'I]
    linarith

/-- **Single crossing fails at the CERTIFICATE family too** — the SC
upcast route to `hIDO_on` is provably unavailable at this economy; the
B2 discharger below is the sole route. -/
theorem b2Cert_not_singleCrossingOn
    (V : b2Class.CarrierT) (W : b2Class.CarrierS) :
    ¬ Sanctions.MilgromShannon.SingleCrossingOn
        Sanctions.I (Set.Icc (max (1/2:ℝ) (1/2)) 1)
        (fun s x => b2Params.senderDynObjective W.val x
          (b2Class.α_on V W x) s) := by
  have hfam : ∀ s ∈ Sanctions.I, ∀ u ∈ Set.Icc (0:ℝ) 1,
      b2Params.senderDynObjective W.val u (b2Class.α_on V W u) s
        = b2f s u + (W.val (Sanctions.clipS' 0) - b2base 0)/2 := by
    intro s hs u hu
    show b2Params.U_S u (b2Class.α_on V W u) s
        + b2Params.β_S * W.val (Sanctions.clipS' (b2Params.F u s)) = _
    rw [show b2Class.α_on V W u = 0 from by rw [b2_α_on_eq_zero V W]]
    rw [b2dynObj_eq W.property hu 0 hs]
    unfold b2dg
    ring
  intro h
  apply b2f_not_singleCrossingOn
  intro s s' t t' hs hs' hss ht ht' htt
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have ht'I : t' ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht'.1], ht'.2⟩
  have hmt : t ∈ Set.Icc (max (1/2:ℝ) (1/2)) 1 := by
    rw [max_self]; exact ht
  have hmt' : t' ∈ Set.Icc (max (1/2:ℝ) (1/2)) 1 := by
    rw [max_self]; exact ht'
  have hc := h hs hs' hss hmt hmt' htt
  constructor
  · intro hprem
    have h1 := hc.1 (by
      simp only
      rw [hfam s hs t htI, hfam s' hs' t htI]
      linarith)
    simp only at h1
    rw [hfam s hs t' ht'I, hfam s' hs' t' ht'I] at h1
    linarith
  · intro hprem
    have h2 := hc.2 (by
      simp only
      rw [hfam s hs t htI, hfam s' hs' t htI]
      linarith)
    simp only at h2
    rw [hfam s hs t' ht'I, hfam s' hs' t' ht'I] at h2
    linarith

/-! ## 21. THE CERTIFICATE — `hIDO_on` filled by the B2 discharger -/

/-- **The first `StandardComplianceLocalCoreCertificate` whose
`hIDO_on` field is discharged through
`hIDO_on_of_quasiconcave_monotoneTransfer`** — the 2026-07-02
user-approved B2 route, consumed here for the first time, at an
economy where the single-crossing upcast is machine-checked
unavailable (`b2Cert_not_singleCrossingOn`). -/
noncomputable def b2Certificate :
    b2Params.StandardComplianceLocalCoreCertificate where
  D := b2Class
  h_inv := b2Class_IsInvariant
  β_T := 9/10
  β_S := 1/2
  L_TS := 0
  L_ST := 0
  hβ_T_nn := by norm_num
  hβ_S_nn := by norm_num
  hL_TS_nn := le_refl 0
  hL_ST_nn := le_refl 0
  hT_T_op := b2Class_hT_T_op b2Class_IsInvariant
  hT_S_op := b2Class_hT_S_op b2Class_IsInvariant
  hsuff_T := by norm_num
  hsuff_S := by norm_num
  xT := 1/2
  xS := 1/2
  sbar := 1/2
  mS := 3/4
  KS := 2
  hxT_mem := ⟨by norm_num, by norm_num⟩
  hxS_mem := ⟨by norm_num, by norm_num⟩
  hsbar_mem := ⟨by norm_num, by norm_num⟩
  d := b2Params.δ
  hF_chord := b2Params.affine_sender_chord_on rfl _ _
  hS_margin := by
    simp only [b2Params_β_S, b2Params_δ]
    norm_num
  hjoint_lt := by rw [max_self]; norm_num
  hV_S_lip_carrier := b2_hV_S_lip
  h_stage_sender_on := b2_h_stage_sender
  hIDO_on := b2Params.hIDO_on_of_quasiconcave_monotoneTransfer
    b2Class b2_hQC b2_hMT
  M := b2Myopic
  hMyoCeiling := b2_hMyoCeiling

/-! ## 22. The three-goals corollary -/

/-- **Unconditional three-goals at the B2 witness.** The forward-looking
equilibrium exists on the carriers (with a NON-monotone Sender
continuation value), and on the basin the myopic realized sanction is
dominated by the forward-looking realized sanction — delivered through
a certificate whose interval-dominance field could NOT have come from
single crossing. -/
theorem b2NonMono_three_goals_dominance :
    ∃ E : b2Params.FeedbackStackelbergEquilibriumTop,
      E.V_T ∈ b2CarrierT ∧ E.V_S ∈ b2CarrierS
      ∧ (∀ x ∈ Set.Icc (max (1/2:ℝ) (1/2)) 1,
           b2Params.σ x (b2Myopic.α x)
             ≤ b2Params.dynamicTopRealizedRule E.V_S E.α x) := by
  -- G3 re-route (2026-08-19): Goal 2 mentions no transition, so it is
  -- taken through the general-`F` chord route rather than the affine
  -- `three_goals_local_uniform_starts`. The statement is unchanged. Round
  -- BG (2026-10-06): the call goes to `goal2_dominance_generalF` itself;
  -- the affine wrapper it used to pass through read neither its `hF` nor
  -- its `0 ≤ g_T` binder and was deleted. The affine law enters only as the
  -- `d = δ` instance of the certificate's Sender chord field (its Target lower
  -- chord at `dlo` was deleted in round BJ1.4).
  obtain ⟨E, hVT, hVS, hG2⟩ :=
    b2Certificate.goal2_dominance_generalF (p := b2Params)
  exact ⟨E, hVT, hVS, hG2⟩

/-! ## Within-carrier uniqueness (Schur route, 2026-07-24) -/

/-- Schur-certificate inhabitant at the B2 witness, via the row-sum ⇒
Schur bridge (decoupled rows: `L_TS·L_ST = 0 < (1/10)·(1/2)`). -/
noncomputable def b2CertificateSchur :
    b2Params.StandardComplianceLocalCoreCertificateSchur :=
  AbstractGame.Params.StandardComplianceLocalCoreCertificateSchur.ofRowSum
    b2Params b2Certificate

/-- **Witness within-carrier uniqueness at B2.** Any two top-selector
feedback Stackelberg equilibria of the B2 economy whose value pairs lie
in the shifted-ball carriers and whose policies coincide with the
carrier selector agree in both value functions and the policy; every
quantitative input of the headline uniqueness theorem is
machine-discharged by `b2Certificate` (decoupled rows, diagonals
`9/10`, `1/2`). -/
theorem b2_unique_in_carrier
    (E E' : b2Params.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ b2CarrierT) (hVS : E.V_S ∈ b2CarrierS)
    (hVT' : E'.V_T ∈ b2CarrierT) (hVS' : E'.V_S ∈ b2CarrierS)
    (hαE : E.α = b2Class.α_on ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩)
    (hαE' : E'.α = b2Class.α_on ⟨E'.V_T, hVT'⟩ ⟨E'.V_S, hVS'⟩) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ E.α = E'.α :=
  b2Certificate.unique_in_carrier (p := b2Params)
    E E' hVT hVS hVT' hVS' hαE hαE'

/-- **Witness within-carrier uniqueness at B2, with no selector hypothesis
(round BH1.1, 2026-10-06).** Sibling of `b2_unique_in_carrier` without `hαE`,
`hαE'`: any two top-selector feedback Stackelberg equilibria of the B2 economy
whose values lie in the shifted-ball carriers share both value functions, and
their policies agree at every feasible state. Every quantitative input is
discharged by `b2Certificate`. The economy runs the affine law (`δ = 1/2`); the
theorem it instantiates is general in `F`. -/
theorem b2_unique_in_carrier_of_mem
    (E E' : b2Params.FeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ b2CarrierT) (hVS : E.V_S ∈ b2CarrierS)
    (hVT' : E'.V_T ∈ b2CarrierT) (hVS' : E'.V_S ∈ b2CarrierS) :
    E.V_T = E'.V_T ∧ E.V_S = E'.V_S ∧ Set.EqOn E.α E'.α Sanctions.S :=
  b2Certificate.unique_in_carrier_of_mem (p := b2Params)
    E E' hVT hVS hVT' hVS'

end -- noncomputable section

#print axioms b2f_not_singleCrossingOn_of_flatPeak
#print axioms b2f_not_singleCrossingOn
#print axioms b2f_monotoneTransferOn
#print axioms b2Cert_not_singleCrossingOn
#print axioms b2Certificate
#print axioms b2CertificateSchur
#print axioms b2_unique_in_carrier
#print axioms b2_unique_in_carrier_of_mem
#print axioms b2NonMono_three_goals_dominance

end Examples
end Sanctions
