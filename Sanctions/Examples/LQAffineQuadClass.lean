/-
Sanctions/Examples/LQAffineQuadClass.lean

**Classification of the affine-policy, quadratic-value equilibria of the linear–quadratic
benchmark with partial adjustment** (step 2, target 2c, part C, 2026-10-10; referee M3).

The game has the symbolic payoffs of the quadratic–linear family with no rally softening of
the Target's pain (`n = 0`, approved hypothesis 6) and the affine transition
`F(x, s) = (1 − δ)x + δs`:
`U_S = −(q/2)s² + s(u₀ − k·a + r·x) + w·x`, `U_T = −ℓ·a − c·s + v·x`. The rally rate
`r ≥ 0` is free. Write

    D = c − ℓq/k,   den = δ(v − ℓr/k) + (1 − δ)D,
    β_ind(S₂) = (D + 2ℓβ_Sδ²S₂/k)/den,   β_R = D/den.

**The class** (approved hypothesis 5; NOT GENERAL). An equilibrium is in the class when its
policy is affine on `[0,1]` and below full compliance, its Sender value is the quadratic
`S₂y² + S₁y + S₀` with `Q = q − 2β_Sδ²S₂ > 0` (strictly concave dynamic objective), and its
realised sanction is interior, in `(0,1)`, at every state (`AffineQuadClass`).

**What is proved.**

* K0 (`rule_affine`): the realised sanction is affine, `e₀ + e₁x`, with `e₀, e₁` read off the
  vertex of the Sender's objective; `|e₁| < 1`.
* K1 (`sender_curvature`): `S₂(1 − β_S(1−δ)² + β_Sδ²e₁²) = (q/2)e₁²`, so `S₂ ≥ 0`.
* K2 (`policy_slope`): `k·a₁ = r + 2β_Sδ(1−δ)S₂ − Q·e₁`.
* K3 (`target_affine`): the Target's value is affine with slope
  `P₁ = (v − ℓa₁ − ce₁)/(1 − β_T(1 − δ + δe₁))`.
* K4 (`plateau_identity`): with `G = ℓQ − k(c − β_TδP₁)` (minus `Q` times the slope of the
  Target's objective on its compliance plateau),
  `G·(1 − β_T(1−δ+δe₁)) = k·(β_T·den − D − 2ℓβ_Sδ²S₂/k)`. The `e₁`-terms cancel exactly.
* Optimality on the plateau gives `G ≥ 0`, `G > 0 ⇒` full defiance, and positive compliance
  somewhere `⇒ G = 0` (`gap_nonneg_at`, `gap_nonpos_at`).
* **The classification** (`classification_core`, Params level, product form; and
  `lq_affineQuad_classification`, on the quadratic–linear family): `den > 0` is DERIVED from
  the stage relief condition and the class equilibrium (`lq_den_pos_of_class`; no relief rate
  condition is read); then `β_R ≤ β_ind(S₂) ≤ β_T`; strict inequality forces full defiance;
  positive compliance at some state forces `β_T = β_ind(S₂)` (Target indifference).
* Consequences: no class equilibrium below `β_R` (`lq_affineQuad_empty_below_betaR`); below
  `β_R` an affine-policy, quadratic-value equilibrium whose sanction is interior or zero
  everywhere is the relief equilibrium (`lq_affineQuad_relief_unique_below_betaR`); a
  defiance equilibrium in the class has its curvature on the defiance Riccati pair
  (`lq_affineQuad_defiance`).
* Checks at the affine-window member (`q=3, u₀=1, k=3, r=1/2, w=1, ℓ=1, c=4, v=30, δ=β_S=1/2`):
  `β_R = 36/197`, `β_ind(12/701) = 25248/138097 = β₁`, and a defiance equilibrium in the
  class has `S₂ = (10 − 7√2)/2`, hence `β_T ≥ (82 − 7√2)/394` (`aw_affineQuad_*`). The class
  is not empty: the continuum `awEquilibrium` of `AffineWindowContinuum.lean` lies in it
  (`aw_affineQuadClass_awEquilibrium`), and the family theorem's hypotheses hold at the
  member (`aw_lq_hypotheses`).

**Rule 3.** Approved hypotheses 5 (the class) and 6 (`n = 0`; `den > 0` is proved, not
assumed). **Rule 9.** A classification of one class only: equilibria outside it (non-affine
policies, non-quadratic values, sanctions that vanish on part of the state space) are not
classified. **Rule 1.** The Sender's response is its unique maximiser (`σ_dyn_top_eq_clip`);
the Target's optimality is read from `α_opt_top`. **Rule 22.** AFFINE transition.
-/
import Sanctions.Examples.AffineWindowInstance

namespace Sanctions
namespace Examples
namespace AQClass

open Set BoundedContinuousFunction AbstractGame

noncomputable section

/-! ## 1. The class and its constants -/

/-- **The affine-policy, quadratic-value class** (approved hypothesis 5, 2026-10-10; NOT
GENERAL). The policy is affine on the state set and below full compliance, the Sender's value
is the quadratic `S₂y² + S₁y + S₀` with a strictly concave dynamic objective
(`2β_Sδ²S₂ < q`), and the realised sanction is interior at every state.

Scope: affine-policy equilibria only (not general); approved hypothesis 5. -/
structure AffineQuadClass (p : Params) (Eq : p.FeedbackStackelbergEquilibriumTop)
    (q a₀ a₁ S₂ S₁ S₀ : ℝ) : Prop where
  policy : ∀ x ∈ Sanctions.I, Eq.α x = a₀ + a₁ * x
  policy_lt_one : ∀ x ∈ Sanctions.I, Eq.α x < 1
  value : ∀ y : ↥(Sanctions.S : Set ℝ), Eq.V_S y = S₂ * y.val ^ 2 + S₁ * y.val + S₀
  curvature : 2 * p.β_S * p.δ ^ 2 * S₂ < q
  interior : ∀ x ∈ Sanctions.I, p.dynamicEquilibriumRule Eq x ∈ Ioo (0 : ℝ) 1

/-- The Sender's dynamic curvature `Q = q − 2β_Sδ²S₂`.

Scope: linear–quadratic benchmark only (a definition). -/
def dynCurv (p : Params) (q S₂ : ℝ) : ℝ := q - 2 * p.β_S * p.δ ^ 2 * S₂

/-- The vertex of the Sender's dynamic objective at `(x, a)` against the quadratic value.

Scope: linear–quadratic benchmark only (a definition). -/
def vertex (p : Params) (q u₀ k r S₂ S₁ x a : ℝ) : ℝ :=
  (u₀ - k * a + r * x + p.β_S * p.δ * (2 * S₂ * (1 - p.δ) * x + S₁)) / dynCurv p q S₂

/-- The slope `e₁` of the realised sanction.

Scope: linear–quadratic benchmark only (a definition). -/
def slope (p : Params) (q k r a₁ S₂ : ℝ) : ℝ :=
  (r - k * a₁ + 2 * p.β_S * p.δ * (1 - p.δ) * S₂) / dynCurv p q S₂

/-- The intercept `e₀` of the realised sanction.

Scope: linear–quadratic benchmark only (a definition). -/
def intercept (p : Params) (q u₀ k a₀ S₂ S₁ : ℝ) : ℝ :=
  (u₀ - k * a₀ + p.β_S * p.δ * S₁) / dynCurv p q S₂

/-- The slope `P₁ = (v − ℓa₁ − ce₁)/(1 − β_T(1 − δ + δe₁))` of the Target's value.

Scope: linear–quadratic benchmark only (a definition). -/
def tslope (p : Params) (ℓ c v a₁ e₁ : ℝ) : ℝ :=
  (v - ℓ * a₁ - c * e₁) / (1 - p.β_T * (1 - p.δ + p.δ * e₁))

/-- The intercept `P₀` of the Target's value.

Scope: linear–quadratic benchmark only (a definition). -/
def tintercept (p : Params) (ℓ c a₀ e₀ P₁ : ℝ) : ℝ :=
  (-ℓ * a₀ - c * e₀ + p.β_T * P₁ * p.δ * e₀) / (1 - p.β_T)

/-- The gap `G = ℓQ − k(c − β_TδP₁)`: minus `Q` times the slope of the Target's objective in
compliance on its plateau (where the Sender's response is interior).

Scope: linear–quadratic benchmark only (a definition). -/
def gap (p : Params) (k ℓ c Q P₁ : ℝ) : ℝ := ℓ * Q - k * (c - p.β_T * p.δ * P₁)

/-- The Target's net pain per unit of sanction at the placation margin, `D = c − ℓq/k`.

Scope: linear–quadratic benchmark only (a definition). -/
def netPain (q k ℓ c : ℝ) : ℝ := c - ℓ * q / k

/-- The denominator `den = δ(v − ℓr/k) + (1 − δ)D`.

Scope: linear–quadratic benchmark only (a definition). -/
def den (δ q k r ℓ c v : ℝ) : ℝ := δ * (v - ℓ * r / k) + (1 - δ) * netPain q k ℓ c

/-- The indifference discount `β_ind(S₂) = (D + 2ℓβ_Sδ²S₂/k)/den`.

Scope: linear–quadratic benchmark only (a definition). -/
def betaInd (δ βS q k r ℓ c v S₂ : ℝ) : ℝ :=
  (netPain q k ℓ c + 2 * ℓ * βS * δ ^ 2 * S₂ / k) / den δ q k r ℓ c v

/-- The relief end of the window, `β_R = D/den` (`β_ind(0)`).

Scope: linear–quadratic benchmark only (a definition). -/
def betaR (δ q k r ℓ c v : ℝ) : ℝ := netPain q k ℓ c / den δ q k r ℓ c v

/-- At `r = 0` the relief end is the manuscript's formula `D/(δv + (1 − δ)D)`.

Scope: linear–quadratic benchmark only (not general). -/
theorem betaR_of_r_eq_zero (δ q k ℓ c v : ℝ) :
    betaR δ q k 0 ℓ c v = netPain q k ℓ c / (δ * v + (1 - δ) * netPain q k ℓ c) := by
  unfold betaR den; ring_nf

/-! ## 2. Elementary facts -/

/-- A clipped number that is interior is its own clip.

Scope: general class (an elementary fact about clipping). -/
theorem clip_eq_of_mem_Ioo {t : ℝ} (h : max 0 (min 1 t) ∈ Ioo (0 : ℝ) 1) :
    max 0 (min 1 t) = t := by
  rcases le_total t 1 with h1 | h1
  · rw [min_eq_right h1] at h ⊢
    rcases le_total t 0 with h0 | h0
    · rw [max_eq_left h0] at h; exact absurd h.1 (lt_irrefl 0)
    · exact max_eq_right h0
  · rw [min_eq_left h1, max_eq_right zero_le_one] at h; exact absurd h.2 (lt_irrefl 1)

/-- A number in `[0,1]` is its own clip.

Scope: general class (an elementary fact about clipping). -/
theorem clip_eq_of_mem_I {t : ℝ} (h : t ∈ Sanctions.I) : max 0 (min 1 t) = t := by
  rw [min_eq_right h.2, max_eq_right h.1]

section Core

variable {p : Params} {q u₀ k r w ℓ c v : ℝ}

/-- The affine transition maps the square into the state set.

Scope: general class with an affine transition. -/
theorem F_mem_of_affine (hF : p.F = affineF p.δ) {x s : ℝ} (hx : x ∈ Sanctions.I)
    (hs : s ∈ Sanctions.I) : p.F x s ∈ (Sanctions.S : Set ℝ) := by
  rw [hF]; unfold affineF
  have h := p.δ_mem
  have h1 : 0 ≤ 1 - p.δ := by linarith [h.2]
  constructor
  · nlinarith [mul_nonneg h1 hx.1, mul_nonneg h.1.le hs.1]
  · nlinarith [mul_nonneg h1 (sub_nonneg.mpr hx.2), mul_nonneg h.1.le (sub_nonneg.mpr hs.2)]

/-- **The Sender's objective against a quadratic value is a concave parabola** with curvature
`Q/2` around the vertex.

Scope: linear–quadratic benchmark only. -/
theorem senderObj (hUS : p.U_S = symU_S q u₀ k r w) (hF : p.F = affineF p.δ)
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {S₂ S₁ S₀ : ℝ}
    (hV : ∀ y : ↥(Sanctions.S : Set ℝ), V y = S₂ * y.val ^ 2 + S₁ * y.val + S₀)
    (hQ : 0 < dynCurv p q S₂) {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ}
    (hs : s ∈ Sanctions.I) :
    p.U_S x a s + p.β_S * V (Sanctions.clipS' (p.F x s))
      = (w * x + p.β_S * (S₂ * ((1 - p.δ) * x) ^ 2 + S₁ * ((1 - p.δ) * x) + S₀)
          + dynCurv p q S₂ / 2 * vertex p q u₀ k r S₂ S₁ x a ^ 2)
        - dynCurv p q S₂ / 2 * (s - vertex p q u₀ k r S₂ S₁ x a) ^ 2 := by
  have hQ0 : dynCurv p q S₂ ≠ 0 := hQ.ne'
  have hQv : dynCurv p q S₂ * vertex p q u₀ k r S₂ S₁ x a
      = u₀ - k * a + r * x + p.β_S * p.δ * (2 * S₂ * (1 - p.δ) * x + S₁) := by
    unfold vertex; field_simp
  rw [hV, Sanctions.clipS'_val_eq_of_mem (F_mem_of_affine hF hx hs), hUS, hF]
  unfold symU_S affineF
  unfold dynCurv at hQv ⊢
  linear_combination (-s) * hQv

/-- **The Sender's response is the clipped vertex.**

Scope: linear–quadratic benchmark only. -/
theorem σ_dyn_top_eq (hUS : p.U_S = symU_S q u₀ k r w) (hF : p.F = affineF p.δ)
    {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ} {S₂ S₁ S₀ : ℝ}
    (hV : ∀ y : ↥(Sanctions.S : Set ℝ), V y = S₂ * y.val ^ 2 + S₁ * y.val + S₀)
    (hQ : 0 < dynCurv p q S₂) {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    p.σ_dyn_top V x a = max 0 (min 1 (vertex p q u₀ k r S₂ S₁ x a)) :=
  σ_dyn_top_eq_clip p V (half_pos hQ) (fun _ hs => senderObj (w := w) hUS hF hV hQ hx a hs)

/-- The vertex at an affine compliance level is affine in the state.

Scope: linear–quadratic benchmark only (algebra). -/
theorem vertex_affine (p : Params) (q u₀ k r a₀ a₁ S₂ S₁ x : ℝ) :
    vertex p q u₀ k r S₂ S₁ x (a₀ + a₁ * x)
      = intercept p q u₀ k a₀ S₂ S₁ + slope p q k r a₁ S₂ * x := by
  unfold vertex intercept slope; ring

/-- Raising compliance by `t` lowers the vertex by `k·t/Q`.

Scope: linear–quadratic benchmark only (algebra). -/
theorem vertex_add (p : Params) (q u₀ k r S₂ S₁ x a t : ℝ) :
    vertex p q u₀ k r S₂ S₁ x (a + t) = vertex p q u₀ k r S₂ S₁ x a - k * t / dynCurv p q S₂ := by
  unfold vertex; ring

variable {a₀ a₁ S₂ S₁ S₀ : ℝ}

/-- In the class the dynamic curvature is positive.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem dynCurv_pos {Eq : p.FeedbackStackelbergEquilibriumTop}
    (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) : 0 < dynCurv p q S₂ := by
  unfold dynCurv; linarith [hC.curvature]

/-- **K0. The realised sanction is the vertex at the policy.**

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem rule_eq_vertex (hUS : p.U_S = symU_S q u₀ k r w) (hF : p.F = affineF p.δ)
    (Eq : p.FeedbackStackelbergEquilibriumTop) (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    p.dynamicEquilibriumRule Eq x = vertex p q u₀ k r S₂ S₁ x (Eq.α x) := by
  have h := σ_dyn_top_eq (w := w) hUS hF hC.value (dynCurv_pos hC) hx (Eq.α x)
  have hint := hC.interior x hx
  change p.σ_dyn_top Eq.V_S x (Eq.α x) ∈ _ at hint
  change p.σ_dyn_top Eq.V_S x (Eq.α x) = _
  rw [h] at hint ⊢
  exact clip_eq_of_mem_Ioo hint

/-- **K0. The realised sanction is affine in the state.**

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem rule_affine (hUS : p.U_S = symU_S q u₀ k r w) (hF : p.F = affineF p.δ)
    (Eq : p.FeedbackStackelbergEquilibriumTop) (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) :
    ∀ x ∈ Sanctions.I, p.dynamicEquilibriumRule Eq x
      = intercept p q u₀ k a₀ S₂ S₁ + slope p q k r a₁ S₂ * x := by
  intro x hx
  rw [rule_eq_vertex (w := w) hUS hF Eq hC hx, hC.policy x hx, vertex_affine]

/-- The realised sanction's slope lies in `(−1, 1)`.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem slope_mem (hUS : p.U_S = symU_S q u₀ k r w) (hF : p.F = affineF p.δ)
    (Eq : p.FeedbackStackelbergEquilibriumTop) (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) :
    -1 < slope p q k r a₁ S₂ ∧ slope p q k r a₁ S₂ < 1 := by
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_rfl⟩
  have h0 := hC.interior 0 h0I
  have h1 := hC.interior 1 h1I
  rw [rule_affine (w := w) hUS hF Eq hC 0 h0I] at h0
  rw [rule_affine (w := w) hUS hF Eq hC 1 h1I] at h1
  simp only [mul_zero, add_zero, mul_one] at h0 h1
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-- **K2. The policy slope** is the realised slope's defining relation:
`k·a₁ = r + 2β_Sδ(1−δ)S₂ − Q·e₁`.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem policy_slope (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) :
    k * a₁ = r + 2 * p.β_S * p.δ * (1 - p.δ) * S₂ - dynCurv p q S₂ * slope p q k r a₁ S₂ := by
  have hQ0 : dynCurv p q S₂ ≠ 0 := (dynCurv_pos hC).ne'
  unfold slope; field_simp; ring

/-- The Sender's Bellman equation along the policy, in vertex form, at every state.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem sender_bellman (hUS : p.U_S = symU_S q u₀ k r w) (hF : p.F = affineF p.δ)
    (Eq : p.FeedbackStackelbergEquilibriumTop) (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀)
    {y : ℝ} (hy : y ∈ Sanctions.I) :
    S₂ * y ^ 2 + S₁ * y + S₀
      = w * y + p.β_S * (S₂ * ((1 - p.δ) * y) ^ 2 + S₁ * ((1 - p.δ) * y) + S₀)
        + dynCurv p q S₂ / 2
          * (intercept p q u₀ k a₀ S₂ S₁ + slope p q k r a₁ S₂ * y) ^ 2 := by
  have hσ : p.σ_dyn_top Eq.V_S y (Eq.α y) = vertex p q u₀ k r S₂ S₁ y (Eq.α y) :=
    rule_eq_vertex (w := w) hUS hF Eq hC hy
  have hvI : vertex p q u₀ k r S₂ S₁ y (Eq.α y) ∈ Sanctions.I :=
    hσ ▸ p.σ_dyn_top_mem_I Eq.V_S y (Eq.α y)
  have h := V_S_eq_at_top p Eq ⟨y, hy⟩
  dsimp only at h
  rw [hσ, senderObj hUS hF hC.value (dynCurv_pos hC) hy (Eq.α y) hvI, sub_self] at h
  rw [hC.value] at h
  dsimp only at h
  rw [hC.policy y hy, vertex_affine] at h
  linear_combination h

/-- **K1. The Sender's curvature**: `S₂(1 − β_S(1−δ)² + β_Sδ²e₁²) = (q/2)e₁²`.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem sender_curvature (hUS : p.U_S = symU_S q u₀ k r w) (hF : p.F = affineF p.δ)
    (Eq : p.FeedbackStackelbergEquilibriumTop) (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) :
    S₂ * (1 - p.β_S * (1 - p.δ) ^ 2 + p.β_S * p.δ ^ 2 * slope p q k r a₁ S₂ ^ 2)
      = q / 2 * slope p q k r a₁ S₂ ^ 2 := by
  have h0 := sender_bellman hUS hF Eq hC (y := 0) ⟨le_rfl, zero_le_one⟩
  have h12 := sender_bellman hUS hF Eq hC (y := 1 / 2) ⟨by norm_num, by norm_num⟩
  have h1 := sender_bellman hUS hF Eq hC (y := 1) ⟨zero_le_one, le_rfl⟩
  have hA : S₂ = p.β_S * S₂ * (1 - p.δ) ^ 2 + dynCurv p q S₂ / 2 * slope p q k r a₁ S₂ ^ 2 := by
    linear_combination 2 * h1 - 4 * h12 + 2 * h0
  unfold dynCurv at hA
  linear_combination hA

/-- `S₂ ≥ 0` in the class, when `q > 0`.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem curvature_nonneg (hUS : p.U_S = symU_S q u₀ k r w) (hF : p.F = affineF p.δ)
    (hq : 0 < q) (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) : 0 ≤ S₂ := by
  have h := sender_curvature (w := w) (u₀ := u₀) hUS hF Eq hC
  have hδ := p.δ_mem
  have hβ := p.β_S_mem
  have hd2 : (1 - p.δ) ^ 2 < 1 := by nlinarith [hδ.1, hδ.2]
  have hpos : 0 < 1 - p.β_S * (1 - p.δ) ^ 2 + p.β_S * p.δ ^ 2 * slope p q k r a₁ S₂ ^ 2 := by
    have h1 : p.β_S * (1 - p.δ) ^ 2 < 1 := by nlinarith [hβ.1, hβ.2, sq_nonneg (1 - p.δ)]
    have h2 : 0 ≤ p.β_S * p.δ ^ 2 * slope p q k r a₁ S₂ ^ 2 :=
      mul_nonneg (mul_nonneg hβ.1 (sq_nonneg _)) (sq_nonneg _)
    linarith
  have hrhs : 0 ≤ q / 2 * slope p q k r a₁ S₂ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  by_contra hneg
  have hneg := not_le.mp hneg
  have : S₂ * (1 - p.β_S * (1 - p.δ) ^ 2 + p.β_S * p.δ ^ 2 * slope p q k r a₁ S₂ ^ 2) < 0 :=
    mul_neg_of_neg_of_pos hneg hpos
  linarith

/-- `1 − β_T(1 − δ + δe₁) > 0` when `e₁ < 1`.

Scope: general class (elementary). -/
theorem one_sub_βT_m_pos (p : Params) {e₁ : ℝ} (he : e₁ < 1) :
    0 < 1 - p.β_T * (1 - p.δ + p.δ * e₁) := by
  have hδ := p.δ_mem
  have hβ := p.β_T_mem
  have hm : 0 < 1 - (1 - p.δ + p.δ * e₁) := by nlinarith [hδ.1]
  nlinarith [mul_nonneg hβ.1 hm.le, hβ.2]

/-- **K3 (abstract form).** If the realised sanction and the policy are affine, the Target's
value is affine with slope `P₁` and intercept `P₀` solving the two linear recursions.

Scope: linear–quadratic benchmark only; affine policy and affine sanction (not general). -/
theorem target_affine_of (hUT : p.U_T = symU_T ℓ c 0 v) (hF : p.F = affineF p.δ)
    (Eq : p.FeedbackStackelbergEquilibriumTop) {e₀ e₁ P₁ P₀ : ℝ}
    (hpol : ∀ x ∈ Sanctions.I, Eq.α x = a₀ + a₁ * x)
    (hrule : ∀ x ∈ Sanctions.I, p.dynamicEquilibriumRule Eq x = e₀ + e₁ * x)
    (hP₁ : P₁ * (1 - p.β_T * (1 - p.δ + p.δ * e₁)) = v - ℓ * a₁ - c * e₁)
    (hP₀ : P₀ * (1 - p.β_T) = -ℓ * a₀ - c * e₀ + p.β_T * P₁ * p.δ * e₀) :
    ∀ y : ↥(Sanctions.S : Set ℝ), Eq.V_T y = P₁ * y.val + P₀ := by
  have hβ := p.β_T_mem
  let D : ↥(Sanctions.S : Set ℝ) → ℝ := fun y => Eq.V_T y - (P₁ * y.val + P₀)
  let φ : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.S : Set ℝ) := fun y =>
    Sanctions.clipS' (p.F y.val (p.σ_dyn_top Eq.V_S y.val (Eq.α y.val)))
  have hrec : ∀ y, D y = p.β_T * D (φ y) := by
    intro y
    have hV := Params.FeedbackStackelbergEquilibriumTop.V_T_eq_at_policy p Eq y
    simp only [Params.joint_T_top_integrand] at hV
    have hσ : p.σ_dyn_top Eq.V_S y.val (Eq.α y.val) = e₀ + e₁ * y.val := hrule y.val y.property
    have hσI : e₀ + e₁ * y.val ∈ Sanctions.I := hσ ▸ p.σ_dyn_top_mem_I _ _ _
    simp only [D, φ]
    rw [hσ] at hV ⊢
    rw [hV, Sanctions.clipS'_val_eq_of_mem (F_mem_of_affine hF y.property hσI), hUT, hF,
      hpol y.val y.property]
    unfold symU_T affineF
    linear_combination (-(y.val)) * hP₁ - hP₀
  have hbound : ∀ y, |D y| ≤ ‖Eq.V_T‖ + |P₁| + |P₀| := by
    intro y
    have h1 := BoundedContinuousFunction.norm_coe_le_norm Eq.V_T y
    rw [Real.norm_eq_abs] at h1
    have hy := y.property
    have hy' : |y.val| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    have h2 : |P₁ * y.val| ≤ |P₁| := by
      rw [abs_mul]; nlinarith [abs_nonneg P₁, abs_nonneg y.val]
    calc |D y| = |Eq.V_T y - (P₁ * y.val + P₀)| := rfl
      _ ≤ |Eq.V_T y| + |P₁ * y.val + P₀| := abs_sub _ _
      _ ≤ |Eq.V_T y| + (|P₁ * y.val| + |P₀|) := by gcongr; exact abs_add_le _ _
      _ ≤ ‖Eq.V_T‖ + |P₁| + |P₀| := by linarith
  intro y
  have h := eq_zero_of_eq_mul_comp hβ.1 hβ.2 hbound hrec y
  simp only [D] at h
  linarith

/-- **K3. The Target's value is affine**, with slope
`P₁ = (v − ℓa₁ − ce₁)/(1 − β_T(1 − δ + δe₁))`.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem target_affine (hUS : p.U_S = symU_S q u₀ k r w) (hUT : p.U_T = symU_T ℓ c 0 v)
    (hF : p.F = affineF p.δ) (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) :
    ∀ y : ↥(Sanctions.S : Set ℝ), Eq.V_T y
      = tslope p ℓ c v a₁ (slope p q k r a₁ S₂) * y.val
        + tintercept p ℓ c a₀ (intercept p q u₀ k a₀ S₂ S₁)
            (tslope p ℓ c v a₁ (slope p q k r a₁ S₂)) := by
  have hβ := p.β_T_mem
  have hm := one_sub_βT_m_pos p (slope_mem (w := w) hUS hF Eq hC).2
  have h1 : (1 - p.β_T) ≠ 0 := by linarith [hβ.2]
  refine target_affine_of hUT hF Eq hC.policy (rule_affine (w := w) hUS hF Eq hC) ?_ ?_
  · unfold tslope; exact div_mul_cancel₀ _ hm.ne'
  · unfold tintercept; exact div_mul_cancel₀ _ h1

/-! ## 3. The Target's objective on its compliance plateau -/

/-- The Target's objective where the Sender's response is interior.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem joint_eq (hUS : p.U_S = symU_S q u₀ k r w) (hUT : p.U_T = symU_T ℓ c 0 v)
    (hF : p.F = affineF p.δ) (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) {P₁ P₀ : ℝ}
    (hT : ∀ y : ↥(Sanctions.S : Set ℝ), Eq.V_T y = P₁ * y.val + P₀)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (hvI : vertex p q u₀ k r S₂ S₁ x a ∈ Sanctions.I) :
    p.joint_T_top_integrand Eq.V_T Eq.V_S x a
      = -ℓ * a - c * vertex p q u₀ k r S₂ S₁ x a + v * x
        + p.β_T * (P₁ * ((1 - p.δ) * x + p.δ * vertex p q u₀ k r S₂ S₁ x a) + P₀) := by
  simp only [Params.joint_T_top_integrand]
  rw [σ_dyn_top_eq (w := w) hUS hF hC.value (dynCurv_pos hC) hx a, clip_eq_of_mem_I hvI, hT,
    Sanctions.clipS'_val_eq_of_mem (F_mem_of_affine hF hx hvI), hUT, hF]
  unfold symU_T affineF; ring

/-- **The Target's objective is affine in compliance on the plateau**, with slope `−G/Q`.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem joint_sub (hUS : p.U_S = symU_S q u₀ k r w) (hUT : p.U_T = symU_T ℓ c 0 v)
    (hF : p.F = affineF p.δ) (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) {P₁ P₀ : ℝ}
    (hT : ∀ y : ↥(Sanctions.S : Set ℝ), Eq.V_T y = P₁ * y.val + P₀)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a a' : ℝ}
    (hv : vertex p q u₀ k r S₂ S₁ x a ∈ Sanctions.I)
    (hv' : vertex p q u₀ k r S₂ S₁ x a' ∈ Sanctions.I) :
    dynCurv p q S₂ * (p.joint_T_top_integrand Eq.V_T Eq.V_S x a'
        - p.joint_T_top_integrand Eq.V_T Eq.V_S x a)
      = -(gap p k ℓ c (dynCurv p q S₂) P₁) * (a' - a) := by
  have hQ0 : dynCurv p q S₂ ≠ 0 := (dynCurv_pos hC).ne'
  have hQv : dynCurv p q S₂ * vertex p q u₀ k r S₂ S₁ x a
      = u₀ - k * a + r * x + p.β_S * p.δ * (2 * S₂ * (1 - p.δ) * x + S₁) := by
    unfold vertex; field_simp
  have hQv' : dynCurv p q S₂ * vertex p q u₀ k r S₂ S₁ x a'
      = u₀ - k * a' + r * x + p.β_S * p.δ * (2 * S₂ * (1 - p.δ) * x + S₁) := by
    unfold vertex; field_simp
  rw [joint_eq hUS hUT hF Eq hC hT hx hv, joint_eq hUS hUT hF Eq hC hT hx hv']
  unfold gap
  linear_combination (-(c - p.β_T * p.δ * P₁)) * hQv' + (c - p.β_T * p.δ * P₁) * hQv

/-- **The gap is nonnegative** at any state where compliance is below one: raising compliance
slightly keeps the response interior, so optimality bounds the plateau slope above by zero.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem gap_nonneg_at (hUS : p.U_S = symU_S q u₀ k r w) (hUT : p.U_T = symU_T ℓ c 0 v)
    (hF : p.F = affineF p.δ) (hk : 0 < k) (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) {P₁ P₀ : ℝ}
    (hT : ∀ y : ↥(Sanctions.S : Set ℝ), Eq.V_T y = P₁ * y.val + P₀)
    {x : ℝ} (hx : x ∈ Sanctions.I) : 0 ≤ gap p k ℓ c (dynCurv p q S₂) P₁ := by
  have hQ := dynCurv_pos hC
  have haI := Eq.α_mem x hx
  have ha1 := hC.policy_lt_one x hx
  have hσ := rule_eq_vertex (w := w) hUS hF Eq hC hx
  have hint := hC.interior x hx
  rw [hσ] at hint
  set σ := vertex p q u₀ k r S₂ S₁ x (Eq.α x) with hσdef
  set t := min (1 - Eq.α x) (dynCurv p q S₂ * σ / k) with htdef
  have ht0 : 0 < t := lt_min (by linarith) (div_pos (mul_pos hQ hint.1) hk)
  have ht1 : t ≤ 1 - Eq.α x := min_le_left _ _
  have ht2 : t ≤ dynCurv p q S₂ * σ / k := min_le_right _ _
  have hkt : k * t ≤ dynCurv p q S₂ * σ := by
    rw [le_div_iff₀ hk] at ht2; linarith
  have hkt' : k * t / dynCurv p q S₂ ≤ σ := by rw [div_le_iff₀ hQ]; linarith
  have hkt0 : 0 ≤ k * t / dynCurv p q S₂ := div_nonneg (mul_nonneg hk.le ht0.le) hQ.le
  have hv'I : vertex p q u₀ k r S₂ S₁ x (Eq.α x + t) ∈ Sanctions.I := by
    rw [vertex_add, ← hσdef]
    constructor <;> linarith [hint.2]
  have hvI : σ ∈ Sanctions.I := ⟨hint.1.le, hint.2.le⟩
  have hmem : Eq.α x + t ∈ Sanctions.I := ⟨by linarith [haI.1], by linarith⟩
  have hopt : p.joint_T_top_integrand Eq.V_T Eq.V_S x (Eq.α x + t)
      ≤ p.joint_T_top_integrand Eq.V_T Eq.V_S x (Eq.α x) :=
    isMaxOn_iff.mp (Eq.α_opt_top x hx) _ hmem
  have hsub := joint_sub hUS hUT hF Eq hC hT hx hvI hv'I
  have h1 : dynCurv p q S₂ * (p.joint_T_top_integrand Eq.V_T Eq.V_S x (Eq.α x + t)
      - p.joint_T_top_integrand Eq.V_T Eq.V_S x (Eq.α x)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hQ.le (by linarith)
  rw [hsub] at h1
  by_contra hneg
  have hneg := not_le.mp hneg
  nlinarith

/-- **The gap is nonpositive** at any state with positive compliance: lowering compliance
slightly keeps the response interior.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem gap_nonpos_at (hUS : p.U_S = symU_S q u₀ k r w) (hUT : p.U_T = symU_T ℓ c 0 v)
    (hF : p.F = affineF p.δ) (hk : 0 < k) (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) {P₁ P₀ : ℝ}
    (hT : ∀ y : ↥(Sanctions.S : Set ℝ), Eq.V_T y = P₁ * y.val + P₀)
    {x : ℝ} (hx : x ∈ Sanctions.I) (hpos : 0 < Eq.α x) :
    gap p k ℓ c (dynCurv p q S₂) P₁ ≤ 0 := by
  have hQ := dynCurv_pos hC
  have haI := Eq.α_mem x hx
  have hσ := rule_eq_vertex (w := w) hUS hF Eq hC hx
  have hint := hC.interior x hx
  rw [hσ] at hint
  set σ := vertex p q u₀ k r S₂ S₁ x (Eq.α x) with hσdef
  set t := min (Eq.α x) (dynCurv p q S₂ * (1 - σ) / k) with htdef
  have ht0 : 0 < t := lt_min hpos (div_pos (mul_pos hQ (by linarith [hint.2])) hk)
  have ht1 : t ≤ Eq.α x := min_le_left _ _
  have ht2 : t ≤ dynCurv p q S₂ * (1 - σ) / k := min_le_right _ _
  have hkt : k * t ≤ dynCurv p q S₂ * (1 - σ) := by
    rw [le_div_iff₀ hk] at ht2; linarith
  have hkt' : k * t / dynCurv p q S₂ ≤ 1 - σ := by rw [div_le_iff₀ hQ]; linarith
  have hkt0 : 0 ≤ k * t / dynCurv p q S₂ := div_nonneg (mul_nonneg hk.le ht0.le) hQ.le
  have hv'I : vertex p q u₀ k r S₂ S₁ x (Eq.α x + -t) ∈ Sanctions.I := by
    rw [vertex_add, ← hσdef]
    have : k * -t / dynCurv p q S₂ = -(k * t / dynCurv p q S₂) := by ring
    rw [this]
    constructor <;> linarith [hint.1]
  have hvI : σ ∈ Sanctions.I := ⟨hint.1.le, hint.2.le⟩
  have hmem : Eq.α x + -t ∈ Sanctions.I := ⟨by linarith, by linarith [haI.2]⟩
  have hopt : p.joint_T_top_integrand Eq.V_T Eq.V_S x (Eq.α x + -t)
      ≤ p.joint_T_top_integrand Eq.V_T Eq.V_S x (Eq.α x) :=
    isMaxOn_iff.mp (Eq.α_opt_top x hx) _ hmem
  have hsub := joint_sub hUS hUT hF Eq hC hT hx hvI hv'I
  have h1 : dynCurv p q S₂ * (p.joint_T_top_integrand Eq.V_T Eq.V_S x (Eq.α x + -t)
      - p.joint_T_top_integrand Eq.V_T Eq.V_S x (Eq.α x)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hQ.le (by linarith)
  rw [hsub] at h1
  by_contra hneg
  have hneg := not_le.mp hneg
  nlinarith

/-- **K4. The plateau identity**: `G·(1 − β_T m) = β_T·k·den − k·D − 2ℓβ_Sδ²S₂`, written
without division. The terms in the realised slope `e₁` cancel.

Scope: linear–quadratic benchmark only (pure algebra). -/
theorem plateau_identity (p : Params) {q k r ℓ c v S₂ a₁ e₁ P₁ : ℝ}
    (hP₁ : P₁ * (1 - p.β_T * (1 - p.δ + p.δ * e₁)) = v - ℓ * a₁ - c * e₁)
    (he₁ : dynCurv p q S₂ * e₁ = r - k * a₁ + 2 * p.β_S * p.δ * (1 - p.δ) * S₂) :
    gap p k ℓ c (dynCurv p q S₂) P₁ * (1 - p.β_T * (1 - p.δ + p.δ * e₁))
      = p.β_T * (p.δ * (k * v - ℓ * r) + (1 - p.δ) * (k * c - ℓ * q))
        - (k * c - ℓ * q) - 2 * ℓ * p.β_S * p.δ ^ 2 * S₂ := by
  unfold gap dynCurv at *
  linear_combination (k * p.β_T * p.δ) * hP₁ - (p.β_T * p.δ * ℓ) * he₁

/-- **The classification, Params level, product form.** In every class equilibrium,
`k·D + 2ℓβ_Sδ²S₂ ≤ β_T·k·den`; strict inequality forces full defiance; positive compliance at
some state forces equality. No sign of `den` is used.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6 (`n = 0`). -/
theorem classification_core (hUS : p.U_S = symU_S q u₀ k r w) (hUT : p.U_T = symU_T ℓ c 0 v)
    (hF : p.F = affineF p.δ) (hk : 0 < k) (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hC : AffineQuadClass p Eq q a₀ a₁ S₂ S₁ S₀) :
    k * c - ℓ * q + 2 * ℓ * p.β_S * p.δ ^ 2 * S₂
        ≤ p.β_T * (p.δ * (k * v - ℓ * r) + (1 - p.δ) * (k * c - ℓ * q)) ∧
      (k * c - ℓ * q + 2 * ℓ * p.β_S * p.δ ^ 2 * S₂
          < p.β_T * (p.δ * (k * v - ℓ * r) + (1 - p.δ) * (k * c - ℓ * q)) →
        ∀ x ∈ Sanctions.I, Eq.α x = 0) ∧
      ((∃ x ∈ Sanctions.I, 0 < Eq.α x) →
        k * c - ℓ * q + 2 * ℓ * p.β_S * p.δ ^ 2 * S₂
          = p.β_T * (p.δ * (k * v - ℓ * r) + (1 - p.δ) * (k * c - ℓ * q))) := by
  set e₁ := slope p q k r a₁ S₂ with he₁def
  set e₀ := intercept p q u₀ k a₀ S₂ S₁ with he₀def
  set P₁ := tslope p ℓ c v a₁ e₁ with hP₁def
  set P₀ := tintercept p ℓ c a₀ e₀ P₁ with hP₀def
  have hQ := dynCurv_pos hC
  have hm := one_sub_βT_m_pos p (slope_mem (w := w) hUS hF Eq hC).2
  have hT : ∀ y : ↥(Sanctions.S : Set ℝ), Eq.V_T y = P₁ * y.val + P₀ :=
    target_affine hUS hUT hF Eq hC
  have hP₁ : P₁ * (1 - p.β_T * (1 - p.δ + p.δ * e₁)) = v - ℓ * a₁ - c * e₁ := by
    rw [hP₁def]; unfold tslope; exact div_mul_cancel₀ _ hm.ne'
  have he₁ : dynCurv p q S₂ * e₁ = r - k * a₁ + 2 * p.β_S * p.δ * (1 - p.δ) * S₂ := by
    rw [he₁def]; unfold slope; field_simp
  have hid := plateau_identity p hP₁ he₁
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have hG := gap_nonneg_at hUS hUT hF hk Eq hC hT h0I
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hG hm.le]
  · intro hlt x hx
    have hGpos : 0 < gap p k ℓ c (dynCurv p q S₂) P₁ := by
      by_contra hle
      have hle := not_lt.mp hle
      have hG0 : gap p k ℓ c (dynCurv p q S₂) P₁ = 0 := le_antisymm hle hG
      rw [hG0, zero_mul] at hid
      linarith
    have haI := Eq.α_mem x hx
    rcases eq_or_lt_of_le haI.1 with h | h
    · exact h.symm
    · exact absurd (gap_nonpos_at hUS hUT hF hk Eq hC hT hx h) (not_le.mpr hGpos)
  · rintro ⟨x, hx, hpos⟩
    have hG0 : gap p k ℓ c (dynCurv p q S₂) P₁ = 0 :=
      le_antisymm (gap_nonpos_at hUS hUT hF hk Eq hC hT hx hpos) hG
    rw [hG0, zero_mul] at hid
    linarith

end Core

/-! ## 4. On the quadratic–linear family: `den > 0` derived, and the classification -/

/-- **The zero level's Lipschitz constant is at least `r_hi/k_lo`**, on every enriched chord
economy: `L_α = M_tot·L_resp/(k_lo·μ)` with `L_resp ≥ r_hi` and `M_tot ≥ μ > 0`.

Scope: general class (enriched chord economies). -/
theorem rhi_div_klo_le_Lalpha (E : ChordEconomyCs) : E.rhi / E.klo ≤ E.Lalpha := by
  unfold ChordEconomyCs.Lalpha
  have hk := E.hklo
  have hmu := E.mu_pos
  have hmuM := E.mu_le_Mtot
  have hL0 := E.Lresp_nonneg
  have hL : E.rhi ≤ E.Lresp := by
    unfold ChordEconomyTwoSided.Lresp ChordEconomy.plLresp
    have hσ : 0 ≤ max E.SigV E.SigC := le_max_of_le_left E.hSigV0
    have h := mul_nonneg E.hβS0.le
      (add_nonneg (mul_nonneg (mul_nonneg hσ E.ghi_nonneg) E.dhi_nonneg)
        (mul_nonneg (by linarith [E.KS_nonneg] : (0 : ℝ) ≤ E.KS + 2 * max E.SigV E.SigC)
          E.hMmix0))
    linarith
  rw [div_le_div_iff₀ hk (mul_pos hk hmu)]
  have h1 : E.rhi * E.mu ≤ E.Lresp * E.Mtot := mul_le_mul hL hmuM hmu.le hL0
  nlinarith [mul_le_mul_of_nonneg_left h1 hk.le]

/-- **`den > 0` is derived, not assumed** (approved hypothesis 6). In a class equilibrium on the
quadratic–linear family with `n = 0` and the stage relief margin, `den > 0`. The product form
of the classification (`classification_core`) bounds the positive quantity
`k·c − ℓq + 2ℓβ_Sδ²S₂` (stage relief and `S₂ ≥ 0`) by `β_T·k·den`, so `den > 0`. No relief
rate condition is read.

Scope: affine-policy equilibria only (not general); approved hypotheses 5 (the class) and 6
(`n = 0`). -/
theorem lq_den_pos_of_class (E : PlacableEconomyFcs) (hF : E.F = affineF E.δ)
    (hn : E.n = 0) (hSR : E.StageRelief)
    (Eq : E.toChordCs.toParams.FeedbackStackelbergEquilibriumTop) {a₀ a₁ S₂ S₁ S₀ : ℝ}
    (hC : AffineQuadClass E.toChordCs.toParams Eq E.q a₀ a₁ S₂ S₁ S₀) :
    0 < den E.δ E.q E.k E.r E.ℓ E.c E.v := by
  have hUS : E.toChordCs.toParams.U_S = symU_S E.q E.u₀ E.k E.r E.w := rfl
  have hUT : E.toChordCs.toParams.U_T = symU_T E.ℓ E.c 0 E.v := by
    rw [← hn]; rfl
  have hF' : E.toChordCs.toParams.F = affineF E.toChordCs.toParams.δ := hF
  have hk := E.hk
  have hS₂ : 0 ≤ S₂ := curvature_nonneg hUS hF' E.hq Eq hC
  obtain ⟨h1, -, -⟩ := classification_core hUS hUT hF' hk Eq hC
  have h1' : E.k * E.c - E.ℓ * E.q + 2 * E.ℓ * E.βS * E.δ ^ 2 * S₂
      ≤ E.βT * (E.δ * (E.k * E.v - E.ℓ * E.r) + (1 - E.δ) * (E.k * E.c - E.ℓ * E.q)) := h1
  have hsr : E.ℓ * E.q < E.k * E.c := by
    have h : E.ℓ * E.q < E.k * (E.c - E.n) := hSR
    rwa [hn, sub_zero] at h
  have hε : 0 ≤ 2 * E.ℓ * E.βS * E.δ ^ 2 * S₂ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two E.hℓ.le) E.hβS0.le)
      (sq_nonneg _)) hS₂
  have hX : 0 < E.δ * (E.k * E.v - E.ℓ * E.r) + (1 - E.δ) * (E.k * E.c - E.ℓ * E.q) := by
    by_contra hneg
    push Not at hneg
    have := mul_nonpos_of_nonneg_of_nonpos E.hβT0.le hneg
    linarith
  have hDk : den E.δ E.q E.k E.r E.ℓ E.c E.v * E.k
      = E.δ * (E.k * E.v - E.ℓ * E.r) + (1 - E.δ) * (E.k * E.c - E.ℓ * E.q) := by
    unfold den netPain; field_simp
  rw [← hDk] at hX
  exact pos_of_mul_pos_left hX hk.le

/-- **Classification of the affine-policy, quadratic-value equilibria** of the linear–quadratic
benchmark (`F` affine, `n = 0`, any rally rate `r ≥ 0`). In every equilibrium of the class
(`AffineQuadClass`: affine policy below full compliance, quadratic Sender value with a
strictly concave dynamic objective, interior realised sanctions), `den > 0`, the Sender
value's curvature is `S₂ ≥ 0`, and

    β_R ≤ β_ind(S₂) ≤ β_T,

strict inequality `β_ind(S₂) < β_T` forces full defiance, and positive compliance at some
state forces `β_T = β_ind(S₂)` (the Target is indifferent on its compliance plateau).

Scope: affine-policy equilibria only (not general); approved hypotheses 5 (the class) and 6
(`n = 0`; `den > 0` derived from stage relief and the class). -/
theorem lq_affineQuad_classification (E : PlacableEconomyFcs) (hF : E.F = affineF E.δ)
    (hn : E.n = 0) (hSR : E.StageRelief)
    (Eq : E.toChordCs.toParams.FeedbackStackelbergEquilibriumTop) {a₀ a₁ S₂ S₁ S₀ : ℝ}
    (hC : AffineQuadClass E.toChordCs.toParams Eq E.q a₀ a₁ S₂ S₁ S₀) :
    0 < den E.δ E.q E.k E.r E.ℓ E.c E.v ∧ 0 ≤ S₂ ∧
      betaR E.δ E.q E.k E.r E.ℓ E.c E.v ≤ betaInd E.δ E.βS E.q E.k E.r E.ℓ E.c E.v S₂ ∧
      betaInd E.δ E.βS E.q E.k E.r E.ℓ E.c E.v S₂ ≤ E.βT ∧
      (betaInd E.δ E.βS E.q E.k E.r E.ℓ E.c E.v S₂ < E.βT → ∀ x ∈ Sanctions.I, Eq.α x = 0) ∧
      ((∃ x ∈ Sanctions.I, 0 < Eq.α x) →
        E.βT = betaInd E.δ E.βS E.q E.k E.r E.ℓ E.c E.v S₂) := by
  have hUS : E.toChordCs.toParams.U_S = symU_S E.q E.u₀ E.k E.r E.w := rfl
  have hUT : E.toChordCs.toParams.U_T = symU_T E.ℓ E.c 0 E.v := by
    rw [← hn]; rfl
  have hF' : E.toChordCs.toParams.F = affineF E.toChordCs.toParams.δ := hF
  have hk := E.hk
  have hden := lq_den_pos_of_class E hF hn hSR Eq hC
  have hS₂ : 0 ≤ S₂ := curvature_nonneg hUS hF' E.hq Eq hC
  obtain ⟨h1, h2, h3⟩ := classification_core hUS hUT hF' hk Eq hC
  have h1' : E.k * E.c - E.ℓ * E.q + 2 * E.ℓ * E.βS * E.δ ^ 2 * S₂
      ≤ E.βT * (E.δ * (E.k * E.v - E.ℓ * E.r) + (1 - E.δ) * (E.k * E.c - E.ℓ * E.q)) := h1
  have h2' : E.k * E.c - E.ℓ * E.q + 2 * E.ℓ * E.βS * E.δ ^ 2 * S₂
      < E.βT * (E.δ * (E.k * E.v - E.ℓ * E.r) + (1 - E.δ) * (E.k * E.c - E.ℓ * E.q)) →
      ∀ x ∈ Sanctions.I, Eq.α x = 0 := h2
  have h3' : (∃ x ∈ Sanctions.I, 0 < Eq.α x) →
      E.k * E.c - E.ℓ * E.q + 2 * E.ℓ * E.βS * E.δ ^ 2 * S₂
        = E.βT * (E.δ * (E.k * E.v - E.ℓ * E.r) + (1 - E.δ) * (E.k * E.c - E.ℓ * E.q)) := h3
  set B := betaInd E.δ E.βS E.q E.k E.r E.ℓ E.c E.v S₂ with hBdef
  set Dn := den E.δ E.q E.k E.r E.ℓ E.c E.v with hDndef
  have hB : B * Dn = netPain E.q E.k E.ℓ E.c + 2 * E.ℓ * E.βS * E.δ ^ 2 * S₂ / E.k :=
    div_mul_cancel₀ _ hden.ne'
  have hNk : (netPain E.q E.k E.ℓ E.c + 2 * E.ℓ * E.βS * E.δ ^ 2 * S₂ / E.k) * E.k
      = E.k * E.c - E.ℓ * E.q + 2 * E.ℓ * E.βS * E.δ ^ 2 * S₂ := by
    unfold netPain; field_simp
  have hDk : Dn * E.k
      = E.δ * (E.k * E.v - E.ℓ * E.r) + (1 - E.δ) * (E.k * E.c - E.ℓ * E.q) := by
    rw [hDndef]; unfold den netPain; field_simp
  have hDkpos : 0 < Dn * E.k := mul_pos hden hk
  have hBk : B * (Dn * E.k) = E.k * E.c - E.ℓ * E.q + 2 * E.ℓ * E.βS * E.δ ^ 2 * S₂ := by
    rw [← hNk, ← hB]; ring
  rw [← hDk] at h1' h2' h3'
  refine ⟨hden, hS₂, ?_, ?_, ?_, ?_⟩
  · have hR : betaR E.δ E.q E.k E.r E.ℓ E.c E.v * Dn = netPain E.q E.k E.ℓ E.c :=
      div_mul_cancel₀ _ hden.ne'
    have hε : 0 ≤ 2 * E.ℓ * E.βS * E.δ ^ 2 * S₂ / E.k :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two E.hℓ.le)
        E.hβS0.le) (sq_nonneg _)) hS₂) hk.le
    exact le_of_mul_le_mul_right (by linarith) hden
  · exact le_of_mul_le_mul_right (by linarith) hDkpos
  · intro hlt
    exact h2' (by rw [← hBk]; exact mul_lt_mul_of_pos_right hlt hDkpos)
  · intro hex
    have h' : B * (Dn * E.k) = E.βT * (Dn * E.k) := by rw [hBk]; exact h3' hex
    exact (mul_right_cancel₀ hDkpos.ne' h').symm

/-- **No class equilibrium below `β_R`.** Below the relief end `β_R = D/den` no equilibrium has
an affine policy, a quadratic Sender value and interior sanctions at every state.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem lq_affineQuad_empty_below_betaR (E : PlacableEconomyFcs) (hF : E.F = affineF E.δ)
    (hn : E.n = 0) (hSR : E.StageRelief)
    (hβ : E.βT < betaR E.δ E.q E.k E.r E.ℓ E.c E.v) :
    ¬ ∃ (Eq : E.toChordCs.toParams.FeedbackStackelbergEquilibriumTop) (a₀ a₁ S₂ S₁ S₀ : ℝ),
      AffineQuadClass E.toChordCs.toParams Eq E.q a₀ a₁ S₂ S₁ S₀ := by
  rintro ⟨Eq, a₀, a₁, S₂, S₁, S₀, hC⟩
  obtain ⟨-, -, h3, h4, -, -⟩ := lq_affineQuad_classification E hF hn hSR Eq hC
  linarith

/-- **Relief is unique in the class below `β_R`.** Below the relief end, an equilibrium with an
affine policy below full compliance and a quadratic Sender value with a strictly concave
dynamic objective, whose realised sanction is either interior at every state or zero at every
state, never sanctions; under interiority and placability it is the relief equilibrium (the
zero level, the zero-sanction Sender value, the relief Target value).

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6; class under
placability for the relief identification. -/
theorem lq_affineQuad_relief_unique_below_betaR (E : PlacableEconomyFcs)
    (hF : E.F = affineF E.δ) (hn : E.n = 0) (hSR : E.StageRelief)
    (hInt : E.Interior) (hP : E.Placable)
    (hβ : E.βT < betaR E.δ E.q E.k E.r E.ℓ E.c E.v)
    (Eq : E.toChordCs.toParams.FeedbackStackelbergEquilibriumTop) {a₀ a₁ S₂ S₁ S₀ : ℝ}
    (hpol : ∀ x ∈ Sanctions.I, Eq.α x = a₀ + a₁ * x) (hlt : ∀ x ∈ Sanctions.I, Eq.α x < 1)
    (hV : ∀ y : ↥(Sanctions.S : Set ℝ), Eq.V_S y = S₂ * y.val ^ 2 + S₁ * y.val + S₀)
    (hQ : 2 * E.βS * E.δ ^ 2 * S₂ < E.q)
    (hrule : (∀ x ∈ Sanctions.I, E.toChordCs.toParams.dynamicEquilibriumRule Eq x ∈ Ioo (0 : ℝ) 1)
      ∨ (∀ x ∈ Sanctions.I, E.toChordCs.toParams.dynamicEquilibriumRule Eq x = 0)) :
    (∀ x ∈ Sanctions.I, E.toChordCs.toParams.dynamicEquilibriumRule Eq x = 0) ∧
      (∀ x ∈ Sanctions.I, Eq.α x = E.toChordCs.zeroLevel x) ∧
      Eq.V_S = E.toChordCs.VS01 ∧
      Eq.V_T = E.toChordCs.VTrel (E.toChordCs_interior hInt) hP := by
  have hzero : ∀ x ∈ Sanctions.I, E.toChordCs.toParams.dynamicEquilibriumRule Eq x = 0 := by
    rcases hrule with hint | hz
    · exact absurd ⟨Eq, a₀, a₁, S₂, S₁, S₀, ⟨hpol, hlt, hV, hQ, hint⟩⟩
        (lq_affineQuad_empty_below_betaR E hF hn hSR hβ)
    · exact hz
  obtain ⟨h1, h2, h3⟩ := E.toChordCs.relief_equilibrium_of_zero_rule (E.toChordCs_interior hInt)
    hP E.toPlacableEconomyF.toChord_zeroSanctionNeutral Eq hzero
  exact ⟨hzero, h1, h2, h3⟩

/-- **A defiance equilibrium in the class sits on the defiance Riccati pair.** If a class
equilibrium has full defiance, its realised slope `e₁ ∈ (−1, 1)` and curvature `S₂` solve
`Q·e₁ = r + 2β_Sδ(1−δ)S₂` and `S₂(1 − β_S(1−δ)² + β_Sδ²e₁²) = (q/2)e₁²`, and
`β_ind(S₂) ≤ β_T`: the defiance end of the window is `β_D = β_ind(S₂ᴰ)`.

Scope: affine-policy equilibria only (not general); approved hypotheses 5–6. -/
theorem lq_affineQuad_defiance (E : PlacableEconomyFcs) (hF : E.F = affineF E.δ)
    (hn : E.n = 0) (hSR : E.StageRelief)
    (Eq : E.toChordCs.toParams.FeedbackStackelbergEquilibriumTop) {a₀ a₁ S₂ S₁ S₀ : ℝ}
    (hC : AffineQuadClass E.toChordCs.toParams Eq E.q a₀ a₁ S₂ S₁ S₀)
    (hdef : ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    ∃ e₁ : ℝ, -1 < e₁ ∧ e₁ < 1 ∧
      (E.q - 2 * E.βS * E.δ ^ 2 * S₂) * e₁ = E.r + 2 * E.βS * E.δ * (1 - E.δ) * S₂ ∧
      S₂ * (1 - E.βS * (1 - E.δ) ^ 2 + E.βS * E.δ ^ 2 * e₁ ^ 2) = E.q / 2 * e₁ ^ 2 ∧
      betaInd E.δ E.βS E.q E.k E.r E.ℓ E.c E.v S₂ ≤ E.βT := by
  have hUS : E.toChordCs.toParams.U_S = symU_S E.q E.u₀ E.k E.r E.w := rfl
  have hF' : E.toChordCs.toParams.F = affineF E.toChordCs.toParams.δ := hF
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_rfl⟩
  have ha₀ : a₀ = 0 := by have := hC.policy 0 h0I; rw [hdef 0 h0I] at this; linarith
  have ha₁ : a₁ = 0 := by have := hC.policy 1 h1I; rw [hdef 1 h1I] at this; linarith
  have hslope := slope_mem (w := E.w) hUS hF' Eq hC
  have hK2 := policy_slope (k := E.k) (r := E.r) Eq hC
  have hK1 := sender_curvature (w := E.w) hUS hF' Eq hC
  obtain ⟨-, -, -, h4, -, -⟩ := lq_affineQuad_classification E hF hn hSR Eq hC
  refine ⟨slope E.toChordCs.toParams E.q E.k E.r a₁ S₂, hslope.1, hslope.2, ?_, hK1, h4⟩
  have hK2' : E.k * a₁ = E.r + 2 * E.βS * E.δ * (1 - E.δ) * S₂
      - (E.q - 2 * E.βS * E.δ ^ 2 * S₂) * slope E.toChordCs.toParams E.q E.k E.r a₁ S₂ := hK2
  linear_combination hK2' - E.k * ha₁

/-! ## 5. Checks at the affine-window member -/

/-- `β_R = 36/197` at the affine-window member, reproducing `aw_zero_rule_iff`.

Scope: at the example economy only (not general). -/
theorem aw_betaR : betaR (1 / 2) 3 3 (1 / 2) 1 4 30 = 36 / 197 := by
  unfold betaR den netPain; norm_num

/-- `β_ind(S₂) = (36 + S₂)/197` at the affine-window member.

Scope: at the example economy only (not general). -/
theorem aw_betaInd (S₂ : ℝ) : betaInd (1 / 2) (1 / 2) 3 3 (1 / 2) 1 4 30 S₂ = (36 + S₂) / 197 := by
  unfold betaInd den netPain; ring

/-- `β_ind(12/701) = 25248/138097 = β₁`, the discount of the continuum `aw_continuum`.

Scope: at the example economy only (not general). -/
theorem aw_betaInd_β₁ : betaInd (1 / 2) (1 / 2) 3 3 (1 / 2) 1 4 30 (12 / 701) = awβ₁ := by
  rw [aw_betaInd]; unfold awβ₁; norm_num

/-- `β_ind((10 − 7√2)/2) = (82 − 7√2)/394 = β_D`, reproducing `aw_full_defiance_iff`.

Scope: at the example economy only (not general). -/
theorem aw_betaInd_defiance :
    betaInd (1 / 2) (1 / 2) 3 3 (1 / 2) 1 4 30 ((10 - 7 * Real.sqrt 2) / 2)
      = (82 - 7 * Real.sqrt 2) / 394 := by
  rw [aw_betaInd]; ring

/-- **The family theorem's hypotheses hold at the affine-window member**: the transition is
affine with rate `1/2`, `n = 0` and stage relief (`3 < 12`).

Scope: at the example economy only (not general). -/
theorem aw_lq_hypotheses (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (awBase b hb0 hb1).F = affineF (awBase b hb0 hb1).δ ∧ (awBase b hb0 hb1).n = 0 ∧
      (awBase b hb0 hb1).StageRelief := by
  refine ⟨rfl, rfl, ?_⟩
  unfold PlacableEconomyF.StageRelief
  norm_num [awBase, placableAffineCs, placableAffine]

/-- **The classification at the affine-window member.** Every class equilibrium at Target
discount `b` has `36/197 ≤ (36 + S₂)/197 ≤ b`; strict inequality forces full defiance, and
positive compliance at some state forces `b = (36 + S₂)/197`.

Scope: at the example economy only (not general); affine-policy equilibria only; approved
hypotheses 5–6. -/
theorem aw_affineQuad_classification {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}
    (Eq : (awParams b hb0 hb1).FeedbackStackelbergEquilibriumTop) {a₀ a₁ S₂ S₁ S₀ : ℝ}
    (hC : AffineQuadClass (awParams b hb0 hb1) Eq 3 a₀ a₁ S₂ S₁ S₀) :
    0 ≤ S₂ ∧ 36 / 197 ≤ (36 + S₂) / 197 ∧ (36 + S₂) / 197 ≤ b ∧
      ((36 + S₂) / 197 < b → ∀ x ∈ Sanctions.I, Eq.α x = 0) ∧
      ((∃ x ∈ Sanctions.I, 0 < Eq.α x) → b = (36 + S₂) / 197) := by
  obtain ⟨hF, hn, hSR⟩ := aw_lq_hypotheses b hb0 hb1
  obtain ⟨-, h1, h2, h3, h4, h5⟩ :=
    lq_affineQuad_classification (awBase b hb0 hb1) hF hn hSR Eq hC
  have eI : betaInd (awBase b hb0 hb1).δ (awBase b hb0 hb1).βS (awBase b hb0 hb1).q
      (awBase b hb0 hb1).k (awBase b hb0 hb1).r (awBase b hb0 hb1).ℓ (awBase b hb0 hb1).c
      (awBase b hb0 hb1).v S₂ = (36 + S₂) / 197 := aw_betaInd S₂
  have eR : betaR (awBase b hb0 hb1).δ (awBase b hb0 hb1).q (awBase b hb0 hb1).k
      (awBase b hb0 hb1).r (awBase b hb0 hb1).ℓ (awBase b hb0 hb1).c (awBase b hb0 hb1).v
      = 36 / 197 := aw_betaR
  have eb : (awBase b hb0 hb1).βT = b := rfl
  rw [eI, eR] at h2
  rw [eI, eb] at h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **A defiance equilibrium in the class at the member has curvature `(10 − 7√2)/2`**, so its
discount is at least `β_D = (82 − 7√2)/394`, as `aw_full_defiance_iff` states. The defiance
Riccati pair at the member is `(3 − S₂/4)e₁ = 1/2 + S₂/4`, `S₂(7 + e₁²) = 12e₁²`, whose only
root with `|e₁| < 1` is `e₁ = 3 − 2√2`.

Scope: at the example economy only (not general); affine-policy equilibria only; approved
hypotheses 5–6. -/
theorem aw_affineQuad_defiance {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}
    (Eq : (awParams b hb0 hb1).FeedbackStackelbergEquilibriumTop) {a₀ a₁ S₂ S₁ S₀ : ℝ}
    (hC : AffineQuadClass (awParams b hb0 hb1) Eq 3 a₀ a₁ S₂ S₁ S₀)
    (hdef : ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    S₂ = (10 - 7 * Real.sqrt 2) / 2 ∧ (82 - 7 * Real.sqrt 2) / 394 ≤ b := by
  obtain ⟨hF, hn, hSR⟩ := aw_lq_hypotheses b hb0 hb1
  obtain ⟨e, he0, he1, hK2, hK1, hβ⟩ :=
    lq_affineQuad_defiance (awBase b hb0 hb1) hF hn hSR Eq hC hdef
  have hK2' : (3 - 2 * (1 / 2) * (1 / 2) ^ 2 * S₂) * e
      = 1 / 2 + 2 * (1 / 2) * (1 / 2) * (1 - 1 / 2) * S₂ := hK2
  have hK1' : S₂ * (1 - 1 / 2 * (1 - 1 / 2) ^ 2 + 1 / 2 * (1 / 2) ^ 2 * e ^ 2)
      = 3 / 2 * e ^ 2 := hK1
  have hA : S₂ * (7 + e ^ 2) = 12 * e ^ 2 := by linear_combination 8 * hK1'
  have hB : S₂ * (1 + e) = 12 * e - 2 := by linear_combination -4 * hK2'
  have hquad : e ^ 2 - 6 * e + 1 = 0 := by
    linear_combination (-(1 + e) / 14) * hA + ((7 + e ^ 2) / 14) * hB
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hspos := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
  have hfac : (e - 3 + 2 * Real.sqrt 2) * (e - 3 - 2 * Real.sqrt 2) = 0 := by
    linear_combination hquad - 4 * hs
  have he : e = 3 - 2 * Real.sqrt 2 := by
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · exfalso; nlinarith
  have hS : S₂ = (10 - 7 * Real.sqrt 2) / 2 := by
    rw [he] at hB
    have hne : (4 - 2 * Real.sqrt 2) ≠ 0 := by intro h; nlinarith [hs]
    have hprod : (S₂ - (10 - 7 * Real.sqrt 2) / 2) * (4 - 2 * Real.sqrt 2) = 0 := by
      linear_combination hB - 7 * hs
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exact absurd h hne
  refine ⟨hS, ?_⟩
  have eI : betaInd (awBase b hb0 hb1).δ (awBase b hb0 hb1).βS (awBase b hb0 hb1).q
      (awBase b hb0 hb1).k (awBase b hb0 hb1).r (awBase b hb0 hb1).ℓ (awBase b hb0 hb1).c
      (awBase b hb0 hb1).v S₂ = (36 + S₂) / 197 := aw_betaInd S₂
  have eb : (awBase b hb0 hb1).βT = b := rfl
  rw [eI, eb, hS] at hβ
  linarith

/-- **The class is not empty**: every member of the continuum at `β₁` with `t < 4/9`
(`awEquilibrium`, `AffineWindowContinuum.lean`) lies in it, with `S₂ = 12/701`.

Scope: at the example economy only (not general); approved hypothesis 5 (non-vacuity). -/
theorem aw_affineQuadClass_awEquilibrium {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (4 / 9)) :
    AffineQuadClass awP₁ (awEquilibrium t ⟨ht.1, ht.2.le⟩) 3 t (287 / 4206) (12 / 701)
      (awκ t) (awAe t ^ 2 * (701 / 2100)) := by
  have hδ : awP₁.δ = 1 / 2 := rfl
  refine ⟨fun _ _ => rfl, fun x hx => ?_, fun _ => rfl, ?_, fun x hx => ?_⟩
  · change t + 287 / 4206 * x < 1
    nlinarith [ht.2, hx.2]
  · rw [aw_β_S, hδ]; norm_num
  · rw [aw_rule ⟨ht.1, ht.2.le⟩ hx]
    have := ht.1; have := ht.2; have := hx.1; have := hx.2
    constructor <;> nlinarith

/-- **The classification is consistent at `β₁`**: the class equilibria `awEquilibrium t`
(`t < 4/9`) have positive compliance, so the classification forces `β₁ = β_ind(12/701)`, which
holds (`aw_betaInd_β₁`).

Scope: at the example economy only (not general); approved hypotheses 5–6. -/
theorem aw_classification_at_β₁ {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (4 / 9)) :
    awβ₁ = (36 + 12 / 701) / 197 := by
  have hC := aw_affineQuadClass_awEquilibrium ht
  obtain ⟨-, -, -, -, h5⟩ := aw_affineQuad_classification _ hC
  refine h5 ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
  change 0 < t + 287 / 4206 * 1
  linarith [ht.1]

end

end AQClass
end Examples
end Sanctions
