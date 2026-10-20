import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic

/-!
# Argmax sensitivity under strong concavity

This file isolates a generic two-coordinate sensitivity estimate for a real-valued
argmax.  If changing either coordinate changes the objective difference at a
controlled rate, strong concavity converts that objective bound into a Lipschitz
bound for the selected maximizer.

The result is independent of the sanctions model: the two coordinates may be any
pseudometric spaces, and the feasible action set may be any convex subset of `ℝ`.
-/

namespace Sanctions

open Set

private theorem strongConcaveOn_deviation_at_maximizer
    {f : ℝ → ℝ} {A : Set ℝ} {c : ℝ}
    (hA : Convex ℝ A) (hf : StrongConcaveOn A c f)
    {aMax a : ℝ} (haMax : aMax ∈ A) (ha : a ∈ A)
    (hmax : IsMaxOn f A aMax) :
    f a ≤ f aMax - (c / 4) * (aMax - a) ^ 2 := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hsum : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  unfold StrongConcaveOn UniformConcaveOn at hf
  have hsc := hf.2 haMax ha hhalf hhalf hsum
  dsimp only at hsc
  have hnorm : ‖aMax - a‖ ^ 2 = (aMax - a) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm] at hsc
  have hmidMem : (1 / 2 : ℝ) • aMax + (1 / 2 : ℝ) • a ∈ A :=
    hA haMax ha hhalf hhalf hsum
  have hmidMax : f ((1 / 2 : ℝ) • aMax + (1 / 2 : ℝ) • a) ≤ f aMax :=
    hmax hmidMem
  simp only [smul_eq_mul] at hsc hmidMax
  have hchain := le_trans hsc hmidMax
  have hcompute :
      (1 / 2 : ℝ) * (1 / 2) * (c / 2 * (aMax - a) ^ 2)
        = c / 8 * (aMax - a) ^ 2 := by
    ring
  rw [hcompute] at hchain
  nlinarith

/-- **Two-coordinate argmax sensitivity.** Let an objective depend on two
pseudometric coordinates. If the objectives before and after a coordinate change
are strongly concave with the same positive modulus, their selected actions are
maximizers on the same convex feasible set, and the change in the objective
difference between those two actions is bounded by the sum of the two coordinate
distances, then the selected action changes by at most `2 / c` times that sum. -/
theorem argmax_lipschitz_two_coordinates_of_strongConcave
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (objective : X → Y → ℝ → ℝ) (select : X → Y → ℝ)
    {A : Set ℝ} {c Lx Ly : ℝ}
    (hc : 0 < c) (hLx : 0 ≤ Lx) (hLy : 0 ≤ Ly)
    (hA : Convex ℝ A) (x x' : X) (y y' : Y)
    (hsc : StrongConcaveOn A c (objective x y))
    (hsc' : StrongConcaveOn A c (objective x' y'))
    (hmem : select x y ∈ A) (hmem' : select x' y' ∈ A)
    (hmax : IsMaxOn (objective x y) A (select x y))
    (hmax' : IsMaxOn (objective x' y') A (select x' y'))
    (hdiff :
      |(objective x y (select x y) - objective x' y' (select x y))
        - (objective x y (select x' y') - objective x' y' (select x' y'))|
        ≤ (Lx * dist x x' + Ly * dist y y') * |select x y - select x' y'|) :
    |select x y - select x' y'|
      ≤ (2 / c) * (Lx * dist x x' + Ly * dist y y') := by
  have hL : 0 ≤ Lx * dist x x' + Ly * dist y y' :=
    add_nonneg (mul_nonneg hLx dist_nonneg) (mul_nonneg hLy dist_nonneg)
  have hdev :
      objective x y (select x' y')
        ≤ objective x y (select x y) - (c / 4) * (select x y - select x' y') ^ 2 :=
    strongConcaveOn_deviation_at_maximizer hA hsc hmem hmem' hmax
  have hdev' :
      objective x' y' (select x y)
        ≤ objective x' y' (select x' y')
          - (c / 4) * (select x' y' - select x y) ^ 2 :=
    strongConcaveOn_deviation_at_maximizer hA hsc' hmem' hmem hmax'
  have hsq :
      (select x' y' - select x y) ^ 2 = (select x y - select x' y') ^ 2 := by
    ring
  rw [hsq] at hdev'
  have hkey :
      (c / 2) * (select x y - select x' y') ^ 2
        ≤ (objective x y (select x y) - objective x' y' (select x y))
          - (objective x y (select x' y') - objective x' y' (select x' y')) := by
    linarith
  have hbound :
      (c / 2) * (select x y - select x' y') ^ 2
        ≤ (Lx * dist x x' + Ly * dist y y') * |select x y - select x' y'| :=
    le_trans hkey (le_trans (le_abs_self _) hdiff)
  have habsSq :
      (select x y - select x' y') ^ 2 = |select x y - select x' y'| ^ 2 :=
    (sq_abs _).symm
  rw [habsSq] at hbound
  rcases (abs_nonneg (select x y - select x' y')).lt_or_eq with hpos | hzero
  · rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith
  · rw [← hzero]
    exact mul_nonneg (by positivity) hL

/-- **Two-coordinate argmax sensitivity from quadratic growth.**

This is the assumption-minimal form needed by local carrier arguments.  Each
selected action need only satisfy quadratic growth with a common positive
coefficient `q`; global strong concavity is not required.  A product-form
objective-difference estimate then bounds the distance between the selected
actions by the coordinate perturbation divided by `2 * q`.

The theorem is entirely parametric.  Concrete coefficients belong only in a
witness corollary obtained by substituting derived values for `q`, `Lx`, and
`Ly`. -/
theorem argmax_lipschitz_two_coordinates_of_quadraticGrowth
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (objective : X → Y → ℝ → ℝ) (select : X → Y → ℝ)
    {A : Set ℝ} {q Lx Ly : ℝ}
    (hq : 0 < q) (hLx : 0 ≤ Lx) (hLy : 0 ≤ Ly)
    (x x' : X) (y y' : Y)
    (hmem : select x y ∈ A) (hmem' : select x' y' ∈ A)
    (growth : ∀ a ∈ A,
      q * (a - select x y) ^ 2
        ≤ objective x y (select x y) - objective x y a)
    (growth' : ∀ a ∈ A,
      q * (a - select x' y') ^ 2
        ≤ objective x' y' (select x' y') - objective x' y' a)
    (hdiff :
      |(objective x y (select x y) - objective x' y' (select x y))
          - (objective x y (select x' y') - objective x' y' (select x' y'))|
        ≤ (Lx * dist x x' + Ly * dist y y') *
          |select x y - select x' y'|) :
    |select x y - select x' y'|
      ≤ (Lx * dist x x' + Ly * dist y y') / (2 * q) := by
  let a := select x y
  let a' := select x' y'
  let L := Lx * dist x x' + Ly * dist y y'
  have hg := growth a' hmem'
  have hg' := growth' a hmem
  have hchord :
      2 * q * (a - a') ^ 2
        ≤ (objective x y a - objective x' y' a)
          - (objective x y a' - objective x' y' a') := by
    dsimp only [a, a'] at hg hg' ⊢
    nlinarith [sq_nonneg (select x y - select x' y')]
  have hupper :
      (objective x y a - objective x' y' a)
          - (objective x y a' - objective x' y' a')
        ≤ L * |a - a'| := by
    dsimp only [a, a', L] at hdiff ⊢
    exact le_trans (le_abs_self _) hdiff
  have hsq : 2 * q * |a - a'| ^ 2 ≤ L * |a - a'| := by
    rw [sq_abs]
    exact le_trans hchord hupper
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hden : 0 < 2 * q := by positivity
  by_cases hzero : |a - a'| = 0
  · rw [hzero]
    exact div_nonneg hL (le_of_lt hden)
  · have hpos : 0 < |a - a'| :=
      lt_of_le_of_ne (abs_nonneg _) (Ne.symm hzero)
    have hmul : (2 * q) * |a - a'| ≤ L := by
      nlinarith
    rw [le_div_iff₀ hden]
    simpa [mul_comm] using hmul

/-- **Two-coordinate argmax sensitivity from coordinatewise objective
geometry.**

This is the symbolic replacement for witness-specific two-coordinate selector
bounds.  The two objective coordinates are changed one at a time.  If each
coordinate change has an action-chord modulus, the selected policy has the
derived moduli

`Lx / (2 * q)` and `Ly / (2 * q)`,

where `q` is the common quadratic-growth coefficient.  No numerical policy
coefficient is assumed by the theorem. -/
theorem argmax_lipschitz_two_coordinates_of_quadraticGrowth_of_coordinate_geometry
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (objective : X → Y → ℝ → ℝ) (select : X → Y → ℝ)
    {A : Set ℝ} {q Lx Ly : ℝ}
    (hq : 0 < q) (hLx : 0 ≤ Lx) (hLy : 0 ≤ Ly)
    (x x' : X) (y y' : Y)
    (hmem : select x y ∈ A) (hmem' : select x' y' ∈ A)
    (growth : ∀ a ∈ A,
      q * (a - select x y) ^ 2
        ≤ objective x y (select x y) - objective x y a)
    (growth' : ∀ a ∈ A,
      q * (a - select x' y') ^ 2
        ≤ objective x' y' (select x' y') - objective x' y' a)
    (hdiff_x :
      |(objective x y (select x y) - objective x' y (select x y))
          - (objective x y (select x' y') - objective x' y (select x' y'))|
        ≤ Lx * dist x x' * |select x y - select x' y'|)
    (hdiff_y :
      |(objective x' y (select x y) - objective x' y' (select x y))
          - (objective x' y (select x' y') - objective x' y' (select x' y'))|
        ≤ Ly * dist y y' * |select x y - select x' y'|) :
    |select x y - select x' y'|
      ≤ (Lx / (2 * q)) * dist x x' + (Ly / (2 * q)) * dist y y' := by
  have hdiff :
      |(objective x y (select x y) - objective x' y' (select x y))
          - (objective x y (select x' y') - objective x' y' (select x' y'))|
        ≤ (Lx * dist x x' + Ly * dist y y') *
          |select x y - select x' y'| := by
    calc
      |(objective x y (select x y) - objective x' y' (select x y))
          - (objective x y (select x' y') - objective x' y' (select x' y'))|
          =
          |((objective x y (select x y) - objective x' y (select x y))
              - (objective x y (select x' y') - objective x' y (select x' y')))
            + ((objective x' y (select x y) - objective x' y' (select x y))
              - (objective x' y (select x' y') - objective x' y' (select x' y')))| := by
            congr 1
            ring
      _ ≤
          |(objective x y (select x y) - objective x' y (select x y))
              - (objective x y (select x' y') - objective x' y (select x' y'))|
            + |(objective x' y (select x y) - objective x' y' (select x y))
              - (objective x' y (select x' y') - objective x' y' (select x' y'))| :=
            abs_add_le _ _
      _ ≤ Lx * dist x x' * |select x y - select x' y'|
            + Ly * dist y y' * |select x y - select x' y'| :=
            add_le_add hdiff_x hdiff_y
      _ = (Lx * dist x x' + Ly * dist y y') *
            |select x y - select x' y'| := by ring
  calc
    |select x y - select x' y'|
        ≤ (Lx * dist x x' + Ly * dist y y') / (2 * q) :=
      argmax_lipschitz_two_coordinates_of_quadraticGrowth
        objective select hq hLx hLy x x' y y' hmem hmem'
        growth growth' hdiff
    _ = (Lx / (2 * q)) * dist x x' + (Ly / (2 * q)) * dist y y' := by
      ring


/-! ## How far a maximizer moves when the loss it is centred on moves

A separate sensitivity question from the one above. Consider a family of
objectives `f m s = g (s - m) + W s`, indexed by a *centre* `m`. The first term
is a loss that depends only on the displacement `s - m`, so moving `m`
translates it rigidly; the second is a fixed perturbation. Write `d m` for a
maximizer. The question is not whether `d` moves with `m` — under a concave loss
it does — but **how far it moves relative to the shift itself**, because a
downstream comparison may read the *gap* `d m - m` rather than the level.

Three **sufficient** conditions are proved below, each with its own selection
premise. None of them is a characterization: nothing here says that only a
concave `W` can shrink the gap, and no converse is proved in either direction.

* `W` concave — the maximizer moves by **at most** the shift, so the gap
  `d m - m` does not grow in `m`;
* `W` convex — it moves by **at least** the shift, so the gap does not shrink;
* `W` both — it moves by **exactly** the shift and the gap is constant. This is
  a knife edge in the sufficient direction only: a `W` that is neither concave
  nor convex may perfectly well leave some particular pair of gaps equal.

### The one lemma all three run on

The whole section rests on `shift_tight`, and it is worth stating separately
what that lemma does and does not use. Translate each maximizer by the shift and
offer it as a candidate in the *other* problem. Because `g` reads only the
displacement, the two loss terms appearing on the two sides are the **same two
numbers**, so they cancel exactly and optimality alone — with no curvature
whatever — bounds a sum of four `W` values from one side.

Curvature enters only to supply the *reverse* of that sum inequality. Once both
directions hold the sum is an equality, which forces each of the two optimality
inequalities to be tight individually, and a tight inequality says precisely that
the translated point is a maximizer of the other problem too. So the conclusion
of `shift_tight` is symmetric: **both** translated points are optimal, and a
selection premise on either side then pins the movement.

That symmetry is why one lemma covers concavity, convexity and the affine case:
they differ only in which sum inequality is available and which of the two
resulting optimality facts is then consumed.

No derivative, no strong concavity, no continuity and no compactness is used
anywhere in the section. -/

/-- **The exchange step.** If the curvature of `W` supplies the displayed sum
inequality, then *both* shift-translated maximizers are optimal in the other
problem.

The hypothesis `hcurv` is the only place curvature is used, and it is stated as
a bare inequality rather than as `ConcaveOn` / `ConvexOn` precisely so that the
three routes below can supply it in three different ways. -/
private theorem shift_tight
    {g W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (h₁ : IsMaxOn (fun s => g (s - m₁) + W s) A d₁)
    (h₂ : IsMaxOn (fun s => g (s - m₂) + W s) A d₂)
    (hcurv : W d₁ + W d₂ ≤ W (d₁ + (m₂ - m₁)) + W (d₂ - (m₂ - m₁))) :
    IsMaxOn (fun s => g (s - m₁) + W s) A (d₂ - (m₂ - m₁)) ∧
      IsMaxOn (fun s => g (s - m₂) + W s) A (d₁ + (m₂ - m₁)) := by
  -- Optimality at the higher centre, against the up-translated lower maximizer.
  have hA : g (d₁ - m₁) + W (d₁ + (m₂ - m₁)) ≤ g (d₂ - m₂) + W d₂ := by
    have h : g (d₁ + (m₂ - m₁) - m₂) + W (d₁ + (m₂ - m₁))
        ≤ g (d₂ - m₂) + W d₂ := h₂ hsh₁
    rwa [show d₁ + (m₂ - m₁) - m₂ = d₁ - m₁ from by ring] at h
  -- Optimality at the lower centre, against the down-translated higher one.
  have hB : g (d₂ - m₂) + W (d₂ - (m₂ - m₁)) ≤ g (d₁ - m₁) + W d₁ := by
    have h : g (d₂ - (m₂ - m₁) - m₁) + W (d₂ - (m₂ - m₁))
        ≤ g (d₁ - m₁) + W d₁ := h₁ hsh₂
    rwa [show d₂ - (m₂ - m₁) - m₁ = d₂ - m₂ from by ring] at h
  -- `hA + hB` bounds the `W`-sum one way; `hcurv` bounds it the other. So both
  -- are equalities, and each says a translated point attains the other maximum.
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have hy1 : g (y - m₁) + W y ≤ g (d₁ - m₁) + W d₁ := h₁ hy
    change g (y - m₁) + W y ≤ g (d₂ - (m₂ - m₁) - m₁) + W (d₂ - (m₂ - m₁))
    rw [show d₂ - (m₂ - m₁) - m₁ = d₂ - m₂ from by ring]
    linarith
  · have hy2 : g (y - m₂) + W y ≤ g (d₂ - m₂) + W d₂ := h₂ hy
    change g (y - m₂) + W y ≤ g (d₁ + (m₂ - m₁) - m₂) + W (d₁ + (m₂ - m₁))
    rw [show d₁ + (m₂ - m₁) - m₂ = d₁ - m₁ from by ring]
    linarith

/-- Concavity supplies `shift_tight`'s sum inequality when the maximizers move
*at least* as far as the centres: the two translated points then lie inside
`[d₁, d₂]`, as a matched pair of convex combinations with swapped weights. -/
private theorem concave_shift_sum
    {W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hW : ConcaveOn ℝ A W) (hd₁ : d₁ ∈ A) (hd₂ : d₂ ∈ A)
    (hδ : 0 ≤ m₂ - m₁) (hle : m₂ - m₁ ≤ d₂ - d₁) :
    W d₁ + W d₂ ≤ W (d₁ + (m₂ - m₁)) + W (d₂ - (m₂ - m₁)) := by
  rcases eq_or_lt_of_le (hδ.trans hle) with hΔ | hΔ
  · -- Degenerate: no room to move, so the shift is zero and both sides agree.
    have h0 : m₂ - m₁ = 0 := le_antisymm (by linarith) hδ
    rw [h0]; simp
  · set lam : ℝ := (m₂ - m₁) / (d₂ - d₁) with hlam
    have hlam0 : 0 ≤ lam := div_nonneg hδ hΔ.le
    have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hΔ]; linarith
    have hne : d₂ - d₁ ≠ 0 := ne_of_gt hΔ
    have e1 : (1 - lam) * d₁ + lam * d₂ = d₁ + (m₂ - m₁) := by
      rw [hlam]; field_simp; ring
    have e2 : lam * d₁ + (1 - lam) * d₂ = d₂ - (m₂ - m₁) := by
      rw [hlam]; field_simp; ring
    have hc1 : (1 - lam) * W d₁ + lam * W d₂ ≤ W (d₁ + (m₂ - m₁)) := by
      have h := hW.2 hd₁ hd₂ (by linarith : (0:ℝ) ≤ 1 - lam) hlam0 (by ring)
      simp only [smul_eq_mul] at h
      rwa [e1] at h
    have hc2 : lam * W d₁ + (1 - lam) * W d₂ ≤ W (d₂ - (m₂ - m₁)) := by
      have h := hW.2 hd₁ hd₂ hlam0 (by linarith : (0:ℝ) ≤ 1 - lam) (by ring)
      simp only [smul_eq_mul] at h
      rwa [e2] at h
    linarith

/-- Convexity supplies the same sum inequality in the opposite regime: when the
maximizers move *at most* as far as the centres, it is `d₁` and `d₂` that lie
inside the translated pair, and convexity bounds them from above. -/
private theorem convex_shift_sum
    {W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hW : ConvexOn ℝ A W)
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (hδ : 0 ≤ m₂ - m₁) (hge : d₂ - d₁ ≤ m₂ - m₁) :
    W d₁ + W d₂ ≤ W (d₁ + (m₂ - m₁)) + W (d₂ - (m₂ - m₁)) := by
  -- The translated pair spans a width `2δ - Δ`, which is nonnegative here.
  rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ 2 * (m₂ - m₁) - (d₂ - d₁))
    with hw | hw
  · -- Degenerate: zero width forces a zero shift, and both sides agree.
    have h0 : m₂ - m₁ = 0 := le_antisymm (by linarith) hδ
    rw [h0]; simp
  · set t : ℝ := (m₂ - m₁ - (d₂ - d₁)) / (2 * (m₂ - m₁) - (d₂ - d₁)) with ht
    have hne : 2 * (m₂ - m₁) - (d₂ - d₁) ≠ 0 := ne_of_gt hw
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hw.le
    have ht1 : 0 ≤ 1 - t := by
      rw [ht, sub_nonneg, div_le_one hw]; linarith
    -- Clearing the denominator once; both weight identities are then linear.
    have htw : t * (2 * (m₂ - m₁) - (d₂ - d₁)) = m₂ - m₁ - (d₂ - d₁) := by
      rw [ht]; exact div_mul_cancel₀ _ hne
    have e1 : (1 - t) * (d₂ - (m₂ - m₁)) + t * (d₁ + (m₂ - m₁)) = d₁ := by
      linear_combination htw
    have e2 : t * (d₂ - (m₂ - m₁)) + (1 - t) * (d₁ + (m₂ - m₁)) = d₂ := by
      linear_combination -htw
    have hc1 : W d₁
        ≤ (1 - t) * W (d₂ - (m₂ - m₁)) + t * W (d₁ + (m₂ - m₁)) := by
      have h := hW.2 hsh₂ hsh₁ ht1 ht0 (by ring)
      simp only [smul_eq_mul] at h
      rwa [e1] at h
    have hc2 : W d₂
        ≤ t * W (d₂ - (m₂ - m₁)) + (1 - t) * W (d₁ + (m₂ - m₁)) := by
      have h := hW.2 hsh₂ hsh₁ ht0 ht1 (by ring)
      simp only [smul_eq_mul] at h
      rwa [e2] at h
    linarith

/-- **A concave perturbation makes the maximizer move by at most the shift** —
under a greatest-selection premise at the *lower* centre.

`g` is a loss read off the displacement `s - m`, so `m` translates it rigidly;
`W` is a fixed concave perturbation. Raising the centre from `m₁` to `m₂` then
moves the maximizer by no more than `m₂ - m₁`.

`hgreat₁` says `d₁` is the greatest maximizer at the lower centre. That is a
strictly weaker demand than uniqueness, and it is the form an extremal-selector
architecture supplies for free. The two membership hypotheses say the translated
candidates stay feasible; on an interval they hold whenever the translate does
not leave it.

This is a **sufficient** condition. It does not say that a gap which fails to
grow forces `W` to be concave. -/
theorem argmax_shift_le_of_concaveOn_of_lowerGreatest
    {g W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hW : ConcaveOn ℝ A W)
    (hd₁ : d₁ ∈ A) (hd₂ : d₂ ∈ A)
    (hm : m₁ ≤ m₂)
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (h₁ : IsMaxOn (fun s => g (s - m₁) + W s) A d₁)
    (h₂ : IsMaxOn (fun s => g (s - m₂) + W s) A d₂)
    (hgreat₁ : ∀ y ∈ A, IsMaxOn (fun s => g (s - m₁) + W s) A y → y ≤ d₁) :
    d₂ - d₁ ≤ m₂ - m₁ := by
  by_contra hcon0
  have hcon : m₂ - m₁ < d₂ - d₁ := not_le.mp hcon0
  have hsum := concave_shift_sum hW hd₁ hd₂ (by linarith) hcon.le
  have hmax := (shift_tight hsh₁ hsh₂ h₁ h₂ hsum).1
  have := hgreat₁ _ hsh₂ hmax
  linarith

/-- **A convex perturbation makes the maximizer move by at least the shift** —
under a greatest-selection premise at the *higher* centre.

The exact mirror of `argmax_shift_le_of_concaveOn_of_lowerGreatest`, and the
direction a comparison needs when it wants the gap `d - m` **not to shrink** as
the centre rises.

Note the absent hypotheses: `d₁ ∈ A` and `d₂ ∈ A` are not required, because the
convexity step is applied at the two *translated* points rather than at the
maximizers themselves.

This is a **sufficient** condition; no converse is claimed. -/
theorem argmax_shift_ge_of_convexOn_of_upperGreatest
    {g W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hW : ConvexOn ℝ A W)
    (hm : m₁ ≤ m₂)
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (h₁ : IsMaxOn (fun s => g (s - m₁) + W s) A d₁)
    (h₂ : IsMaxOn (fun s => g (s - m₂) + W s) A d₂)
    (hgreat₂ : ∀ y ∈ A, IsMaxOn (fun s => g (s - m₂) + W s) A y → y ≤ d₂) :
    m₂ - m₁ ≤ d₂ - d₁ := by
  by_contra hcon0
  have hcon : d₂ - d₁ < m₂ - m₁ := not_le.mp hcon0
  have hsum := convex_shift_sum hW hsh₁ hsh₂ (by linarith) hcon.le
  have hmax := (shift_tight hsh₁ hsh₂ h₁ h₂ hsum).2
  have := hgreat₂ _ hsh₁ hmax
  linarith

/-- **A perturbation that is both concave and convex moves the maximizer by
exactly the shift.**

The knife edge, in the sufficient direction only: an affine `W` leaves the gap
`d - m` unchanged. It is emphatically *not* a characterization — a `W` that is
neither concave nor convex may still leave some particular pair of gaps equal,
and nothing here rules that out. -/
theorem argmax_shift_eq_of_concave_convex_of_greatest
    {g W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hWc : ConcaveOn ℝ A W) (hWv : ConvexOn ℝ A W)
    (hd₁ : d₁ ∈ A) (hd₂ : d₂ ∈ A)
    (hm : m₁ ≤ m₂)
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (h₁ : IsMaxOn (fun s => g (s - m₁) + W s) A d₁)
    (h₂ : IsMaxOn (fun s => g (s - m₂) + W s) A d₂)
    (hgreat₁ : ∀ y ∈ A, IsMaxOn (fun s => g (s - m₁) + W s) A y → y ≤ d₁)
    (hgreat₂ : ∀ y ∈ A, IsMaxOn (fun s => g (s - m₂) + W s) A y → y ≤ d₂) :
    d₂ - d₁ = m₂ - m₁ :=
  le_antisymm
    (argmax_shift_le_of_concaveOn_of_lowerGreatest hWc hd₁ hd₂ hm hsh₁ hsh₂
      h₁ h₂ hgreat₁)
    (argmax_shift_ge_of_convexOn_of_upperGreatest hWv hm hsh₁ hsh₂ h₁ h₂ hgreat₂)

/-- **The uniqueness variant of the concave theorem.**

Kept because uniqueness at the higher centre is sometimes the premise in hand —
strict concavity of that objective delivers it — and it is not implied by
greatestness at the lower one. Same conclusion as
`argmax_shift_le_of_concaveOn_of_lowerGreatest`, reached through the other half
of `shift_tight`. -/
theorem argmax_shift_le_of_concaveOn
    {g W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hW : ConcaveOn ℝ A W)
    (hd₁ : d₁ ∈ A) (hd₂ : d₂ ∈ A)
    (hm : m₁ ≤ m₂)
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (h₁ : IsMaxOn (fun s => g (s - m₁) + W s) A d₁)
    (h₂ : IsMaxOn (fun s => g (s - m₂) + W s) A d₂)
    (huniq₂ : ∀ s ∈ A, IsMaxOn (fun s' => g (s' - m₂) + W s') A s → s = d₂) :
    d₂ - d₁ ≤ m₂ - m₁ := by
  by_contra hcon0
  have hcon : m₂ - m₁ < d₂ - d₁ := not_le.mp hcon0
  have hsum := concave_shift_sum hW hd₁ hd₂ (by linarith) hcon.le
  have hmax := (shift_tight hsh₁ hsh₂ h₁ h₂ hsum).2
  have hid : d₁ + (m₂ - m₁) = d₂ := huniq₂ _ hsh₁ hmax
  linarith

/-! ### Translated chords, and why they are the right primitive

The three results above are stated with `ConcaveOn` / `ConvexOn`, and that is
more than any of their proofs consume. Each one applies its curvature
hypothesis exactly **once**, at exactly **four** points, and always in the same
shape: a chord of one fixed length, compared against the same chord translated
along the axis.

Naming that inequality directly has three payoffs.

* It is what the proof actually uses, so the hypothesis stops over-stating.
* It composes with the transition. What a downstream application needs is
  curvature of a *composite* `s ↦ V (F x s)`, and requiring increasing chords of
  the composite is genuinely weaker than convexity of `V`: it constrains `V` only
  on the states `F x ·` can actually produce, and equal steps in `s` need not be
  equal steps in `F` when `F x ·` is nonlinear.
* It is an order condition, not a curvature one, so it sits in the same idiom as
  the single-crossing machinery the rest of this development runs on.

**What this is and is not a weakening of.** Imposed on *every* chord, as it is
below, the condition is equivalent to convexity whenever `A` is an interval and
`W` is continuous: the case `u = a`, `v = h = (b-a)/2` gives midpoint convexity,
and Sierpiński's theorem closes it. So at any application with an interval action
set and a continuous perturbation — which is the sanctions case — the chord form
and `ConvexOn` say the same thing, and it would be wrong to present the chord
form as a weaker hypothesis there.

Two things it *is*. It does not bundle `Convex ℝ A`, so these theorems reach
action sets that are not intervals, where the two conditions genuinely differ.
And it names exactly the inequality the proofs consume, which is what makes the
next weakening visible: a version quantifying only over the chords a particular
comparison generates would be strictly weaker than convexity even on an
interval. That version is **not** implemented here — the definitions below
quantify over all chords in `A`, and `A` is also the set the maximization runs
over, so a caller cannot shrink it.

The converse direction is not proved in this development. Mathlib carries no
midpoint-convexity theorem at the pinned revision, so it would require the
dyadic density argument from scratch; the cost was judged not worth paying for a
fact that is only used to describe the hypothesis, never to discharge it. -/

/-- **Increasing translated chords.** The increment of `W` across a chord of
fixed length does not fall as the chord is translated to the right. For a
continuous function on an interval this is equivalent to convexity; as stated,
on an arbitrary `A`, it is exactly the family of four-point inequalities. -/
def IncreasingChordsOn (W : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ ⦃u v h : ℝ⦄, u ∈ A → v ∈ A → u + h ∈ A → v + h ∈ A → u ≤ v → 0 ≤ h →
    W (u + h) - W u ≤ W (v + h) - W v

/-- **Decreasing translated chords.** The mirror image: the increment across a
chord of fixed length does not rise as the chord moves right. Equivalent to
concavity in the continuous-on-an-interval regime. -/
def DecreasingChordsOn (W : ℝ → ℝ) (A : Set ℝ) : Prop :=
  ∀ ⦃u v h : ℝ⦄, u ∈ A → v ∈ A → u + h ∈ A → v + h ∈ A → u ≤ v → 0 ≤ h →
    W (v + h) - W v ≤ W (u + h) - W u

/-- The two translated points are convex combinations of the two chord endpoints
with the *same* pair of weights, swapped — which is why one curvature
application settles both at once. -/
private theorem chord_weights {u v h : ℝ} (huv : u ≤ v) (hh : 0 ≤ h)
    (hpos : 0 < v + h - u) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧
      (1 - lam) * u + lam * (v + h) = u + h ∧
      lam * u + (1 - lam) * (v + h) = v := by
  refine ⟨h / (v + h - u), div_nonneg hh hpos.le, ?_, ?_, ?_⟩
  · rw [div_le_one hpos]; linarith
  · field_simp; ring
  · field_simp; ring

/-- Convexity gives increasing translated chords. -/
theorem ConvexOn.increasingChordsOn {W : ℝ → ℝ} {A : Set ℝ}
    (hW : ConvexOn ℝ A W) : IncreasingChordsOn W A := by
  intro u v h hu hv huh hvh huv hh
  rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ v + h - u) with hz | hpos
  · -- Degenerate: both chords are the same single point.
    have h0 : h = 0 := le_antisymm (by linarith) hh
    have h1 : u = v := by linarith
    subst h0; subst h1; simp
  · obtain ⟨lam, hlam0, hlam1, e1, e2⟩ := chord_weights huv hh hpos
    have hc1 : W (u + h) ≤ (1 - lam) * W u + lam * W (v + h) := by
      have h := hW.2 hu hvh (by linarith : (0:ℝ) ≤ 1 - lam) hlam0 (by ring)
      simp only [smul_eq_mul] at h
      rwa [e1] at h
    have hc2 : W v ≤ lam * W u + (1 - lam) * W (v + h) := by
      have h := hW.2 hu hvh hlam0 (by linarith : (0:ℝ) ≤ 1 - lam) (by ring)
      simp only [smul_eq_mul] at h
      rwa [e2] at h
    linarith

/-- Concavity gives decreasing translated chords. -/
theorem ConcaveOn.decreasingChordsOn {W : ℝ → ℝ} {A : Set ℝ}
    (hW : ConcaveOn ℝ A W) : DecreasingChordsOn W A := by
  intro u v h hu hv huh hvh huv hh
  rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ v + h - u) with hz | hpos
  · have h0 : h = 0 := le_antisymm (by linarith) hh
    have h1 : u = v := by linarith
    subst h0; subst h1; simp
  · obtain ⟨lam, hlam0, hlam1, e1, e2⟩ := chord_weights huv hh hpos
    have hc1 : (1 - lam) * W u + lam * W (v + h) ≤ W (u + h) := by
      have h := hW.2 hu hvh (by linarith : (0:ℝ) ≤ 1 - lam) hlam0 (by ring)
      simp only [smul_eq_mul] at h
      rwa [e1] at h
    have hc2 : lam * W u + (1 - lam) * W (v + h) ≤ W v := by
      have h := hW.2 hu hvh hlam0 (by linarith : (0:ℝ) ≤ 1 - lam) (by ring)
      simp only [smul_eq_mul] at h
      rwa [e2] at h
    linarith

/-- **The maximizer moves by at most the shift, from decreasing chords alone.**

The chord form of `argmax_shift_le_of_concaveOn_of_lowerGreatest`, and the
version that states what the proof consumes. Concavity is one way to supply
`hW`; it is not the only one, and it is not needed away from the four points the
argument visits. -/
theorem argmax_shift_le_of_decreasingChords_of_lowerGreatest
    {g W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hW : DecreasingChordsOn W A)
    (hd₁ : d₁ ∈ A) (hd₂ : d₂ ∈ A)
    (hm : m₁ ≤ m₂)
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (h₁ : IsMaxOn (fun s => g (s - m₁) + W s) A d₁)
    (h₂ : IsMaxOn (fun s => g (s - m₂) + W s) A d₂)
    (hgreat₁ : ∀ y ∈ A, IsMaxOn (fun s => g (s - m₁) + W s) A y → y ≤ d₁) :
    d₂ - d₁ ≤ m₂ - m₁ := by
  by_contra hcon0
  have hcon : m₂ - m₁ < d₂ - d₁ := not_le.mp hcon0
  -- The refuted case puts `d₁` to the left of `d₂ - (m₂ - m₁)`, so the two
  -- length-`(m₂ - m₁)` chords are `[d₁, d₁ + (m₂-m₁)]` and `[d₂ - (m₂-m₁), d₂]`.
  have hcancel : d₂ - (m₂ - m₁) + (m₂ - m₁) = d₂ := by ring
  have hsum : W d₁ + W d₂ ≤ W (d₁ + (m₂ - m₁)) + W (d₂ - (m₂ - m₁)) := by
    have h := hW hd₁ hsh₂ hsh₁ (by rw [hcancel]; exact hd₂)
      (by linarith) (by linarith)
    rw [hcancel] at h
    linarith
  have hmax := (shift_tight hsh₁ hsh₂ h₁ h₂ hsum).1
  have := hgreat₁ _ hsh₂ hmax
  linarith

/-- **The maximizer moves by at least the shift, from increasing chords alone.**

The chord form of `argmax_shift_ge_of_convexOn_of_upperGreatest`. This is the
direction a downstream comparison wants when it needs a response gap *not to
widen*, and stating it on chords is what lets the condition be imposed on a
composite `s ↦ V (F x s)` rather than on `V`. -/
theorem argmax_shift_ge_of_increasingChords_of_upperGreatest
    {g W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hW : IncreasingChordsOn W A)
    (hd₁ : d₁ ∈ A) (hd₂ : d₂ ∈ A)
    (hm : m₁ ≤ m₂)
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (h₁ : IsMaxOn (fun s => g (s - m₁) + W s) A d₁)
    (h₂ : IsMaxOn (fun s => g (s - m₂) + W s) A d₂)
    (hgreat₂ : ∀ y ∈ A, IsMaxOn (fun s => g (s - m₂) + W s) A y → y ≤ d₂) :
    m₂ - m₁ ≤ d₂ - d₁ := by
  by_contra hcon0
  have hcon : d₂ - d₁ < m₂ - m₁ := not_le.mp hcon0
  -- Here the order of the two chords is the other way round.
  have hcancel : d₂ - (m₂ - m₁) + (m₂ - m₁) = d₂ := by ring
  have hsum : W d₁ + W d₂ ≤ W (d₁ + (m₂ - m₁)) + W (d₂ - (m₂ - m₁)) := by
    have h := hW hsh₂ hd₁ (by rw [hcancel]; exact hd₂) hsh₁
      (by linarith) (by linarith)
    rw [hcancel] at h
    linarith
  have hmax := (shift_tight hsh₁ hsh₂ h₁ h₂ hsum).2
  have := hgreat₂ _ hsh₁ hmax
  linarith

/-- **An affine perturbation leaves the gap exactly unchanged.**

Both chord conditions hold with equality for an affine `W`, so the two
inequalities above pin the movement to the shift. The knife edge, stated where
it belongs: on the chords, with no appeal to differentiability, and *sufficient
only* — a `W` that is neither convex nor concave can still leave some particular
pair of gaps equal. -/
theorem argmax_shift_eq_of_chords_of_greatest
    {g W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hWi : IncreasingChordsOn W A) (hWd : DecreasingChordsOn W A)
    (hd₁ : d₁ ∈ A) (hd₂ : d₂ ∈ A)
    (hm : m₁ ≤ m₂)
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (h₁ : IsMaxOn (fun s => g (s - m₁) + W s) A d₁)
    (h₂ : IsMaxOn (fun s => g (s - m₂) + W s) A d₂)
    (hgreat₁ : ∀ y ∈ A, IsMaxOn (fun s => g (s - m₁) + W s) A y → y ≤ d₁)
    (hgreat₂ : ∀ y ∈ A, IsMaxOn (fun s => g (s - m₂) + W s) A y → y ≤ d₂) :
    d₂ - d₁ = m₂ - m₁ :=
  le_antisymm
    (argmax_shift_le_of_decreasingChords_of_lowerGreatest hWd hd₁ hd₂ hm hsh₁
      hsh₂ h₁ h₂ hgreat₁)
    (argmax_shift_ge_of_increasingChords_of_upperGreatest hWi hd₁ hd₂ hm hsh₁
      hsh₂ h₁ h₂ hgreat₂)

/-- An affine function has increasing translated chords — with equality. -/
theorem increasingChordsOn_of_affine {A : Set ℝ} (c b : ℝ) :
    IncreasingChordsOn (fun y => c * y + b) A := by
  intro u v h _ _ _ _ _ _; simp only; ring_nf; linarith

/-- An affine function has decreasing translated chords — with equality. -/
theorem decreasingChordsOn_of_affine {A : Set ℝ} (c b : ℝ) :
    DecreasingChordsOn (fun y => c * y + b) A := by
  intro u v h _ _ _ _ _ _; simp only; ring_nf; linarith

/-! ### The same three results, read on the gap

`d - m` rather than `d`. Purely a restatement in each case: `d₂ - d₁ ≤ m₂ - m₁`
and `d₂ - m₂ ≤ d₁ - m₁` are the same inequality rearranged. -/

/-- **The gap does not grow** with the centre, under concavity and a greatest
selection at the lower centre. -/
theorem gap_antitone_of_concaveOn_of_lowerGreatest
    {g W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hW : ConcaveOn ℝ A W)
    (hd₁ : d₁ ∈ A) (hd₂ : d₂ ∈ A)
    (hm : m₁ ≤ m₂)
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (h₁ : IsMaxOn (fun s => g (s - m₁) + W s) A d₁)
    (h₂ : IsMaxOn (fun s => g (s - m₂) + W s) A d₂)
    (hgreat₁ : ∀ y ∈ A, IsMaxOn (fun s => g (s - m₁) + W s) A y → y ≤ d₁) :
    d₂ - m₂ ≤ d₁ - m₁ := by
  have := argmax_shift_le_of_concaveOn_of_lowerGreatest hW hd₁ hd₂ hm hsh₁ hsh₂
    h₁ h₂ hgreat₁
  linarith

/-- **The gap does not shrink** with the centre, under convexity and a greatest
selection at the higher centre. This is the direction a downstream comparison
wants when it needs the gap to be *antitone in a parameter that moves the centre
down* — the composition is done at the point of use, not here. -/
theorem gap_monotone_of_convexOn_of_upperGreatest
    {g W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hW : ConvexOn ℝ A W)
    (hm : m₁ ≤ m₂)
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (h₁ : IsMaxOn (fun s => g (s - m₁) + W s) A d₁)
    (h₂ : IsMaxOn (fun s => g (s - m₂) + W s) A d₂)
    (hgreat₂ : ∀ y ∈ A, IsMaxOn (fun s => g (s - m₂) + W s) A y → y ≤ d₂) :
    d₁ - m₁ ≤ d₂ - m₂ := by
  have := argmax_shift_ge_of_convexOn_of_upperGreatest hW hm hsh₁ hsh₂ h₁ h₂
    hgreat₂
  linarith

/-- **The gap does not grow**, uniqueness variant. Immediate restatement of
`argmax_shift_le_of_concaveOn`. -/
theorem gap_antitone_of_concaveOn
    {g W : ℝ → ℝ} {A : Set ℝ} {m₁ m₂ d₁ d₂ : ℝ}
    (hW : ConcaveOn ℝ A W)
    (hd₁ : d₁ ∈ A) (hd₂ : d₂ ∈ A)
    (hm : m₁ ≤ m₂)
    (hsh₁ : d₁ + (m₂ - m₁) ∈ A) (hsh₂ : d₂ - (m₂ - m₁) ∈ A)
    (h₁ : IsMaxOn (fun s => g (s - m₁) + W s) A d₁)
    (h₂ : IsMaxOn (fun s => g (s - m₂) + W s) A d₂)
    (huniq₂ : ∀ s ∈ A, IsMaxOn (fun s' => g (s' - m₂) + W s') A s → s = d₂) :
    d₂ - m₂ ≤ d₁ - m₁ := by
  have := argmax_shift_le_of_concaveOn hW hd₁ hd₂ hm hsh₁ hsh₂ h₁ h₂ huniq₂
  linarith

end Sanctions
