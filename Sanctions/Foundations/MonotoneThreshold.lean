/-
Sanctions/Foundations/MonotoneThreshold.lean

**Generic threshold extraction for monotone condition sets on ℝ.**

Standard order-topology machinery for the "first-crossing" pattern: a
condition on a real state variable whose validity propagates upward
(an *upward-closed* set within an ambient interval) is exactly an
upper interval `[x*, hi]`, and its pivot `x* = sInf` is a derived
object — it exists, belongs to the set (when the set is closed), is
interior when the bottom of the ambient interval fails the condition,
and moves antitonically under inclusion of condition sets ("more
demanding conditions flip later").

Mathematical content is classical:

* upper-interval structure + pivot membership — order topology on a
  conditionally complete linear order (`IsClosed.csInf_mem`);
* pivot comparison — `csInf` antitonicity under set inclusion;
* uniqueness of a crossing for strictly monotone functions;
* existence of an interior crossing — intermediate value theorem.

The pattern is the abstract core of monotone-comparative-statics
threshold arguments (Topkis 1998 §2; Milgrom-Shannon 1994): when a
family of chord conditions is monotone in a state parameter, the set
of states satisfying all of them is upward closed, and the economic
"tipping threshold" is its `sInf`.

No project-specific content: everything is stated for abstract
sets/functions on `ℝ`. The application to the sanction game's
stage-payoff flip sets lives in
`Sanctions/Theory/Basin/StageFlip.lean`.
-/

import Sanctions.Foundations.Basic

namespace Sanctions
namespace MonotoneThreshold

open Filter Set Topology

/-! ## Upward-closed sets in an interval -/

/-- **Upward-closed in an interval.** `A` is a subset of `[lo, hi]`
whose membership propagates upward within the interval: if `x ∈ A` and
`x ≤ y` with `y ∈ [lo, hi]`, then `y ∈ A`. This is the abstract shape
of a *flip set* — the set of states at which a family of
monotone-in-state conditions all hold. -/
def UpwardClosedIn (A : Set ℝ) (lo hi : ℝ) : Prop :=
  A ⊆ Set.Icc lo hi ∧
    ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ Set.Icc lo hi → x ≤ y → y ∈ A

namespace UpwardClosedIn

variable {A : Set ℝ} {lo hi : ℝ}

theorem subset (h : UpwardClosedIn A lo hi) : A ⊆ Set.Icc lo hi := h.1

theorem mem_of_le (h : UpwardClosedIn A lo hi) {x y : ℝ}
    (hx : x ∈ A) (hy : y ∈ Set.Icc lo hi) (hxy : x ≤ y) : y ∈ A :=
  h.2 hx hy hxy

/-- An upward-closed set in `[lo, hi]` is bounded below (by `lo`). -/
theorem bddBelow (h : UpwardClosedIn A lo hi) : BddBelow A :=
  ⟨lo, fun _ hx => (h.1 hx).1⟩

/-- **Pivot membership.** The infimum of a nonempty *closed*
upward-closed set belongs to the set: the threshold itself satisfies
the condition (the crossing is attained). -/
theorem pivot_mem (h : UpwardClosedIn A lo hi) (hA : IsClosed A)
    (hne : A.Nonempty) : sInf A ∈ A :=
  hA.csInf_mem hne h.bddBelow

/-- **The flip set is exactly the upper interval `[sInf A, hi]`.**
A nonempty closed upward-closed subset of `[lo, hi]` equals
`[sInf A, hi]`: the condition holds at a state iff the state is at
or above the pivot. -/
theorem eq_Icc_pivot (h : UpwardClosedIn A lo hi) (hA : IsClosed A)
    (hne : A.Nonempty) : A = Set.Icc (sInf A) hi := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨csInf_le h.bddBelow hx, (h.1 hx).2⟩
  · intro y hy
    have hpivot := h.pivot_mem hA hne
    exact h.mem_of_le hpivot ⟨le_trans (h.1 hpivot).1 hy.1, hy.2⟩ hy.1

/-- **Interiority.** If the bottom of the ambient interval fails the
condition, the pivot is strictly above it. -/
theorem lo_lt_pivot (h : UpwardClosedIn A lo hi) (hA : IsClosed A)
    (hne : A.Nonempty) (hlo : lo ∉ A) : lo < sInf A := by
  rcases lt_or_eq_of_le (le_csInf hne fun x hx => (h.1 hx).1) with hlt | heq
  · exact hlt
  · exact absurd (heq ▸ h.pivot_mem hA hne) hlo

end UpwardClosedIn

/-! ## Pivot comparison -/

/-- **Pivot antitonicity under inclusion.** A more demanding condition
set (a subset) has a weakly later pivot. Wrapper around
`csInf_le_csInf` in threshold language; drives both the
static-vs-dynamic two-threshold comparison and the action-frontier
monotonicity. -/
theorem pivot_le_pivot_of_subset {A B : Set ℝ} (hBA : B ⊆ A)
    (hA_bdd : BddBelow A) (hB_ne : B.Nonempty) : sInf A ≤ sInf B :=
  csInf_le_csInf hA_bdd hB_ne hBA

/-! ## Crossings of monotone functions -/

/-- **Uniqueness of the crossing.** A strictly monotone function on a
set has at most one zero. -/
theorem zero_unique_of_strictMonoOn {g : ℝ → ℝ} {s : Set ℝ}
    (hg : StrictMonoOn g s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s)
    (hgx : g x = 0) (hgy : g y = 0) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have := hg hx hy hlt
    rw [hgx, hgy] at this
    exact absurd this (lt_irrefl 0)
  · exact heq
  · have := hg hy hx hgt
    rw [hgx, hgy] at this
    exact absurd this (lt_irrefl 0)

/-- **Existence of an interior crossing (IVT).** A continuous function
negative at `lo` and positive at `hi` has a zero strictly between
them. -/
theorem exists_interior_zero {g : ℝ → ℝ} {lo hi : ℝ} (hle : lo ≤ hi)
    (hg : ContinuousOn g (Set.Icc lo hi)) (hneg : g lo < 0)
    (hpos : 0 < g hi) : ∃ x ∈ Set.Ioo lo hi, g x = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (g lo) (g hi) := ⟨hneg, hpos⟩
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Ioo hle hg h0
  exact ⟨x, hx, hgx⟩

/-! ## Downward-closed sets in an interval (low-basin mirror)

Sign-mirrors of the upward-closed machinery: a condition whose
validity propagates *downward* (e.g. "the chord is still negative")
is exactly a lower interval `[lo, x*]` with pivot `x* = sSup`. -/

/-- **Downward-closed in an interval.** `A ⊆ [lo, hi]` whose
membership propagates downward within the interval. -/
def DownwardClosedIn (A : Set ℝ) (lo hi : ℝ) : Prop :=
  A ⊆ Set.Icc lo hi ∧
    ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ Set.Icc lo hi → y ≤ x → y ∈ A

namespace DownwardClosedIn

variable {A : Set ℝ} {lo hi : ℝ}

theorem subset (h : DownwardClosedIn A lo hi) : A ⊆ Set.Icc lo hi := h.1

theorem mem_of_ge (h : DownwardClosedIn A lo hi) {x y : ℝ}
    (hx : x ∈ A) (hy : y ∈ Set.Icc lo hi) (hyx : y ≤ x) : y ∈ A :=
  h.2 hx hy hyx

/-- A downward-closed set in `[lo, hi]` is bounded above (by `hi`). -/
theorem bddAbove (h : DownwardClosedIn A lo hi) : BddAbove A :=
  ⟨hi, fun _ hx => (h.1 hx).2⟩

/-- **Pivot membership (dual).** The supremum of a nonempty closed
downward-closed set belongs to the set. -/
theorem pivot_mem (h : DownwardClosedIn A lo hi) (hA : IsClosed A)
    (hne : A.Nonempty) : sSup A ∈ A :=
  hA.csSup_mem hne h.bddAbove

/-- **The dual flip set is exactly the lower interval
`[lo, sSup A]`.** -/
theorem eq_Icc_pivot (h : DownwardClosedIn A lo hi) (hA : IsClosed A)
    (hne : A.Nonempty) : A = Set.Icc lo (sSup A) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨(h.1 hx).1, le_csSup h.bddAbove hx⟩
  · intro y hy
    have hpivot := h.pivot_mem hA hne
    exact h.mem_of_ge hpivot ⟨hy.1, le_trans hy.2 (h.1 hpivot).2⟩ hy.2

/-- **Interiority (dual).** If the top of the ambient interval fails
the condition, the pivot is strictly below it. -/
theorem pivot_lt_hi (h : DownwardClosedIn A lo hi) (hA : IsClosed A)
    (hne : A.Nonempty) (hhi : hi ∉ A) : sSup A < hi := by
  rcases lt_or_eq_of_le (csSup_le hne fun x hx => (h.1 hx).2) with hlt | heq
  · exact hlt
  · exact absurd (heq ▸ h.pivot_mem hA hne) hhi

end DownwardClosedIn

/-- **Pivot monotonicity under inclusion (dual).** A more demanding
condition set (a subset) has a weakly *earlier* upper pivot. -/
theorem pivot_le_pivot_of_subset_sup {A B : Set ℝ} (hBA : B ⊆ A)
    (hA_bdd : BddAbove A) (hB_ne : B.Nonempty) : sSup B ≤ sSup A :=
  csSup_le_csSup hA_bdd hB_ne hBA


/-! ## Scalar Knaster-Tarski on a closed interval (Round E2)

A monotone self-map of `[lo, hi]` has a least fixed point — the
infimum of its post-fixed points. Drives the steady-state band of the
realized sanction rule. -/

/-- **Scalar Knaster-Tarski.** A monotone self-map of `[lo, hi]` has a
least fixed point. -/
theorem exists_least_fixedPoint_of_monotoneOn_Icc {G : ℝ → ℝ}
    {lo hi : ℝ} (hle : lo ≤ hi)
    (hmono : MonotoneOn G (Set.Icc lo hi))
    (hmaps : ∀ x ∈ Set.Icc lo hi, G x ∈ Set.Icc lo hi) :
    ∃ xs ∈ Set.Icc lo hi, G xs = xs ∧
      ∀ y ∈ Set.Icc lo hi, G y = y → xs ≤ y := by
  set A := {x | x ∈ Set.Icc lo hi ∧ G x ≤ x} with hA_def
  have hhiA : hi ∈ A :=
    ⟨⟨hle, le_refl hi⟩, (hmaps hi ⟨hle, le_refl hi⟩).2⟩
  have hAne : A.Nonempty := ⟨hi, hhiA⟩
  have hAbdd : BddBelow A := ⟨lo, fun x hx => hx.1.1⟩
  set xs := sInf A with hxs_def
  have hxs_mem : xs ∈ Set.Icc lo hi :=
    ⟨le_csInf hAne (fun x hx => hx.1.1), csInf_le hAbdd hhiA⟩
  have hGlb : ∀ x ∈ A, G xs ≤ x := fun x hx =>
    le_trans (hmono hxs_mem hx.1 (csInf_le hAbdd hx)) hx.2
  have hGxs_le : G xs ≤ xs := le_csInf hAne hGlb
  have hGxs_mem : G xs ∈ Set.Icc lo hi := hmaps xs hxs_mem
  have hGxsA : G xs ∈ A :=
    ⟨hGxs_mem, hmono hGxs_mem hxs_mem hGxs_le⟩
  have hxs_le_G : xs ≤ G xs := csInf_le hAbdd hGxsA
  refine ⟨xs, hxs_mem, le_antisymm hGxs_le hxs_le_G, ?_⟩
  intro y hy hGy
  exact csInf_le hAbdd ⟨hy, le_of_eq hGy⟩

/-- **A monotone orbit limit need not be a fixed point.** There is a
monotone self-map of `[0,2]` whose orbit from `0` converges to `1`, even
though `1` is not fixed and the map's least fixed point is `2`. Thus
monotonicity and interval invariance alone do not justify identifying an
iteration limit with the least fixed point; an order-continuity or closed-graph
condition is needed at the limit. -/
theorem monotone_selfMap_orbit_limit_need_not_be_fixed :
    ∃ G : ℝ → ℝ, ∃ u : ℕ → ℝ,
      MonotoneOn G (Set.Icc 0 2) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 2, G x ∈ Set.Icc (0 : ℝ) 2) ∧
      u 0 = 0 ∧
      (∀ n, u (n + 1) = G (u n)) ∧
      Tendsto u atTop (𝓝 1) ∧
      G 1 ≠ 1 ∧
      G 2 = 2 ∧
      (∀ y ∈ Set.Icc (0 : ℝ) 2, G y = y → 2 ≤ y) := by
  let G : ℝ → ℝ := fun x => if x < 1 then (x + 1) / 2 else 2
  let u : ℕ → ℝ := fun n => 1 - ((1 / 2 : ℝ) ^ n)
  refine ⟨G, u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hy1 : y < 1
    · have hx1 : x < 1 := lt_of_le_of_lt hxy hy1
      simp only [G, if_pos hx1, if_pos hy1]
      linarith
    · simp only [G, if_neg hy1]
      by_cases hx1 : x < 1
      · simp only [if_pos hx1]
        have hx2 : x ≤ 2 := hx.2
        linarith
      · simp only [if_neg hx1]
        exact le_rfl
  · intro x hx
    constructor
    · simp only [G]
      split_ifs <;> linarith [hx.1]
    · simp only [G]
      split_ifs <;> linarith [hx.2]
  · norm_num [u]
  · intro n
    have hnpos : 0 < ((1 / 2 : ℝ) ^ n) := pow_pos (by norm_num) n
    have hun1 : u n < 1 := by
      simp only [u]
      linarith
    simp only [u, G, hun1, if_pos, pow_succ]
    ring
  · have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
    simpa only [u, sub_zero] using tendsto_const_nhds.sub hpow
  · norm_num [G]
  · norm_num [G]
  · intro y hy hfix
    by_cases hy1 : y < 1
    · simp only [G, if_pos hy1] at hfix
      linarith
    · simp only [G, if_neg hy1] at hfix
      linarith


/-! ## Constrained monotone greatest selection (Round B3)

Topkis/Milgrom-Shannon monotone selection over ASCENDING interval
constraint sets `[u(x), v(x)]`: if chords of the objective (restricted
to points feasible at both parameters) are non-decreasing in the
parameter, the greatest constrained maximizer is non-decreasing.
The constraint-set movement is handled pointwise — no lattice
machinery needed on the scalar chain. Anchor: Topkis 1998
Thm 2.8.2 / Amir 1996 (next-state coordinates). -/

/-- **Greatest constrained maximizer is monotone under ID on the
overlap.** `y` maximizes `f · x` on `[u x, v x]`; `y'` is the
GREATEST maximizer of `f · x'` on `[u x', v x']`; the interval
endpoints ascend; and chords between points feasible at both
parameters are non-decreasing in the parameter. Then `y ≤ y'`. -/
theorem le_greatestMaxOn_of_ID_ascendingIcc
    {f : ℝ → ℝ → ℝ} {u v : ℝ → ℝ} {x x' : ℝ}
    (hxx' : x ≤ x') (hu : u x ≤ u x') (hv : v x ≤ v x')
    {y y' : ℝ}
    (hy : y ∈ Set.Icc (u x) (v x)) (hy' : y' ∈ Set.Icc (u x') (v x'))
    (hymax : ∀ z ∈ Set.Icc (u x) (v x), f z x ≤ f y x)
    (hy'greatest : ∀ z ∈ Set.Icc (u x') (v x'),
      (∀ w ∈ Set.Icc (u x') (v x'), f w x' ≤ f z x') → z ≤ y')
    (hy'max : ∀ z ∈ Set.Icc (u x') (v x'), f z x' ≤ f y' x')
    (hID : ∀ s₁ s₂,
      s₁ ∈ Set.Icc (u x) (v x) → s₁ ∈ Set.Icc (u x') (v x') →
      s₂ ∈ Set.Icc (u x) (v x) → s₂ ∈ Set.Icc (u x') (v x') →
      s₁ ≤ s₂ → f s₂ x - f s₁ x ≤ f s₂ x' - f s₁ x') :
    y ≤ y' := by
  rcases le_or_gt y y' with h | hgt
  · exact h
  -- y' < y: then both points are feasible at both parameters.
  have hy_at' : y ∈ Set.Icc (u x') (v x') :=
    ⟨le_trans hy'.1 (le_of_lt hgt), le_trans hy.2 hv⟩
  have hy'_at : y' ∈ Set.Icc (u x) (v x) :=
    ⟨le_trans hu hy'.1, le_trans (le_of_lt hgt) hy.2⟩
  -- ID lifts y's optimality at x to optimality over y' at x'.
  have hchord := hID y' y hy'_at hy' hy hy_at' (le_of_lt hgt)
  have h_at_x : f y' x ≤ f y x := hymax y' hy'_at
  have h_y_max' : f y' x' ≤ f y x' := by linarith
  -- Hence y is also a greatest-dominating maximizer at x'.
  have hymax' : ∀ w ∈ Set.Icc (u x') (v x'), f w x' ≤ f y x' :=
    fun w hw => le_trans (hy'max w hw) h_y_max'
  have := hy'greatest y hy_at' hymax'
  linarith

/-! ## Every-selection monotonicity under strict ID (Round B6)

Under STRICT increasing differences, not only extremal selections but
EVERY pair of maximizer selections is ordered — the selector-robust
form of monotone comparative statics (Topkis 1998 Thms 2.8.4-2.8.5
flavor, scalar chain case). -/

/-- **Every selection is monotone under strict ID.** If chords are
STRICTLY increasing in the parameter and `s`, `s'` maximize at
`t < t'` respectively, then `s ≤ s'` — regardless of which
maximizers were selected. -/
theorem argmax_selections_mono_of_strict_ID
    {f : ℝ → ℝ → ℝ} {S : Set ℝ}
    {s s' t t' : ℝ} (htt : t < t')
    (hs : s ∈ S) (hs' : s' ∈ S)
    (hsmax : ∀ z ∈ S, f z t ≤ f s t)
    (hs'max : ∀ z ∈ S, f z t' ≤ f s' t')
    (hstrict : ∀ s₁ s₂, s₁ ∈ S → s₂ ∈ S → s₁ < s₂ →
      f s₂ t - f s₁ t < f s₂ t' - f s₁ t') :
    s ≤ s' := by
  by_contra hcon
  have hlt : s' < s := lt_of_not_ge hcon
  have hchord := hstrict s' s hs' hs hlt
  have h_at_t : f s' t ≤ f s t := hsmax s' hs'
  have h_at_t' : f s t' ≤ f s' t' := hs'max s hs
  linarith


/-! ## Comparative statics of least fixed points (band-MCS round)

Transport layer for deep-parameter comparative statics of the lock-in
level: least fixed points of monotone interval self-maps respond
monotonically to pointwise dominance of the operator, and to the
adjustment weight in convex-combination step maps. Anchors:
Acemoglu-Jensen 2015 (robust comparative statics of extremal fixed
points); Milgrom-Roberts 1994; Topkis 1998. -/

/-- **Least fixed point is monotone under pointwise operator
dominance.** If `G₁ ≤ G₂` pointwise on `[lo, hi]`, `G₁` is monotone
and bounded below by `lo` there, `xs₁` is a least fixed point of
`G₁`, and `xs₂` is any fixed point of `G₂`, then `xs₁ ≤ xs₂`.
Engine: `G₁` maps `[lo, xs₂]` into itself, so the least-fixed-point
existence lemma on the SHRUNKEN interval produces a `G₁`-fixed point
below `xs₂`. -/
theorem least_fixedPoint_le_fixedPoint_of_pointwise_le
    {G₁ G₂ : ℝ → ℝ} {lo hi xs₁ xs₂ : ℝ}
    (hmono₁ : MonotoneOn G₁ (Set.Icc lo hi))
    (hlo₁ : ∀ x ∈ Set.Icc lo hi, lo ≤ G₁ x)
    (hleast₁ : ∀ y ∈ Set.Icc lo hi, G₁ y = y → xs₁ ≤ y)
    (hxs₂ : xs₂ ∈ Set.Icc lo hi) (hfix₂ : G₂ xs₂ = xs₂)
    (hG : ∀ x ∈ Set.Icc lo hi, G₁ x ≤ G₂ x) :
    xs₁ ≤ xs₂ := by
  have hsub : Set.Icc lo xs₂ ⊆ Set.Icc lo hi := by
    intro z hz
    exact ⟨hz.1, le_trans hz.2 hxs₂.2⟩
  have hmaps : ∀ z ∈ Set.Icc lo xs₂, G₁ z ∈ Set.Icc lo xs₂ := by
    intro z hz
    have hzin := hsub hz
    refine ⟨hlo₁ z hzin, ?_⟩
    calc G₁ z ≤ G₁ xs₂ := hmono₁ hzin hxs₂ hz.2
      _ ≤ G₂ xs₂ := hG xs₂ hxs₂
      _ = xs₂ := hfix₂
  obtain ⟨z, hz_mem, hz_fix, _⟩ :=
    exists_least_fixedPoint_of_monotoneOn_Icc hxs₂.1
      (hmono₁.mono hsub) hmaps
  exact le_trans (hleast₁ z (hsub hz_mem) hz_fix) hz_mem.2

/-- **The lock-in level rises with the adjustment weight.** For a
monotone rule `r` with floor `x ≤ r x` and ceiling `r x ≤ hi` on
`[lo, hi]`, the weighted step maps `x ↦ (1−w)·x + w·r(x)` have least
fixed points monotone in the weight `w ∈ [0, 1]`: faster adjustment
locks in at a weakly higher level. -/
theorem exists_least_fixedPoints_le_of_weight_le
    {r : ℝ → ℝ} {lo hi w₁ w₂ : ℝ} (hle : lo ≤ hi)
    (hw₁ : 0 ≤ w₁) (hw₂ : w₂ ≤ 1) (hww : w₁ ≤ w₂)
    (hr_mono : MonotoneOn r (Set.Icc lo hi))
    (hr_floor : ∀ x ∈ Set.Icc lo hi, x ≤ r x)
    (hr_ceil : ∀ x ∈ Set.Icc lo hi, r x ≤ hi) :
    ∃ xs₁ ∈ Set.Icc lo hi, ∃ xs₂ ∈ Set.Icc lo hi,
      (1 - w₁) * xs₁ + w₁ * r xs₁ = xs₁ ∧
      (1 - w₂) * xs₂ + w₂ * r xs₂ = xs₂ ∧
      (∀ y ∈ Set.Icc lo hi, (1 - w₁) * y + w₁ * r y = y → xs₁ ≤ y) ∧
      (∀ y ∈ Set.Icc lo hi, (1 - w₂) * y + w₂ * r y = y → xs₂ ≤ y) ∧
      xs₁ ≤ xs₂ := by
  have hw₁1 : w₁ ≤ 1 := le_trans hww hw₂
  have hw₂0 : 0 ≤ w₂ := le_trans hw₁ hww
  have hmono : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      MonotoneOn (fun x => (1 - w) * x + w * r x) (Set.Icc lo hi) := by
    intro w hw0 hw1 x hx y hy hxy
    simp only
    have h1 : (1 - w) * x ≤ (1 - w) * y :=
      mul_le_mul_of_nonneg_left hxy (by linarith)
    have h2 : w * r x ≤ w * r y :=
      mul_le_mul_of_nonneg_left (hr_mono hx hy hxy) hw0
    linarith
  have hmaps : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      ∀ x ∈ Set.Icc lo hi, (1 - w) * x + w * r x ∈ Set.Icc lo hi := by
    intro w hw0 hw1 x hx
    constructor
    · have hfl := hr_floor x hx
      have hnn : 0 ≤ w * (r x - x) := mul_nonneg hw0 (by linarith)
      nlinarith [hx.1]
    · have hc := hr_ceil x hx
      have h1 : (1 - w) * x ≤ (1 - w) * hi :=
        mul_le_mul_of_nonneg_left hx.2 (by linarith)
      have h2 : w * r x ≤ w * hi := mul_le_mul_of_nonneg_left hc hw0
      nlinarith
  obtain ⟨xs₁, hxs₁_mem, hxs₁_fix, hxs₁_least⟩ :=
    exists_least_fixedPoint_of_monotoneOn_Icc hle
      (hmono w₁ hw₁ hw₁1) (hmaps w₁ hw₁ hw₁1)
  obtain ⟨xs₂, hxs₂_mem, hxs₂_fix, hxs₂_least⟩ :=
    exists_least_fixedPoint_of_monotoneOn_Icc hle
      (hmono w₂ hw₂0 hw₂) (hmaps w₂ hw₂0 hw₂)
  refine ⟨xs₁, hxs₁_mem, xs₂, hxs₂_mem, hxs₁_fix, hxs₂_fix,
    hxs₁_least, hxs₂_least, ?_⟩
  apply least_fixedPoint_le_fixedPoint_of_pointwise_le
    (G₁ := fun x => (1 - w₁) * x + w₁ * r x)
    (G₂ := fun x => (1 - w₂) * x + w₂ * r x)
    (hmono w₁ hw₁ hw₁1) (fun x hx => (hmaps w₁ hw₁ hw₁1 x hx).1)
    hxs₁_least hxs₂_mem hxs₂_fix
  intro x hx
  have hfl := hr_floor x hx
  have hnn : 0 ≤ (w₂ - w₁) * (r x - x) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- **Two-objective greatest-maximizer comparison.** If the
difference `g − f` is nondecreasing on `S`, then any maximizer of
`f` sits weakly below the greatest maximizer of `g`. -/
theorem le_greatestMaxOn_of_diff_mono
    {f g : ℝ → ℝ} {S : Set ℝ} {y y' : ℝ}
    (hy : y ∈ S) (hy' : y' ∈ S)
    (hymax : ∀ z ∈ S, f z ≤ f y)
    (hy'max : ∀ z ∈ S, g z ≤ g y')
    (hy'greatest : ∀ z ∈ S, (∀ w ∈ S, g w ≤ g z) → z ≤ y')
    (hdiff : ∀ z₁ z₂, z₁ ∈ S → z₂ ∈ S → z₁ ≤ z₂ →
      g z₁ - f z₁ ≤ g z₂ - f z₂) :
    y ≤ y' := by
  rcases le_or_gt y y' with h | hgt
  · exact h
  have hfy : f y' ≤ f y := hymax y' hy'
  have hd := hdiff y' y hy' hy (le_of_lt hgt)
  have hgy : ∀ w ∈ S, g w ≤ g y := by
    intro w hw
    have h1 := hy'max w hw
    linarith
  have := hy'greatest y hy hgy
  linarith

/-! ## Closedness helpers for quantified condition sets -/

/-- A guarded condition set `{x | Q → R x}` (guard `Q` independent of
`x`) is closed when `{x | R x}` is. -/
theorem isClosed_setOf_imp {α : Type*} [TopologicalSpace α] {Q : Prop}
    {R : α → Prop} (h : IsClosed {x : α | R x}) :
    IsClosed {x : α | Q → R x} := by
  by_cases hQ : Q
  · simpa [hQ] using h
  · simp [hQ]

/-- A universally quantified condition set
`{x | ∀ i ∈ s, P i x}` is closed when each slice `{x | P i x}` is. -/
theorem isClosed_setOf_forall_mem {α ι : Type*} [TopologicalSpace α]
    {s : Set ι} {P : ι → α → Prop}
    (h : ∀ i ∈ s, IsClosed {x : α | P i x}) :
    IsClosed {x : α | ∀ i ∈ s, P i x} := by
  have heq : {x : α | ∀ i ∈ s, P i x} = ⋂ i ∈ s, {x : α | P i x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_biInter h

end MonotoneThreshold
end Sanctions
