/-
Sanctions/Examples/AffineWindowContinuum.lean

**A continuum of equilibria inside the certificate window, at the affine member**
(round BE, 2026-10-03; gap G4 of `suggestions/2026-10-02-lean-gap-map/01_GAP_MAP.md`;
construction C4 of the first ChatGPT gap review and §2 of
`suggestions/2026-10-03-books-and-mathematical-revalidation/02_MATHEMATICAL_VALIDATION.md`,
checked locally on 2026-10-03 by exact algebra and an independent numerical re-solve).

The economy is the affine member of the quadratic–linear family (`placableAffine`:
`q = 3`, `u₀ = 1`, `k = 3`, `r = 1/2`, `w = 1`, `ℓ = 1`, `c = 4`, `n = 0`, `v = 30`,
transition `(x+s)/2`, `β_S = 1/2`) with only the Target's discount factor varied
(`awChord b`). At this member the bracket's certificates leave a window, about
`[0.180, 0.1875]` in `β_T` (appendix, the bracket's probe).

This file proves that at the discount `β₁ = 25248/138097 ≈ 0.18283`, inside that window,
the game has a continuum of top-selector equilibria: for every `t ∈ [0, 4/9]`,

    α_t(x) = t + (287/4206)·x,
    V_S(x) = (12/701)x² + ((44 − 12t)/29)x + ((40 − 90t)/29)²·(701/2100),
    V_T(x) = (197/6)x − ((40 − 3t)/29)·138097/(3·112849),

with realised sanction `((40 − 90t)/29)·(701/2100) + x/10`, positive for `t < 4/9`
(`awEquilibrium`, `aw_continuum`). Distinct `t` give distinct policies. The Target is
indifferent among all compliance levels up to the level that ends the sanction, which is
why the policy can move with `t`; this is weak, not strict, optimality.

`AffineWindowBoundaries.lean` proves the two exact endpoint boundaries at this member
(zero sanctions exist exactly up to `36/197`, full defiance exactly from
`(82 − 7√2)/394`), and that `β₁` lies strictly between them.

**Rule 9.** An existence certificate for multiplicity at one member and one discount. It
does not classify the equilibrium correspondence and does not show that multiplicity is
generic or survives perturbation. **Rule 22.** AFFINE: the affine member of the family.
**Rule 1.** The response is the unique Sender maximiser at every compliance level, and the
policy a Target maximiser at every state. **Rule 3.** No assumption is introduced.
-/
import Sanctions.Examples.ExplicitEquilibriumKit
import Sanctions.Examples.PlacableSenderWitnesses

namespace Sanctions
namespace Examples

open Set BoundedContinuousFunction AbstractGame

noncomputable section

/-! ## 1. The affine member with a free Target discount -/

/-- The affine member of the quadratic–linear family with Target discount `b`. -/
def awBase (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : PlacableEconomyFcs :=
  { placableAffineCs with
    toPlacableEconomyF := { placableAffine with βT := b, hβT0 := hb0, hβT1 := hb1 } }

/-- The same member as an enriched chord economy. -/
abbrev awChord (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : ChordEconomyCs :=
  (awBase b hb0 hb1).toChordCs

/-- Its game. -/
abbrev awParams (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : Params :=
  (awChord b hb0 hb1).toParams

section Game

variable {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1}

theorem aw_U_S : (awParams b hb0 hb1).U_S = symU_S 3 1 3 (1 / 2) 1 := rfl
theorem aw_U_T : (awParams b hb0 hb1).U_T = symU_T 1 4 0 30 := rfl
theorem aw_F : (awParams b hb0 hb1).F = affineF (1 / 2) := rfl
theorem aw_β_S : (awParams b hb0 hb1).β_S = 1 / 2 := rfl
theorem aw_β_T : (awParams b hb0 hb1).β_T = b := rfl

theorem aw_F_mem {x s : ℝ} (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    (awParams b hb0 hb1).F x s ∈ (Sanctions.S : Set ℝ) := by
  rw [aw_F]; unfold affineF; constructor <;> nlinarith [hx.1, hx.2, hs.1, hs.2]

end Game

/-! ## 2. The rational member of the continuum -/

/-- The discount `β₁ = 25248/138097`. -/
def awβ₁ : ℝ := 25248 / 138097

theorem awβ₁_pos : 0 < awβ₁ := by unfold awβ₁; norm_num
theorem awβ₁_lt_one : awβ₁ < 1 := by unfold awβ₁; norm_num

/-- The game at `β₁`. -/
abbrev awP₁ : Params := awParams awβ₁ awβ₁_pos awβ₁_lt_one

/-- The Sender's slope coefficient `κ_t = (44 − 12t)/29`. -/
def awκ (t : ℝ) : ℝ := (44 - 12 * t) / 29
/-- The realised intercept coefficient `A_e(t) = (40 − 90t)/29`. -/
def awAe (t : ℝ) : ℝ := (40 - 90 * t) / 29
/-- The off-policy intercept coefficient `A_o(t) = (40 − 3t)/29`. -/
def awAo (t : ℝ) : ℝ := (40 - 3 * t) / 29

/-- The Sender's value at `t`. -/
def awVS (t : ℝ) : ChordEconomy.Val := quadBCF (12 / 701) (awκ t) (awAe t ^ 2 * (701 / 2100))
/-- The Target's value at `t`. -/
def awVT (t : ℝ) : ChordEconomy.Val :=
  ChordEconomy.affBCF (197 / 6) (-(awAo t * 138097 / (3 * 112849)))
/-- The Target's policy at `t`. -/
def awα (t : ℝ) (x : ℝ) : ℝ := t + 287 / 4206 * x

/-- The vertex of the Sender's objective: `(A_o + (707/1402)x − 3a)·(701/2100)`. -/
def awVertex (t x a : ℝ) : ℝ := (awAo t + 707 / 1402 * x - 3 * a) * (701 / 2100)

/-- The Sender's objective is a concave parabola with curvature `1050/701`. -/
theorem aw_senderObj (t : ℝ) {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ}
    (hs : s ∈ Sanctions.I) :
    awP₁.U_S x a s + awP₁.β_S * awVS t (Sanctions.clipS' (awP₁.F x s))
      = (x + 3 / 1402 * x ^ 2 + awκ t / 4 * x + awAe t ^ 2 * (701 / 2100) / 2
          + 1050 / 701 * awVertex t x a ^ 2)
        - 1050 / 701 * (s - awVertex t x a) ^ 2 := by
  unfold awVS
  rw [quadBCF_apply, Sanctions.clipS'_val_eq_of_mem (aw_F_mem hx hs), aw_U_S, aw_β_S, aw_F]
  unfold symU_S affineF awVertex awκ awAo awAe
  ring

theorem awVertex_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (4 / 9)) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a : ℝ} (ha : a ∈ Sanctions.I) : awVertex t x a ≤ 1 := by
  unfold awVertex awAo
  nlinarith [ht.1, hx.2, ha.1]

/-- **The top response is the positive part of the vertex.** -/
theorem aw_σ_dyn_top {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (4 / 9)) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a : ℝ} (ha : a ∈ Sanctions.I) :
    awP₁.σ_dyn_top (awVS t) x a = max 0 (awVertex t x a) := by
  rw [σ_dyn_top_eq_clip awP₁ (awVS t) (by norm_num : (0 : ℝ) < 1050 / 701)
    (fun s hs => aw_senderObj t hx a hs)]
  rw [min_eq_right (awVertex_le_one ht hx ha)]

theorem awα_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (4 / 9)) {x : ℝ} (hx : x ∈ Sanctions.I) :
    awα t x ∈ Sanctions.I := by
  unfold awα; constructor <;> nlinarith [ht.1, ht.2, hx.1, hx.2]

/-- At the policy the vertex is `A_e·(701/2100) + x/10 ≥ 0`. -/
theorem awVertex_at_policy (t x : ℝ) :
    awVertex t x (awα t x) = awAe t * (701 / 2100) + x / 10 := by
  unfold awVertex awα awAo awAe; ring

theorem awVertex_at_policy_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (4 / 9)) {x : ℝ}
    (hx : x ∈ Sanctions.I) : 0 ≤ awVertex t x (awα t x) := by
  rw [awVertex_at_policy]; unfold awAe; nlinarith [ht.2, hx.1]

/-- The Target's objective at the constructed values: the sanction enters with weight
`700/701`, exactly one third of the Sender's curvature `2100/701`. -/
theorem aw_joint {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (4 / 9)) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a : ℝ} (ha : a ∈ Sanctions.I) :
    awP₁.joint_T_top_integrand (awVT t) (awVS t) x a
      = 30 * x + 2104 / 701 * x - awβ₁ * (awAo t * 138097 / (3 * 112849)) - a
        - 700 / 701 * max 0 (awVertex t x a) := by
  simp only [Params.joint_T_top_integrand]
  rw [aw_σ_dyn_top ht hx ha]
  have hρ : max 0 (awVertex t x a) ∈ Sanctions.I :=
    ⟨le_max_left _ _, max_le zero_le_one (awVertex_le_one ht hx ha)⟩
  unfold awVT
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (aw_F_mem hx hρ), aw_U_T,
    aw_β_T, aw_F]
  unfold symU_T affineF awβ₁
  ring

/-- **The Target is indifferent up to the zero-sanction level and loses beyond it**: at
every compliance level its objective is at most the constant
`K(x) − (A_o + (707/1402)x)/3`, with equality while the response is positive. -/
theorem aw_joint_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (4 / 9)) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a : ℝ} (ha : a ∈ Sanctions.I) :
    awP₁.joint_T_top_integrand (awVT t) (awVS t) x a
      ≤ 30 * x + 2104 / 701 * x - awβ₁ * (awAo t * 138097 / (3 * 112849))
        - (awAo t + 707 / 1402 * x) / 3 := by
  rw [aw_joint ht hx ha]
  rcases le_total (awVertex t x a) 0 with h | h
  · rw [max_eq_left h]
    unfold awVertex at h
    nlinarith [h]
  · rw [max_eq_right h]
    unfold awVertex
    nlinarith [h]

theorem aw_joint_at_policy {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (4 / 9)) {x : ℝ}
    (hx : x ∈ Sanctions.I) :
    awP₁.joint_T_top_integrand (awVT t) (awVS t) x (awα t x)
      = 30 * x + 2104 / 701 * x - awβ₁ * (awAo t * 138097 / (3 * 112849))
        - (awAo t + 707 / 1402 * x) / 3 := by
  rw [aw_joint ht hx (awα_mem ht hx), max_eq_right (awVertex_at_policy_nonneg ht hx)]
  unfold awVertex awα
  ring

/-- **The equilibrium at `t`.** -/
def awEquilibrium (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (4 / 9)) :
    awP₁.FeedbackStackelbergEquilibriumTop where
  V_T := awVT t
  V_S := awVS t
  α := awα t
  hα := by unfold awα; fun_prop
  α_mem := fun _ hx => awα_mem ht hx
  V_S_fix := by
    ext y
    change awVS t y = sSup ((fun s => awP₁.integrandS (awα t) (fun z => awVS t z)
      (y.val, s)) '' Sanctions.I)
    have hval : ∀ s ∈ Sanctions.I,
        awP₁.integrandS (awα t) (fun z => awVS t z) (y.val, s)
          = (y.val + 3 / 1402 * y.val ^ 2 + awκ t / 4 * y.val + awAe t ^ 2 * (701 / 2100) / 2
              + 1050 / 701 * awVertex t y.val (awα t y.val) ^ 2)
            - 1050 / 701 * (s - awVertex t y.val (awα t y.val)) ^ 2 := by
      intro s hs
      have := aw_senderObj t y.property (awα t y.val) hs
      simp only [Params.integrandS]
      rw [this]
    have hv0 := awVertex_at_policy_nonneg ht y.property
    have hv1 := awVertex_le_one ht y.property (awα_mem ht y.property)
    have hgt : IsGreatest ((fun s => awP₁.integrandS (awα t) (fun z => awVS t z)
        (y.val, s)) '' Sanctions.I) (awVS t y) := by
      refine ⟨⟨awVertex t y.val (awα t y.val), ⟨hv0, hv1⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [hval _ ⟨hv0, hv1⟩, awVertex_at_policy]
        unfold awVS; rw [quadBCF_apply]
        unfold awκ awAe
        ring
      · rintro _ ⟨s, hs, rfl⟩
        dsimp only
        rw [hval s hs, awVertex_at_policy]
        unfold awVS; rw [quadBCF_apply]
        unfold awκ awAe
        nlinarith [sq_nonneg (s - ((40 - 90 * t) / 29 * (701 / 2100) + y.val / 10))]
    exact hgt.csSup_eq.symm
  V_T_fix_top := by
    intro y
    have hv : awVT t y = 30 * y.val + 2104 / 701 * y.val
        - awβ₁ * (awAo t * 138097 / (3 * 112849)) - (awAo t + 707 / 1402 * y.val) / 3 := by
      unfold awVT; rw [ChordEconomy.affBCF_apply]; unfold awβ₁ awAo; ring
    have hgt : IsGreatest ((fun a => awP₁.joint_T_top_integrand (awVT t) (awVS t) y.val a)
        '' Sanctions.I) (awVT t y) := by
      refine ⟨⟨awα t y.val, awα_mem ht y.property, ?_⟩, ?_⟩
      · dsimp only
        rw [aw_joint_at_policy ht y.property, hv]
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        rw [hv]
        exact aw_joint_le ht y.property ha
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => by
    intro a ha
    change awP₁.joint_T_top_integrand (awVT t) (awVS t) x a
      ≤ awP₁.joint_T_top_integrand (awVT t) (awVS t) x (awα t x)
    rw [aw_joint_at_policy ht hx]
    exact aw_joint_le ht hx ha

/-- The realised sanction rule at `t`. -/
theorem aw_rule {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (4 / 9)) {x : ℝ} (hx : x ∈ Sanctions.I) :
    awP₁.dynamicEquilibriumRule (awEquilibrium t ht) x
      = (40 - 90 * t) / 29 * (701 / 2100) + x / 10 := by
  change awP₁.σ_dyn_top (awVS t) x (awα t x) = _
  rw [aw_σ_dyn_top ht hx (awα_mem ht hx), max_eq_right (awVertex_at_policy_nonneg ht hx),
    awVertex_at_policy]
  rfl

/-- **A continuum of equilibria at `β₁`.** For every `t ∈ [0, 4/9]` there is a top-selector
equilibrium whose policy is `t + (287/4206)x` and whose realised sanction is
`((40 − 90t)/29)(701/2100) + x/10`; distinct `t` give distinct policies, and for `t < 4/9`
the sanction is positive at every state. -/
theorem aw_continuum :
    (∀ t ∈ Icc (0 : ℝ) (4 / 9), ∃ Q : awP₁.FeedbackStackelbergEquilibriumTop,
      (∀ x ∈ Sanctions.I, Q.α x = t + 287 / 4206 * x) ∧
      (∀ x ∈ Sanctions.I,
        awP₁.dynamicEquilibriumRule Q x = (40 - 90 * t) / 29 * (701 / 2100) + x / 10)) ∧
    (∀ t₁ ∈ Icc (0 : ℝ) (4 / 9), ∀ t₂ ∈ Icc (0 : ℝ) (4 / 9), t₁ ≠ t₂ →
      ∀ Q₁ Q₂ : awP₁.FeedbackStackelbergEquilibriumTop,
        (∀ x ∈ Sanctions.I, Q₁.α x = t₁ + 287 / 4206 * x) →
        (∀ x ∈ Sanctions.I, Q₂.α x = t₂ + 287 / 4206 * x) → Q₁.α 0 ≠ Q₂.α 0) ∧
    (∀ t ∈ Ico (0 : ℝ) (4 / 9), ∀ x ∈ Sanctions.I,
      0 < (40 - 90 * t) / 29 * (701 / 2100) + x / 10) := by
  refine ⟨fun t ht => ⟨awEquilibrium t ht, fun _ _ => rfl, fun _ hx => aw_rule ht hx⟩,
    fun t₁ _ t₂ _ hne Q₁ Q₂ h₁ h₂ => ?_, fun t ht x hx => ?_⟩
  · rw [h₁ 0 ⟨le_rfl, zero_le_one⟩, h₂ 0 ⟨le_rfl, zero_le_one⟩]
    intro h; apply hne; linarith
  · have := ht.2; have := hx.1
    nlinarith

end

#print axioms Sanctions.Examples.awEquilibrium
#print axioms Sanctions.Examples.aw_rule
#print axioms Sanctions.Examples.aw_continuum

end Examples
end Sanctions
