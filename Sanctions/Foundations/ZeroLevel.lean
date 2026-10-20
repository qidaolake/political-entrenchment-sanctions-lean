/-
Sanctions/Foundations/ZeroLevel.lean

**The least zero of an antitone family, and its continuity** (round AV,
2026-09-25; doc 104, the rate-bound programme).

Let `ρ : ℝ → ℝ → ℝ` be a family of functions `a ↦ ρ x a` on `[0,1]`, each
antitone and vanishing at `a = 1` (hence nonnegative on `[0,1]`, which is never
assumed separately). The **zero level** `level ρ x` is the least `a ∈ [0,1]` at
which `ρ x a = 0`. When `ρ` is jointly continuous on the parameter set times
`[0,1]` and has a *linear relief rate* below the zero level —
`ρ x a ≥ c·(level ρ x − a)` with `c > 0` — the zero level is continuous in `x`.

Everything here is general: `ρ` is an abstract two-argument family, so no
transition law `F` appears and nothing is affine-restricted. Continuity is only
ever asked on `[0,1]` in the second argument (round BG-1, 2026-10-06, item
BG1.7; the earlier forms asked for continuity on all of `ℝ`, for a per-`x`
continuity on top of the joint one, and for a separate nonnegativity
hypothesis).

The application is to a Sender's sanction response as a function of the Target's
compliance (the least compliance that buys complete relief), for the stage
response of the myopic reading and the forward-looking responses of the other
readings; nothing here names a game (Rule 19).

Proof of continuity. Lower semicontinuity: just below the zero level `ρ` is
positive, and positivity persists at nearby states by continuity. Upper
semicontinuity: just above the zero level `ρ` vanishes, so at nearby states it
is small, while the relief rate would make it large if the zero level had jumped
up.
-/
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace Sanctions
namespace ZeroLevel

open Set Filter Topology

/-- The zero set in `[0,1]` of `a ↦ ρ x a`. -/
def zeroSet (ρ : ℝ → ℝ → ℝ) (x : ℝ) : Set ℝ := Icc (0 : ℝ) 1 ∩ {a | ρ x a = 0}

/-- **The zero level**: the least `a ∈ [0,1]` at which `ρ x a` vanishes. -/
noncomputable def level (ρ : ℝ → ℝ → ℝ) (x : ℝ) : ℝ := sInf (zeroSet ρ x)

variable {ρ : ℝ → ℝ → ℝ}

theorem zeroSet_bddBelow (x : ℝ) : BddBelow (zeroSet ρ x) := ⟨0, fun _ ha => ha.1.1⟩

/-- **The zero set is closed** when `ρ x` is continuous on `[0,1]` (general:
abstract `ρ`). Before BG1.7 continuity on all of `ℝ` was assumed; only `[0,1]`
is read, because the zero set lies inside it. -/
theorem zeroSet_isClosed {x : ℝ} (hc : ContinuousOn (ρ x) (Icc (0 : ℝ) 1)) :
    IsClosed (zeroSet ρ x) :=
  hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton

/-- **The zero level is attained**: it lies in the zero set, given continuity
of `ρ x` on `[0,1]` and `ρ x 1 = 0` (general: abstract `ρ`; continuity on `ℝ`
is no longer assumed, BG1.7). -/
theorem level_mem_zeroSet {x : ℝ} (hc : ContinuousOn (ρ x) (Icc (0 : ℝ) 1))
    (h1 : ρ x 1 = 0) : level ρ x ∈ zeroSet ρ x :=
  (zeroSet_isClosed hc).csInf_mem ⟨1, ⟨⟨zero_le_one, le_rfl⟩, h1⟩⟩ (zeroSet_bddBelow x)

/-- **The zero level lies in `[0,1]`** (general: abstract `ρ`; continuity is
asked on `[0,1]` only, BG1.7). -/
theorem level_mem {x : ℝ} (hc : ContinuousOn (ρ x) (Icc (0 : ℝ) 1)) (h1 : ρ x 1 = 0) :
    level ρ x ∈ Icc (0 : ℝ) 1 :=
  (level_mem_zeroSet hc h1).1

/-- **The family vanishes at its zero level** (general: abstract `ρ`;
continuity is asked on `[0,1]` only, BG1.7). -/
theorem rho_level {x : ℝ} (hc : ContinuousOn (ρ x) (Icc (0 : ℝ) 1)) (h1 : ρ x 1 = 0) :
    ρ x (level ρ x) = 0 :=
  (level_mem_zeroSet hc h1).2

/-- Below the zero level the family is positive. -/
theorem rho_pos_of_lt {x a : ℝ} (hnn : 0 ≤ ρ x a) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : a < level ρ x) : 0 < ρ x a := by
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso
    have hmem : a ∈ zeroSet ρ x := ⟨⟨ha0, ha1⟩, h.symm⟩
    have := csInf_le (zeroSet_bddBelow x) hmem
    unfold level at ha
    linarith

/-- **At and above the zero level the family vanishes** (general: abstract
`ρ`). Antitonicity squeezes `ρ x a` between `ρ x 1 = 0` and the value `0` at
the zero level. Since BG1.7 the nonnegativity hypothesis is gone (it is the
lower half of that squeeze), and continuity is asked on `[0,1]` only. -/
theorem rho_eq_zero_of_ge {x a : ℝ} (hc : ContinuousOn (ρ x) (Icc (0 : ℝ) 1))
    (h1 : ρ x 1 = 0) (hanti : AntitoneOn (ρ x) (Icc (0 : ℝ) 1))
    (ha : level ρ x ≤ a) (ha1 : a ≤ 1) : ρ x a = 0 := by
  have hz := level_mem hc h1
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨le_trans hz.1 ha, ha1⟩
  have h := hanti hz haI ha
  rw [rho_level hc h1] at h
  have hnn : ρ x 1 ≤ ρ x a := hanti haI ⟨zero_le_one, le_rfl⟩ ha1
  rw [h1] at hnn
  exact le_antisymm h hnn

/-- **From a relief rate between levels below the zero level to a linear lower
bound at the zero level**, by a one-sided limit: if every step `a < a' <` zero
level lowers `ρ` by at least `c·(a' − a)` and `ρ ≥ 0` there, then
`ρ x a ≥ c·(level ρ x − a)`. No continuity is used. -/
theorem rho_ge_of_lt {x a c : ℝ} (hc0 : 0 < c)
    (hshift : ∀ a', a < a' → a' < level ρ x → c * (a' - a) ≤ ρ x a - ρ x a')
    (hnn : ∀ a', a < a' → a' < level ρ x → 0 ≤ ρ x a')
    (ha : a < level ρ x) : c * (level ρ x - a) ≤ ρ x a := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  set L := level ρ x with hL
  have hδc : 0 < δ / c := div_pos hδ hc0
  set a' := max ((a + L) / 2) (L - δ / c) with ha'
  have ha'1 : a < a' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have ha'2 : a' < L := max_lt (by linarith) (by linarith)
  have hkey := hshift a' ha'1 ha'2
  have hρ' := hnn a' ha'1 ha'2
  have hge : L - δ / c ≤ a' := le_max_right _ _
  have hcl : c * (L - a) ≤ c * (a' - a) + δ := by
    have := mul_le_mul_of_nonneg_left hge hc0.le
    have hcancel : c * (δ / c) = δ := by field_simp
    nlinarith [this, hcancel]
  linarith

theorem prod_dist_fst (x x₀ a : ℝ) : dist ((x, a) : ℝ × ℝ) (x₀, a) = dist x x₀ := by
  rw [Prod.dist_eq, dist_self]
  exact max_eq_left dist_nonneg

/-- **Continuity of the zero level.** On a set `X` of parameters, if `ρ` is
jointly continuous on `X × [0,1]`, each `ρ x ·` is antitone on `[0,1]` and
vanishes at `1`, and the relief rate `ρ x a ≥ c·(level ρ x − a)` holds below
the zero level with `c > 0`, then the zero level is continuous on `X`.

General: `ρ` is abstract, so no transition law appears. Round BG-1
(2026-10-06, item BG1.7) weakened the surface in three ways. Joint continuity
is asked on `X × [0,1]` rather than `X × ℝ`, since the proof only evaluates at
compliance levels in `[0,1]`. The separate per-`x` continuity is gone: it is
the joint continuity read along one slice. The nonnegativity hypothesis is
gone: antitonicity and `ρ x 1 = 0` give it. -/
theorem level_continuousOn {X : Set ℝ} {c : ℝ} (hc0 : 0 < c)
    (hjoint : ContinuousOn (fun xa : ℝ × ℝ => ρ xa.1 xa.2) (X ×ˢ Icc (0 : ℝ) 1))
    (h1 : ∀ x ∈ X, ρ x 1 = 0)
    (hanti : ∀ x ∈ X, AntitoneOn (ρ x) (Icc (0 : ℝ) 1))
    (hrate : ∀ x ∈ X, ∀ a ∈ Icc (0 : ℝ) 1, a < level ρ x → c * (level ρ x - a) ≤ ρ x a) :
    ContinuousOn (level ρ) X := by
  -- Per-slice continuity on `[0,1]`: the joint continuity read along `a ↦ (x, a)`.
  have hc : ∀ x ∈ X, ContinuousOn (ρ x) (Icc (0 : ℝ) 1) := fun x hx =>
    hjoint.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ha => ⟨hx, ha⟩)
  -- Nonnegativity on `[0,1]`, from antitonicity and the zero at `1`.
  have hnn : ∀ x ∈ X, ∀ b ∈ Icc (0 : ℝ) 1, 0 ≤ ρ x b := fun x hx b hb => by
    have h := hanti x hx hb ⟨zero_le_one, le_rfl⟩ hb.2
    rwa [h1 x hx] at h
  rw [Metric.continuousOn_iff]
  intro x₀ hx₀ η hη
  have hz₀I := level_mem (hc x₀ hx₀) (h1 x₀ hx₀)
  have hcont := Metric.continuousOn_iff.1 hjoint
  -- lower side
  have hlow : ∃ δ₁ > 0, ∀ x ∈ X, dist x x₀ < δ₁ → level ρ x₀ - η / 2 < level ρ x := by
    by_cases hcase : level ρ x₀ - η / 2 < 0
    · exact ⟨1, one_pos, fun x hx _ =>
        lt_of_lt_of_le hcase (level_mem (hc x hx) (h1 x hx)).1⟩
    · push_neg at hcase
      set a₁ := level ρ x₀ - η / 2 with ha₁
      have ha₁lt : a₁ < level ρ x₀ := by linarith
      have ha₁I : a₁ ∈ Icc (0 : ℝ) 1 := ⟨hcase, by linarith [hz₀I.2]⟩
      have hpos₀ := rho_pos_of_lt (hnn x₀ hx₀ a₁ ha₁I) ha₁I.1 ha₁I.2 ha₁lt
      obtain ⟨δ₁, hδ₁, hδ⟩ := hcont (x₀, a₁) ⟨hx₀, ha₁I⟩ (ρ x₀ a₁ / 2) (by linarith)
      refine ⟨δ₁, hδ₁, fun x hx hdx => ?_⟩
      have hnear := hδ (x, a₁) ⟨hx, ha₁I⟩ (by rw [prod_dist_fst]; exact hdx)
      simp only [Real.dist_eq] at hnear
      have hpos : 0 < ρ x a₁ := by
        have := abs_lt.1 hnear
        linarith [this.1]
      by_contra hcon
      push_neg at hcon
      have h0 := rho_eq_zero_of_ge (hc x hx) (h1 x hx) (hanti x hx) hcon ha₁I.2
      linarith
  -- upper side
  have hup : ∃ δ₂ > 0, ∀ x ∈ X, dist x x₀ < δ₂ → level ρ x ≤ level ρ x₀ + η / 2 := by
    by_cases hcase : 1 < level ρ x₀ + η / 2
    · exact ⟨1, one_pos, fun x hx _ => le_trans (level_mem (hc x hx) (h1 x hx)).2 hcase.le⟩
    · push_neg at hcase
      set a₂ := level ρ x₀ + η / 4 with ha₂
      have ha₂1 : a₂ ≤ 1 := by linarith
      have ha₂0 : 0 ≤ a₂ := by linarith [hz₀I.1]
      have hzero : ρ x₀ a₂ = 0 :=
        rho_eq_zero_of_ge (hc x₀ hx₀) (h1 x₀ hx₀) (hanti x₀ hx₀) (by linarith) ha₂1
      have hc₂pos : 0 < c * (η / 4) := by positivity
      obtain ⟨δ₂, hδ₂, hδ⟩ := hcont (x₀, a₂) ⟨hx₀, ha₂0, ha₂1⟩ (c * (η / 4)) hc₂pos
      refine ⟨δ₂, hδ₂, fun x hx hdx => ?_⟩
      have hnear := hδ (x, a₂) ⟨hx, ha₂0, ha₂1⟩ (by rw [prod_dist_fst]; exact hdx)
      simp only [Real.dist_eq, hzero, sub_zero] at hnear
      by_contra hcon
      push_neg at hcon
      have ha₂lt : a₂ < level ρ x := by linarith
      have hge := hrate x hx a₂ ⟨ha₂0, ha₂1⟩ ha₂lt
      have hmono : c * (η / 4) ≤ c * (level ρ x - a₂) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0.le
      have habs := (abs_lt.1 hnear).2
      linarith
  obtain ⟨δ₁, hδ₁, hlow'⟩ := hlow
  obtain ⟨δ₂, hδ₂, hup'⟩ := hup
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx hdx => ?_⟩
  have h1' := hlow' x hx (lt_of_lt_of_le hdx (min_le_left _ _))
  have h2' := hup' x hx (lt_of_lt_of_le hdx (min_le_right _ _))
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end ZeroLevel
end Sanctions

#print axioms Sanctions.ZeroLevel.rho_ge_of_lt
#print axioms Sanctions.ZeroLevel.level_continuousOn
