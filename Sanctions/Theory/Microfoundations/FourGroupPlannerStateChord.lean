/-
Sanctions/Theory/Microfoundations/FourGroupPlannerStateChord.lean

**A lower state chord on the two endpoint sections sharpens the welfare gap**
(round BD, 2026-10-01; the remark of `app:fourgroup` previously marked "not
formalised").

`FourGroupPlanner.lean` §3 writes the discounted planner gap between the
zero-sanction and the full-sanction paths, under any transition that keeps the
cube and is monotone in both arguments, as `H/(1 − β) + B·Σ_t β^t z_t`, with the
residual separation `z_t = 1 − e_t + y_t` of the two endpoint paths
(`pathValue_cornerF_gap`). For `B ≥ 0` its lower bound used only `z_0 = 1`
(`pathValue_cornerF_gap_ge_of_nonneg`: `H/(1 − β) + B`). This file proves the
sharpening the appendix stated in prose: if the transition moves the state at
least at rate `g` along the two endpoint sections, the residual decays no faster
than `g^t`, so

`V⁰ − Vᴱ ≥ H/(1 − β) + B/(1 − β·g)`  (`pathValue_cornerF_gap_ge_of_nonneg_of_cornerChords`).

**The hypothesis, in its weakest form.** Only the chord *to the fixed corner* on
each endpoint section is read: `g·y ≤ F(y, 0)` (from the corner `(0,0)`) and
`g·(1 − e) ≤ 1 − F(e, 1)` (to the corner `(1,1)`). A lower state chord at rate `g`
along the sections `s = 0` and `s = 1`, with the fixed diagonal at the two corners,
gives both (`cornerChords_of_sectionChords`); so does the chord economy's state
band `g_lo`. Then `z_{t+1} ≥ g·z_t` (`residualF_succ_ge`), `z_t ≥ g^t`
(`pow_le_residualF`) and `Σ β^t z_t ≥ 1/(1 − β·g)` (`inv_le_tsum_residualF`).
The rate satisfies `g ≤ 1` automatically (the chord to `(1,1)` at `e = 0`).

**Sharpness (affine-restricted, Rule 22).** Under the affine law at rate `δ` the
residual is exactly `(1 − δ)^t` (`residualF_affineF`), and the affine law has the
endpoint chord at `g = 1 − δ`; so the bound holds with equality there and the
coefficient `1/(1 − β·g)` cannot be raised uniformly.

General in `F` (Rule 22): no closed form, no strict adjustment, no continuity.
Rule 3: no new assumption on any existing result — this is a new theorem whose
chord hypothesis is the one the appendix remark already named. Since 2026-10-07
(BH6.2) the two welfare bounds are proved over bare coefficients
(`FourGroupCoeffs`, no region-(R) field) and the `FourGroup` forms are `rfl`
corollaries. Rule 19: the
residual lemmas mention no `Params` and could move to `Foundations/` with
`residualF`; they stay beside the definitions they are about.
-/
import Sanctions.Theory.Microfoundations.FourGroupPlanner

namespace Sanctions
namespace KaempferLowenberg

open Set

/-- **The section chords give the corner chords.** A lower state chord at rate
`g` along the zero-sanction and the full-sanction sections, with the fixed
diagonal at the two corners, gives `g·y ≤ F(y, 0)` and `g·(1 − e) ≤ 1 − F(e, 1)`
on `[0,1]`. -/
theorem cornerChords_of_sectionChords {F : ℝ → ℝ → ℝ} {g : ℝ}
    (hlo0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      g * (y₂ - y₁) ≤ F y₂ 0 - F y₁ 0)
    (hlo1 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      g * (y₂ - y₁) ≤ F y₂ 1 - F y₁ 1)
    (h00 : F 0 0 = 0) (h11 : F 1 1 = 1) :
    (∀ y ∈ Icc (0 : ℝ) 1, g * y ≤ F y 0) ∧
      ∀ e ∈ Icc (0 : ℝ) 1, g * (1 - e) ≤ 1 - F e 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨fun y hy => ?_, fun e he => ?_⟩
  · have := hlo0 0 h0 y hy hy.1
    rw [h00] at this
    linarith
  · have := hlo1 e he 1 h1 he.2
    rw [h11] at this
    linarith

/-- **One step of the residual under the corner chords**: `z_{t+1} ≥ g·z_t`. -/
theorem residualF_succ_ge {F : ℝ → ℝ → ℝ} {g : ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hc0 : ∀ y ∈ Icc (0 : ℝ) 1, g * y ≤ F y 0)
    (hc1 : ∀ e ∈ Icc (0 : ℝ) 1, g * (1 - e) ≤ 1 - F e 1)
    {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) (t : ℕ) :
    g * residualF F x0 t ≤ residualF F x0 (t + 1) := by
  have he := cornerPathF_mem_cube hF_mem hx0 t
  have hy := zeroPathF_mem_cube hF_mem hx0 t
  have a := hc0 _ hy
  have b := hc1 _ he
  simp only [residualF, cornerPathF_succ, zeroPathF_succ]
  nlinarith

/-- **The residual decays no faster than `g^t`.** -/
theorem pow_le_residualF {F : ℝ → ℝ → ℝ} {g : ℝ} (hg : 0 ≤ g)
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hc0 : ∀ y ∈ Icc (0 : ℝ) 1, g * y ≤ F y 0)
    (hc1 : ∀ e ∈ Icc (0 : ℝ) 1, g * (1 - e) ≤ 1 - F e 1)
    {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) : ∀ t, g ^ t ≤ residualF F x0 t
  | 0 => by simp
  | t + 1 => by
      have ih := pow_le_residualF hg hF_mem hc0 hc1 hx0 t
      have hs := residualF_succ_ge hF_mem hc0 hc1 hx0 t
      calc g ^ (t + 1) = g * g ^ t := by ring
        _ ≤ g * residualF F x0 t := mul_le_mul_of_nonneg_left ih hg
        _ ≤ residualF F x0 (t + 1) := hs

/-- **The corner chord rate is at most one**: the chord to `(1,1)` at `e = 0`
reads `g ≤ 1 − F(0, 1) ≤ 1`. -/
theorem cornerChord_rate_le_one {F : ℝ → ℝ → ℝ} {g : ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hc1 : ∀ e ∈ Icc (0 : ℝ) 1, g * (1 - e) ≤ 1 - F e 1) : g ≤ 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have := hc1 0 h0
  have hF := (hF_mem 0 1 h0 h1).1
  linarith

/-- **`Σ_t β^t z_t ≥ 1/(1 − β·g)`** under the corner chords at a rate `g ≥ 0`. -/
theorem inv_le_tsum_residualF {F : ℝ → ℝ → ℝ} {g : ℝ} (hg : 0 ≤ g)
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hc0 : ∀ y ∈ Icc (0 : ℝ) 1, g * y ≤ F y 0)
    (hc1 : ∀ e ∈ Icc (0 : ℝ) 1, g * (1 - e) ≤ 1 - F e 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1) :
    1 / (1 - β * g) ≤ ∑' t : ℕ, β ^ t * residualF F x0 t := by
  have hg1 := cornerChord_rate_le_one hF_mem hc1
  have hβg0 : 0 ≤ β * g := mul_nonneg hβ.1 hg
  have hβg1 : β * g < 1 :=
    (mul_le_of_le_one_right hβ.1 hg1).trans_lt hβ.2
  have hgeo : Summable (fun t : ℕ => (β * g) ^ t) := summable_geometric_of_lt_one hβg0 hβg1
  have hz := residualF_summable hF_mem hF_mono_x hF_mono_s hβ hx0
  rw [one_div, ← tsum_geometric_of_lt_one hβg0 hβg1]
  refine hgeo.tsum_le_tsum (fun t => ?_) hz
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_residualF hg hF_mem hc0 hc1 hx0 t)
    (pow_nonneg hβ.1 t)

/-- **Sharpness at the affine law (affine-restricted, Rule 22).** Under
`F = affineF δ` the residual is exactly `(1 − δ)^t`, the equality case of
`pow_le_residualF` at `g = 1 − δ`. -/
theorem residualF_affineF (δ x0 : ℝ) (t : ℕ) :
    residualF (AbstractGame.affineF δ) x0 t = (1 - δ) ^ t := by
  rw [residualF, cornerPathF_affineF, zeroPathF_affineF]
  simp only [affineCornerPath, affineZeroPath]
  ring

/-- The affine law has the corner chords at `g = 1 − δ`, with equality. -/
theorem affineF_cornerChords (δ : ℝ) :
    (∀ y ∈ Icc (0 : ℝ) 1, (1 - δ) * y ≤ AbstractGame.affineF δ y 0) ∧
      ∀ e ∈ Icc (0 : ℝ) 1, (1 - δ) * (1 - e) ≤ 1 - AbstractGame.affineF δ e 1 := by
  refine ⟨fun y _ => ?_, fun e _ => ?_⟩ <;> simp only [AbstractGame.affineF] <;> linarith

namespace FourGroupCoeffs

variable (G : FourGroupCoeffs)

/-- **The sharpened welfare-gap bound.** For a transition that keeps the cube, is
monotone in both arguments, and moves the state at least at rate `g ≥ 0` toward
the fixed corners along the two endpoint sections, and for a nonnegative
transition coefficient `B = b_J − b_K`, the discounted planner gap between the
zero-sanction and the full-sanction paths is at least
`H/(1 − β) + B/(1 − β·g)`, with `H = (k_S + d_s) − (g_J − q_K) − B`. This replaces
the `B` of `pathValue_cornerF_gap_ge_of_nonneg` (the date-zero residual alone) by
`B/(1 − β·g)`, and is attained under the affine law at `g = 1 − δ`
(`residualF_affineF`). General in `F`. Coefficient form (BH6.2, 2026-10-07): no
region-(R) field is assumed, so it holds for every coefficient vector. -/
theorem pathValue_cornerF_gap_ge_of_nonneg_of_cornerChords {F : ℝ → ℝ → ℝ} {g : ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hg : 0 ≤ g)
    (hc0 : ∀ y ∈ Icc (0 : ℝ) 1, g * y ≤ F y 0)
    (hc1 : ∀ e ∈ Icc (0 : ℝ) 1, g * (1 - e) ≤ 1 - F e 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1)
    (hB : 0 ≤ G.b_J - G.b_K) :
    ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) / (1 - β * g)
      ≤ G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
          - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1) := by
  rw [G.pathValue_cornerF_gap hF_mem hF_mono_x hF_mono_s hβ hx0]
  have hS := inv_le_tsum_residualF hg hF_mem hF_mono_x hF_mono_s hc0 hc1 hβ hx0
  have hmul := mul_le_mul_of_nonneg_left hS hB
  rw [mul_one_div] at hmul
  linarith

/-- **The same bound from section chords**: a lower state chord at rate `g ≥ 0`
along the sections `s = 0` and `s = 1`, with the fixed diagonal at the corners.
General in `F`. Coefficient form (BH6.2, 2026-10-07): no region-(R) field is
assumed. -/
theorem pathValue_cornerF_gap_ge_of_nonneg_of_sectionChords {F : ℝ → ℝ → ℝ} {g : ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (h00 : F 0 0 = 0) (h11 : F 1 1 = 1) (hg : 0 ≤ g)
    (hlo0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      g * (y₂ - y₁) ≤ F y₂ 0 - F y₁ 0)
    (hlo1 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      g * (y₂ - y₁) ≤ F y₂ 1 - F y₁ 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1)
    (hB : 0 ≤ G.b_J - G.b_K) :
    ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) / (1 - β * g)
      ≤ G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
          - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1) :=
  let hc := cornerChords_of_sectionChords hlo0 hlo1 h00 h11
  G.pathValue_cornerF_gap_ge_of_nonneg_of_cornerChords hF_mem hF_mono_x hF_mono_s hg hc.1 hc.2
    hβ hx0 hB

end FourGroupCoeffs

namespace FourGroup

variable (G : FourGroup)

/-- **The sharpened welfare-gap bound.** The `FourGroup` form of
`FourGroupCoeffs.pathValue_cornerF_gap_ge_of_nonneg_of_cornerChords`, by `rfl`
through `toCoeffs` (BH6.2); statement unchanged; general in `F`. -/
theorem pathValue_cornerF_gap_ge_of_nonneg_of_cornerChords {F : ℝ → ℝ → ℝ} {g : ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hg : 0 ≤ g)
    (hc0 : ∀ y ∈ Icc (0 : ℝ) 1, g * y ≤ F y 0)
    (hc1 : ∀ e ∈ Icc (0 : ℝ) 1, g * (1 - e) ≤ 1 - F e 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1)
    (hB : 0 ≤ G.b_J - G.b_K) :
    ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) / (1 - β * g)
      ≤ G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
          - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1) :=
  G.toCoeffs.pathValue_cornerF_gap_ge_of_nonneg_of_cornerChords hF_mem hF_mono_x hF_mono_s
    hg hc0 hc1 hβ hx0 hB

/-- **The same bound from section chords.** The `FourGroup` form of
`FourGroupCoeffs.pathValue_cornerF_gap_ge_of_nonneg_of_sectionChords`, by `rfl`
through `toCoeffs` (BH6.2); statement unchanged; general in `F`. -/
theorem pathValue_cornerF_gap_ge_of_nonneg_of_sectionChords {F : ℝ → ℝ → ℝ} {g : ℝ}
    (hF_mem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F x s ∈ Icc (0 : ℝ) 1)
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (h00 : F 0 0 = 0) (h11 : F 1 1 = 1) (hg : 0 ≤ g)
    (hlo0 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      g * (y₂ - y₁) ≤ F y₂ 0 - F y₁ 0)
    (hlo1 : ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      g * (y₂ - y₁) ≤ F y₂ 1 - F y₁ 1)
    {β : ℝ} (hβ : β ∈ Ico (0 : ℝ) 1) {x0 : ℝ} (hx0 : x0 ∈ Icc (0 : ℝ) 1)
    (hB : 0 ≤ G.b_J - G.b_K) :
    ((G.kS + G.d_s) - (G.g_J - G.q_K) - (G.b_J - G.b_K)) / (1 - β)
        + (G.b_J - G.b_K) / (1 - β * g)
      ≤ G.pathValue β (zeroPathF F x0) (fun _ => 0) (fun _ => 0)
          - G.pathValue β (cornerPathF F x0) (fun _ => 0) (fun _ => 1) :=
  G.toCoeffs.pathValue_cornerF_gap_ge_of_nonneg_of_sectionChords hF_mem hF_mono_x hF_mono_s
    h00 h11 hg hlo0 hlo1 hβ hx0 hB

end FourGroup

end KaempferLowenberg
end Sanctions

#print axioms Sanctions.KaempferLowenberg.cornerChords_of_sectionChords
#print axioms Sanctions.KaempferLowenberg.residualF_succ_ge
#print axioms Sanctions.KaempferLowenberg.pow_le_residualF
#print axioms Sanctions.KaempferLowenberg.inv_le_tsum_residualF
#print axioms Sanctions.KaempferLowenberg.residualF_affineF
open Sanctions.KaempferLowenberg in
#print axioms FourGroup.pathValue_cornerF_gap_ge_of_nonneg_of_cornerChords
open Sanctions.KaempferLowenberg in
#print axioms FourGroup.pathValue_cornerF_gap_ge_of_nonneg_of_sectionChords
open Sanctions.KaempferLowenberg in
#print axioms FourGroupCoeffs.pathValue_cornerF_gap_ge_of_nonneg_of_cornerChords
