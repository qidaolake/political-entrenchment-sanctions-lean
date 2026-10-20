/-
Sanctions/Examples/NonAffineCornerWitness.lean

**Non-affine transition witness for the basin-corner equilibrium.**

The Phase-3 work made the transition a general primitive `Params.F`; the
basin-corner construction (`BasinCornerExistence.lean`) builds a
feedback-Stackelberg equilibrium for *any* monotone `F`. This file
discharges that construction at a transition that is **genuinely
non-affine** — i.e. not `affineF δ` for any `δ` — so the general-`F`
machinery is demonstrably not affine-only.

The transition is an **up-fast/down-slow ratchet**:

    F(x,s) = 3x/4 + s/4,  if s ≤ x,
             x/2 + s/2,   if x ≤ s.

Below the diagonal, lower sanctions unwind inherited power by one
quarter of the state-sanction gap. Above the diagonal, higher sanctions
entrench power by one half of the gap. The max representation is
piecewise-linear, so `F` is not affine; yet it maps `[0,1]²` into
`[0,1]`, is jointly continuous, is monotone in each argument (globally),
fixes the diagonal `F(x,x) = x`, and satisfies strict adjustment toward
the current sanction. This retains asymmetric political persistence
without the irreversible inaction region of the old witness.

The payoffs are the minimal `U_T = U_S = s`, `σ ≡ 1` specification (as in
`JointPositiveSanctions.lean`), which makes the corner dischargers apply:
`σ_dyn_top ≡ 1` (Sender objective maximized at the top sanction) and the
Target integrand is `a`-independent. The resulting equilibrium existence
`ratchetParams_feedbackStackelbergTop_corner_exists` is **constructed**
(through the general-`F` value fixed point `V_T_dyn`) and axiom-clean.

## Rule compliance

**Rule 1.** `σ ≡ 1` is the Sender stage argmax of `U_S = id`; the corner
`α ≡ 0` is certified optimal by the discharger (not asserted constant).

**Rule 5.** The corner existence is obtained through the *parametric*
dischargers in `BasinCornerExistence.lean`; this file only supplies the
witness `Params` and the two primitive inputs.

**Rule 19.** The non-affine `F` is project-specific witness data, so it
lives in `Examples/`, not `Foundations/`.
-/

import Sanctions.Theory.Equilibrium.BasinCornerExistence
import Sanctions.Theory.LockIn.LockInLimit

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

/-! ## The non-affine up-fast/down-slow ratchet transition -/

/-- **Up-fast/down-slow ratchet.** The max form is
`3x/4 + s/4 + max 0 (s-x)/4`: it adjusts one quarter of a downward
gap but one half of an upward gap. -/
def ratchetF : ℝ → ℝ → ℝ := fun x s =>
  (3 / 4 : ℝ) * x + (1 / 4 : ℝ) * s + (1 / 4 : ℝ) * max 0 (s - x)

/-- Below the diagonal, the ratchet closes one quarter of the gap. -/
lemma ratchetF_of_le {x s : ℝ} (h : s ≤ x) :
    ratchetF x s = (3 / 4 : ℝ) * x + (1 / 4 : ℝ) * s := by
  rw [ratchetF, max_eq_left (sub_nonpos.mpr h)]
  ring

/-- Above the diagonal, the ratchet closes one half of the gap. -/
lemma ratchetF_of_ge {x s : ℝ} (h : x ≤ s) :
    ratchetF x s = (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * s := by
  rw [ratchetF, max_eq_right (sub_nonneg.mpr h)]
  ring

/-- **`ratchetF` is not the affine law, for any adjustment weight.**

Rule 11 / Rule 9B: the file's title claim is machine-checked here rather than
left to its docstring. The kink does it in two points — below the diagonal
`F 1 0 = 3/4` forces `δ = 1/4`, while above it `F 0 1 = 1/2` forces `δ = 1/2`.
The up-fast/down-slow asymmetry is exactly the obstruction. -/
theorem ratchetF_ne_affineF (δ : ℝ) : ratchetF ≠ AbstractGame.affineF δ := by
  intro h
  have h1 : ratchetF 1 0 = AbstractGame.affineF δ 1 0 := by rw [h]
  have h2 : ratchetF 0 1 = AbstractGame.affineF δ 0 1 := by rw [h]
  rw [ratchetF_of_le (by norm_num : (0:ℝ) ≤ 1)] at h1
  rw [ratchetF_of_ge (by norm_num : (0:ℝ) ≤ 1)] at h2
  unfold AbstractGame.affineF at h1 h2
  norm_num at h1 h2
  linarith

/-! ### The five `Params` transition obligations, as named lemmas

Extracted from the body of `ratchetParams` so a second witness can reuse the
ratchet without restating forty lines of case analysis. `StrictTargetReluctanceWitness.lean`
is the first such reuse: it keeps this transition and changes only the payoffs.
The definition of `ratchetParams` is unchanged — these are the same proofs, named. -/

theorem ratchetF_mem : ∀ x s, x ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
    ratchetF x s ∈ Set.Icc (0 : ℝ) 1 := by
  rintro x s ⟨hx0, hx1⟩ ⟨hs0, hs1⟩
  by_cases hsx : s ≤ x
  · rw [ratchetF_of_le hsx]
    constructor <;> nlinarith
  · have hxs : x ≤ s := le_of_lt (lt_of_not_ge hsx)
    rw [ratchetF_of_ge hxs]
    constructor <;> nlinarith

theorem ratchetF_continuous :
    Continuous (fun (xs : ℝ × ℝ) => ratchetF xs.1 xs.2) := by
  unfold ratchetF
  fun_prop

theorem ratchetF_mono_x : ∀ s, Monotone (fun x => ratchetF x s) := by
  intro s x y hxy
  change ratchetF x s ≤ ratchetF y s
  by_cases hsx : s ≤ x
  · rw [ratchetF_of_le hsx, ratchetF_of_le (hsx.trans hxy)]
    linarith
  · have hxs : x ≤ s := le_of_lt (lt_of_not_ge hsx)
    by_cases hys : y ≤ s
    · rw [ratchetF_of_ge hxs, ratchetF_of_ge hys]
      linarith
    · have hsy : s ≤ y := le_of_lt (lt_of_not_ge hys)
      rw [ratchetF_of_ge hxs, ratchetF_of_le hsy]
      linarith

theorem ratchetF_mono_s : ∀ x, Monotone (fun s => ratchetF x s) := by
  intro x s t hst
  change ratchetF x s ≤ ratchetF x t
  by_cases hsx : s ≤ x
  · by_cases htx : t ≤ x
    · rw [ratchetF_of_le hsx, ratchetF_of_le htx]
      linarith
    · have hxt : x ≤ t := le_of_lt (lt_of_not_ge htx)
      rw [ratchetF_of_le hsx, ratchetF_of_ge hxt]
      linarith
  · have hxs : x ≤ s := le_of_lt (lt_of_not_ge hsx)
    rw [ratchetF_of_ge hxs, ratchetF_of_ge (hxs.trans hst)]
    linarith

theorem ratchetF_diag : ∀ x, ratchetF x x = x := by
  intro x
  rw [ratchetF_of_le le_rfl]
  ring

/-! ## Witness parameters (non-affine `F`, minimal payoffs) -/

/-- **Non-affine witness parameters.** Identical to `jointPositiveParams`
except the transition is the non-affine ratchet `ratchetF` rather than
`affineF δ`. -/
def ratchetParams : AbstractGame.Params where
  δ := 1/2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 1/2
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1/2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := fun _ _ s => s
  U_S := fun _ _ s => s
  σ := fun _ _ => 1
  σ_mem := fun _ _ => ⟨by norm_num, le_refl _⟩
  σ_isMaxOn_U_S := fun _ _ s hs => hs.2
  U_T_continuous := continuous_snd.comp continuous_snd
  U_S_continuous := continuous_snd.comp continuous_snd
  F := ratchetF
  F_continuous := ratchetF_continuous
  F_mono_x := ratchetF_mono_x
  F_mono_s := ratchetF_mono_s
  F_diag := ratchetF_diag

/-- **`ratchetParams` has a continuous static Sender selector.** A concrete member with
the non-affine transition `ratchetF`; the selector itself does not read the transition.
The proof is the one that was the economy's `σ_continuous` field until round BJ5.1
(2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance ratchetParams_staticSelectorContinuous :
    ratchetParams.StaticSelectorContinuous where
  σ_continuous := continuous_const

@[simp] lemma ratchetParams_U_S (x a s : ℝ) : ratchetParams.U_S x a s = s := rfl
@[simp] lemma ratchetParams_U_T (x a s : ℝ) : ratchetParams.U_T x a s = s := rfl

/-- The non-affine ratchet satisfies the maintained strict-adjustment
condition: it moves down by one quarter of a negative gap and up by one
half of a positive gap. -/
theorem ratchetParams_strictAdjustment : ratchetParams.StrictAdjustment := by
  constructor
  · intro x s _ _ hsx
    rw [show ratchetParams.F x s = ratchetF x s from rfl,
      ratchetF_of_le (le_of_lt hsx)]
    linarith
  · intro x s _ _ hxs
    rw [show ratchetParams.F x s = ratchetF x s from rfl,
      ratchetF_of_ge (le_of_lt hxs)]
    linarith

/-- **`ratchetF` is not affine.** Sanity check that this witness genuinely
exercises the general-`F` path: at `(x, s) = (1, 0)` the ratchet gives
`F(1,0) = 3/4`, whereas the affine law `affineF (1/2)` gives `1/2`.
The two transitions disagree, so `ratchetF ≠ affineF (1/2)`. -/
example : ratchetF 1 0 ≠ AbstractGame.affineF (1/2) 1 0 := by
  rw [ratchetF_of_le (by norm_num)]
  simp only [AbstractGame.affineF]
  norm_num

/-! ## Corner equilibrium existence at the non-affine witness -/

/-- The Sender value at the corner policy `α ≡ 0` is monotone (because
`U_S = s` is `x`-independent). -/
theorem ratchetParams_V_S0_monotone :
    Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x => ratchetParams.V_S (fun _ => 0) continuous_const x) :=
  ratchetParams.V_S_monotone_of_integrand_monotone continuous_const
    (by intro s _ x _ y _ _; simp [ratchetParams_U_S])

/-- `σ_dyn_top ≡ 1` at the corner Sender value — via the parametric
discharger, exactly as in the affine case (the argument only uses
`F_mono_s`, which the ratchet satisfies). -/
theorem ratchetParams_σ_dyn_top_V_S0_eq_one (x a : ℝ) :
    ratchetParams.σ_dyn_top
      (ratchetParams.V_S (fun _ => 0) continuous_const) x a = 1 :=
  ratchetParams.σ_dyn_top_V_S_zero_eq_one_of_monotone
    ratchetParams_V_S0_monotone
    (fun x a s hs => by simp only [ratchetParams_U_S]; exact hs.2) x a

/-- **A genuine feedback-Stackelberg equilibrium exists at the saturated
corner under the NON-AFFINE ratchet transition.** Constructed through the
general-`F` single-agent value fixed point `V_T_dyn`; the affine-only
Schur/contraction route does not apply here. This certifies that the
Phase-3 general-`F` existence machinery is non-vacuous at a transition
that is not `affineF δ`. -/
theorem ratchetParams_feedbackStackelbergTop_corner_exists :
    ∃ E : ratchetParams.FeedbackStackelbergEquilibriumTop, E.α = (fun _ => 0) :=
  ratchetParams.feedbackStackelbergTop_corner_exists_of_σtop_one
    ratchetParams_σ_dyn_top_V_S0_eq_one
    (fun _ _ _ => rfl)

/-! ## General-`F` orbit and least selected fixed point -/

/-- **The general-`F` lower-orbit bound holds at the non-affine ratchet.**
At the zero policy, the greatest dynamic Sender sanction is identically one,
so the realized rule is monotone and satisfies the basin level condition on
`[0,1]`. The general theorem therefore gives an equilibrium-consistent limit
for both state and sanction paths, together with a least fixed point of the
greatest-selector step that weakly bounds that orbit limit from above. -/
theorem ratchetParams_generalF_lowerOrbit_below_least_fixedPoint :
    let V_S0 := ratchetParams.V_S (fun _ => 0) continuous_const
    ∃ xl ∈ Set.Icc (0 : ℝ) 1, ∃ xf ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (ratchetParams.dynamicTopLockInPathF V_S0 (fun _ => 0) 0)
        atTop (𝓝 xl) ∧
      Tendsto (ratchetParams.dynamicTopLockInSanctionsF V_S0 (fun _ => 0) 0)
        atTop (𝓝 xl) ∧
      xl ∈ ratchetParams.dynamicArgmaxSet V_S0 xl 0 ∧
      xl ≤ ratchetParams.dynamicTopRealizedRule V_S0 (fun _ => 0) xl ∧
      ratchetParams.dynamicTopLockInStepF V_S0 (fun _ => 0) xf = xf ∧
      ratchetParams.dynamicTopRealizedRule V_S0 (fun _ => 0) xf = xf ∧
      xl ≤ xf ∧
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ratchetParams.dynamicTopLockInStepF V_S0 (fun _ => 0) y = y → xf ≤ y := by
  dsimp only
  apply ratchetParams.dynamicTopLockInPathF_tendsto_below_least_fixedPoint_of_rule_mono
    ratchetParams_strictAdjustment
      (ratchetParams.V_S (fun _ => 0) continuous_const) (fun _ => 0)
      continuous_const (xbar := 0) (sbar := 0) (by norm_num) (by norm_num)
  · intro x hx
    change max x 0 ≤ ratchetParams.σ_dyn_top
      (ratchetParams.V_S (fun _ => 0) continuous_const) x 0
    rw [ratchetParams_σ_dyn_top_V_S0_eq_one x 0]
    simpa only [max_eq_left hx.1] using hx.2
  · intro x hx y hy hxy
    change ratchetParams.σ_dyn_top
        (ratchetParams.V_S (fun _ => 0) continuous_const) x 0 ≤
      ratchetParams.σ_dyn_top
        (ratchetParams.V_S (fun _ => 0) continuous_const) y 0
    rw [ratchetParams_σ_dyn_top_V_S0_eq_one x 0,
      ratchetParams_σ_dyn_top_V_S0_eq_one y 0]

/-- **At the non-affine ratchet witness, both the lower-orbit limit and
the least greatest-selector fixed point are exactly one.**

The general theorem only gives `x_L ≤ x_F`. At this witness the realized
dynamic sanction rule is identically one. Hence the sanction sequence is
constant at one, uniqueness of limits forces `x_L = 1`, and the selected
fixed-point identity forces `x_F = 1`. This is a derived witness
corollary: it adds no primitive assumption and does not strengthen the
general theorem. -/
theorem ratchetParams_generalF_lowerOrbit_and_least_fixedPoint_eq_one :
    let V_S0 := ratchetParams.V_S (fun _ => 0) continuous_const
    Tendsto (ratchetParams.dynamicTopLockInPathF V_S0 (fun _ => 0) 0)
      atTop (𝓝 (1 : ℝ)) ∧
    Tendsto (ratchetParams.dynamicTopLockInSanctionsF V_S0 (fun _ => 0) 0)
      atTop (𝓝 (1 : ℝ)) ∧
    (1 : ℝ) ∈ ratchetParams.dynamicArgmaxSet V_S0 1 0 ∧
    ratchetParams.dynamicTopLockInStepF V_S0 (fun _ => 0) 1 = 1 ∧
    ratchetParams.dynamicTopRealizedRule V_S0 (fun _ => 0) 1 = 1 ∧
    ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ratchetParams.dynamicTopLockInStepF V_S0 (fun _ => 0) y = y → 1 ≤ y := by
  dsimp only
  obtain ⟨xl, hxl, xf, hxf, hpath, hsanctions, hargmax, hbelow,
      hstep, hfixedRule, hxlxf, hleast⟩ :=
    ratchetParams_generalF_lowerOrbit_below_least_fixedPoint
  have hrule_one (x : ℝ) :
      ratchetParams.dynamicTopRealizedRule
          (ratchetParams.V_S (fun _ => 0) continuous_const) (fun _ => 0) x = 1 := by
    unfold Sanctions.AbstractGame.Params.dynamicTopRealizedRule
    exact ratchetParams_σ_dyn_top_V_S0_eq_one x 0
  have hsanctions_one :
      Tendsto
        (ratchetParams.dynamicTopLockInSanctionsF
          (ratchetParams.V_S (fun _ => 0) continuous_const) (fun _ => 0) 0)
        atTop (𝓝 (1 : ℝ)) := by
    have hseq :
        ratchetParams.dynamicTopLockInSanctionsF
            (ratchetParams.V_S (fun _ => 0) continuous_const) (fun _ => 0) 0 =
          (fun _ : ℕ => (1 : ℝ)) := by
      funext n
      unfold Sanctions.AbstractGame.Params.dynamicTopLockInSanctionsF
      exact hrule_one _
    rw [hseq]
    exact tendsto_const_nhds
  have hxl_one : xl = 1 :=
    tendsto_nhds_unique hsanctions hsanctions_one
  have hxf_one : xf = 1 := by
    rw [hrule_one xf] at hfixedRule
    exact hfixedRule.symm
  subst xl
  subst xf
  exact ⟨hpath, hsanctions, hargmax, hstep, hrule_one 1, hleast⟩

end -- noncomputable section

end Examples

end Sanctions
#print axioms Sanctions.Examples.ratchetF_ne_affineF
