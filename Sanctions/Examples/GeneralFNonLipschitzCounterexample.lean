/-
Sanctions/Examples/GeneralFNonLipschitzCounterexample.lean

A concrete disprove-first witness showing that the maintained qualitative
general-transition assumptions do not imply any finite action-Lipschitz
modulus.

On feasible inputs the transition is the square-root quasi-arithmetic mean

  M(x, s) = ((sqrt x + sqrt s) / 2)^2.

The global definition uses clipped inputs and the monotone residual
`x - clipS x`, which preserves the unrestricted diagonal `F(x, x) = x`.
On `[0,1]^2` the residual vanishes, so the transition is exactly `M`.
-/

import Sanctions.Postulates.AbstractGame
import Sanctions.Domain.UnitIntervalProjection

namespace Sanctions

open Set

noncomputable section

namespace AbstractGame

/-- Square-root quasi-arithmetic mean applied to clipped inputs. -/
def clippedSqrtMean (x s : ℝ) : ℝ :=
  ((Real.sqrt (Sanctions.clipS x) + Real.sqrt (Sanctions.clipS s)) / 2) ^ 2

/-- Global transition extension.  The residual term makes the diagonal hold
on all reals while agreeing with `clippedSqrtMean` on feasible states. -/
def sqrtMeanTransition (x s : ℝ) : ℝ :=
  x - Sanctions.clipS x + clippedSqrtMean x s

private theorem clipS_eq_self_of_mem {x : ℝ} (hx : x ∈ (Sanctions.S : Set ℝ)) :
    Sanctions.clipS x = x :=
  Sanctions.clipS'_val_eq_of_mem hx

@[simp] theorem clippedSqrtMean_diag (x : ℝ) :
    clippedSqrtMean x x = Sanctions.clipS x := by
  have hx0 : 0 ≤ Sanctions.clipS x := (Sanctions.clipS_mem x).1
  have hsqrt := Real.sq_sqrt hx0
  unfold clippedSqrtMean
  nlinarith

theorem clippedSqrtMean_mono_left {x y s : ℝ} (hxy : x ≤ y) :
    clippedSqrtMean x s ≤ clippedSqrtMean y s := by
  have hroot :
      Real.sqrt (Sanctions.clipS x) ≤ Real.sqrt (Sanctions.clipS y) :=
    Real.sqrt_le_sqrt (Sanctions.clipS_mono hxy)
  have hx0 := Real.sqrt_nonneg (Sanctions.clipS x)
  have hy0 := Real.sqrt_nonneg (Sanctions.clipS y)
  have hs0 := Real.sqrt_nonneg (Sanctions.clipS s)
  unfold clippedSqrtMean
  nlinarith

theorem clippedSqrtMean_mono_right {x s t : ℝ} (hst : s ≤ t) :
    clippedSqrtMean x s ≤ clippedSqrtMean x t := by
  have hroot :
      Real.sqrt (Sanctions.clipS s) ≤ Real.sqrt (Sanctions.clipS t) :=
    Real.sqrt_le_sqrt (Sanctions.clipS_mono hst)
  have hx0 := Real.sqrt_nonneg (Sanctions.clipS x)
  have hs0 := Real.sqrt_nonneg (Sanctions.clipS s)
  have ht0 := Real.sqrt_nonneg (Sanctions.clipS t)
  unfold clippedSqrtMean
  nlinarith

theorem clippedSqrtMean_strict_right {x s t : ℝ}
    (hx : x ∈ (Sanctions.S : Set ℝ))
    (hs : s ∈ (Sanctions.S : Set ℝ))
    (ht : t ∈ (Sanctions.S : Set ℝ))
    (hst : s < t) :
    clippedSqrtMean x s < clippedSqrtMean x t := by
  have hcx := clipS_eq_self_of_mem hx
  have hcs := clipS_eq_self_of_mem hs
  have hct := clipS_eq_self_of_mem ht
  have hroot : Real.sqrt s < Real.sqrt t :=
    Real.sqrt_lt_sqrt hs.1 hst
  have hx0 := Real.sqrt_nonneg x
  have hs0 := Real.sqrt_nonneg s
  have ht0 := Real.sqrt_nonneg t
  unfold clippedSqrtMean
  rw [hcx, hcs, hct]
  nlinarith

/-- Replace only the transition of an existing parameter vector by the
square-root mean transition. -/
def Params.sqrtMeanTransitionParams (p : Params) : Params :=
  { p with
    F := sqrtMeanTransition
    F_continuous := by
      have hclipX : Continuous (fun xs : ℝ × ℝ => Sanctions.clipS xs.1) :=
        Sanctions.clipS_continuous.comp continuous_fst
      have hclipS : Continuous (fun xs : ℝ × ℝ => Sanctions.clipS xs.2) :=
        Sanctions.clipS_continuous.comp continuous_snd
      have hrootX :
          Continuous (fun xs : ℝ × ℝ => Real.sqrt (Sanctions.clipS xs.1)) :=
        Real.continuous_sqrt.comp hclipX
      have hrootS :
          Continuous (fun xs : ℝ × ℝ => Real.sqrt (Sanctions.clipS xs.2)) :=
        Real.continuous_sqrt.comp hclipS
      exact (continuous_fst.sub hclipX).add
        (((hrootX.add hrootS).div_const 2).pow 2)
    F_mono_x := by
      intro s x y hxy
      have hclip : Sanctions.clipS x ≤ Sanctions.clipS y :=
        Sanctions.clipS_mono hxy
      have hlip := Sanctions.clipS_lipschitz_abs x y
      rw [abs_of_nonpos (sub_nonpos.mpr hclip),
        abs_of_nonpos (sub_nonpos.mpr hxy)] at hlip
      have hres : x - Sanctions.clipS x ≤ y - Sanctions.clipS y := by
        linarith
      exact add_le_add hres (clippedSqrtMean_mono_left hxy)
    F_mono_s := by
      intro x s t hst
      change x - Sanctions.clipS x + clippedSqrtMean x s
        ≤ x - Sanctions.clipS x + clippedSqrtMean x t
      exact add_le_add (le_refl _) (clippedSqrtMean_mono_right hst)
    F_diag := by
      intro x
      simp [sqrtMeanTransition] }

namespace Params

variable {p : Params}

/-- The square-root mean transition satisfies strict movement toward the
current sanction on the feasible square. -/
theorem sqrtMeanTransitionParams_strictAdjustment :
    p.sqrtMeanTransitionParams.StrictAdjustment := by
  constructor
  · intro x s hx hs hsx
    change sqrtMeanTransition x s < x
    rw [sqrtMeanTransition, clipS_eq_self_of_mem hx, sub_self, zero_add]
    calc
      clippedSqrtMean x s < clippedSqrtMean x x :=
        clippedSqrtMean_strict_right hx hs hx hsx
      _ = x := by
        rw [clippedSqrtMean_diag, clipS_eq_self_of_mem hx]
  · intro x s hx hs hxs
    change x < sqrtMeanTransition x s
    rw [sqrtMeanTransition, clipS_eq_self_of_mem hx, sub_self, zero_add]
    calc
      x = clippedSqrtMean x x := by
        rw [clippedSqrtMean_diag, clipS_eq_self_of_mem hx]
      _ < clippedSqrtMean x s :=
        clippedSqrtMean_strict_right hx hx hs hxs

/-- The clipped action map of the square-root mean transition has no finite
global Lipschitz modulus on the feasible square. -/
theorem sqrtMeanTransitionParams_no_finite_action_lipschitz :
    ¬ ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ (Sanctions.S : Set ℝ), ∀ s ∈ Sanctions.I, ∀ t ∈ Sanctions.I,
        |(Sanctions.clipS' (p.sqrtMeanTransitionParams.F x s)).val
            - (Sanctions.clipS' (p.sqrtMeanTransitionParams.F x t)).val|
          ≤ L * |s - t| := by
  rintro ⟨L, hL, hLip⟩
  let r : ℝ := 1 / (4 * (L + 1))
  let t : ℝ := r ^ 2
  have hden : 0 < 4 * (L + 1) := by positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    rw [div_le_one₀ hden]
    nlinarith
  have ht0 : 0 ≤ t := sq_nonneg r
  have ht1 : t ≤ 1 := by
    dsimp [t]
    nlinarith
  have hx : (1 : ℝ) ∈ (Sanctions.S : Set ℝ) := by
    simp [Sanctions.S, Sanctions.I]
  have h0 : (0 : ℝ) ∈ Sanctions.I := by simp [Sanctions.I]
  have ht : t ∈ Sanctions.I := ⟨ht0, ht1⟩
  have hbound := hLip 1 hx 0 h0 t ht
  have hF0 : p.sqrtMeanTransitionParams.F 1 0 = 1 / 4 := by
    norm_num [sqrtMeanTransitionParams, sqrtMeanTransition,
      clippedSqrtMean, Sanctions.clipS]
  have hsqrtt : Real.sqrt t = r := by
    dsimp [t]
    exact Real.sqrt_sq hr.le
  have hFt :
      p.sqrtMeanTransitionParams.F 1 t = 1 / 4 + r / 2 + r ^ 2 / 4 := by
    rw [show p.sqrtMeanTransitionParams.F 1 t = sqrtMeanTransition 1 t by rfl]
    rw [sqrtMeanTransition, clipS_eq_self_of_mem hx, sub_self, zero_add]
    unfold clippedSqrtMean
    rw [clipS_eq_self_of_mem hx, clipS_eq_self_of_mem ht, hsqrtt]
    norm_num
    ring
  have hF0_mem :
      p.sqrtMeanTransitionParams.F 1 0 ∈ (Sanctions.S : Set ℝ) :=
    p.sqrtMeanTransitionParams.F_mem 1 0 hx h0
  have hFt_mem :
      p.sqrtMeanTransitionParams.F 1 t ∈ (Sanctions.S : Set ℝ) :=
    p.sqrtMeanTransitionParams.F_mem 1 t hx ht
  rw [Sanctions.clipS'_val_eq_of_mem hF0_mem,
    Sanctions.clipS'_val_eq_of_mem hFt_mem, hF0, hFt] at hbound
  have habs_left :
      |(1 / 4 : ℝ) - (1 / 4 + r / 2 + r ^ 2 / 4)|
        = r / 2 + r ^ 2 / 4 := by
    rw [abs_of_nonpos]
    · ring
    · nlinarith [sq_nonneg r]
  have habs_right : |(0 : ℝ) - t| = t := by
    rw [abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr ht0
  rw [habs_left, habs_right] at hbound
  have hdenr : (4 * (L + 1)) * r = 1 := by
    dsimp [r]
    field_simp
  have hdenr_mul : 4 * L * r ^ 2 + 4 * r ^ 2 = r := by
    calc
      4 * L * r ^ 2 + 4 * r ^ 2 = r * ((4 * (L + 1)) * r) := by ring
      _ = r := by rw [hdenr, mul_one]
  dsimp [t] at hbound
  nlinarith

/-- **The baseline transition can amplify a sanction difference.**

The internality results of `Foundations/DiagonalMonotone.lean` are *radial*: they
bound `|F x s - x|` by `|s - x|`, the distance of the sanction from the state
the transition starts at. They do **not** bound `|F x s - F x t|` by `|s - t|`,
and this theorem is why that distinction has to be kept.

At `x = 1` the square-root mean answers the sanction `0` with `1/4` and the
sanction `1/4` with `9/16`. The sanctions are `1/4` apart; the states they
produce are `5/16` apart. So the transition is not nonexpansive in the sanction,
even though it is monotone in each argument, fixes its diagonal, is continuous,
and keeps the feasible square invariant — every transition field of `Params`.

Rule 11: this is the Lean artifact behind the prose correction. Rule 9: an
existence certificate refuting a universal, and nothing more — it says the
baseline does not *imply* pairwise nonexpansiveness, not that any particular
economy fails it. Weaker than
`sqrtMeanTransitionParams_no_finite_action_lipschitz`, which refutes every finite
modulus at once; stated separately because modulus `1` is the one the internality
prose is at risk of being read as claiming. -/
theorem sqrtMeanTransitionParams_not_pairwise_nonexpansive :
    ¬ ∀ x ∈ (Sanctions.S : Set ℝ), ∀ s ∈ Sanctions.I, ∀ t ∈ Sanctions.I,
        |p.sqrtMeanTransitionParams.F x s
            - p.sqrtMeanTransitionParams.F x t| ≤ |s - t| := by
  intro hLip
  have hx : (1 : ℝ) ∈ (Sanctions.S : Set ℝ) := by simp [Sanctions.S, Sanctions.I]
  have hs : (1 / 4 : ℝ) ∈ Sanctions.I := by constructor <;> norm_num
  have ht : (0 : ℝ) ∈ Sanctions.I := by simp [Sanctions.I]
  have hbound := hLip 1 hx (1 / 4) hs 0 ht
  have hF0 : p.sqrtMeanTransitionParams.F 1 0 = 1 / 4 := by
    norm_num [sqrtMeanTransitionParams, sqrtMeanTransition,
      clippedSqrtMean, Sanctions.clipS]
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hFs : p.sqrtMeanTransitionParams.F 1 (1 / 4) = 9 / 16 := by
    rw [show p.sqrtMeanTransitionParams.F 1 (1 / 4)
        = sqrtMeanTransition 1 (1 / 4) from rfl]
    rw [sqrtMeanTransition, clipS_eq_self_of_mem hx, sub_self, zero_add]
    unfold clippedSqrtMean
    rw [clipS_eq_self_of_mem hx, clipS_eq_self_of_mem hs, hsqrt]
    rw [Real.sqrt_one]
    norm_num
  rw [hF0, hFs] at hbound
  rw [show |(9 / 16 : ℝ) - 1 / 4| = 5 / 16 by rw [abs_of_nonneg] <;> norm_num,
    show |(1 / 4 : ℝ) - 0| = 1 / 4 by rw [abs_of_nonneg] <;> norm_num] at hbound
  norm_num at hbound

end Params
end AbstractGame

end

end Sanctions
