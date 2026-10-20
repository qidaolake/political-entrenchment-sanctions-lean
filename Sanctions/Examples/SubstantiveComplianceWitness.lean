/-
SubstantiveComplianceWitness.lean — a *substantive* (non-degenerate) witness.

Unlike the `StandardCompliancePolynomialSkeleton` "logical-floor" witness (whose
linear `U_S = s` pins the myopic Sender at the corner `σ ≡ 1`, making the
dynamic-over-myopic dominance degenerate), this witness uses a **concave,
state-dependent** Sender stage payoff

  U_S(x, a, s) = ½·s − ½·s² + ¾·x

with `δ = β_S = β_T = 1/2`. This yields:

* **Interior myopic response** `σ_myopic = ½` (argmax of `½s − ½s²` on `[0,1]`).
* A Sender value function with **positive slope**: matching `V_S(z) = A·z + B`
  through the Bellman fixed point gives `A = 1`, `B = 9/16`
  (`V_S*(z) = z + 9/16`).
* A **strictly larger** forward-looking response: with `V_S` of slope `1`,
  `σ_dyn = ½ + β_S·A·δ = 3/4 > ½ = σ_myopic` — a genuine strict dominance gap.

**Tractability trick.** We pin `carrier_S` to the *gain ball*
`valLipGainBall M_S 1 1 0` (Lipschitz `1` ∧ min-slope `1` ⇒ affine slope exactly
`1`). For every such `V_S`, `σ_dyn` is the constant `3/4`, so the Schur row
coupling decouples (`L_TS = L_ST = 0`) exactly as in the polynomial witness — yet
the dominance is strict because the *myopic comparator* uses `V_S ≡ 0` (slope 0).
The Target side is unchanged from the polynomial witness (`F`'s state-slope is
always `1/2`, independent of the `σ_dyn` value), so `carrier_T` is the same gain
ball `valLipGainBall M_T (20/3) (20/3) 0`.

This is the substantive companion to the polynomial floor: same gain-ball
machinery, but an interior `σ` and a non-degenerate `sbar = 1/2`.
-/

import Sanctions.Theory.Equilibrium.JointMPE
import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.Certificates.TargetSanctionLossOffset
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Theory.Bellman.InvariantLipBall
import Sanctions.Theory.Bellman.InvariantLipGainBall
import Sanctions.Theory.Bellman.InvariantValueClass2
import Sanctions.Theory.Equilibrium.ArgmaxUniquenessFromConcavity
import Sanctions.Theory.Certificates.StandardComplianceLocal

namespace Sanctions

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.AbstractGame.Params

noncomputable section

/-- **The substantive witness parameters.** Concave state-dependent Sender stage
payoff `U_S = ½s − ½s² + ¾x`, linear Target `U_T = 5x − s + a`, affine transition
`F = affineF (1/2)`, discounts `1/2`. The static Sender response is the interior
`σ ≡ 1/2`. -/
def substantiveParams : AbstractGame.Params where
  δ := 1/2
  δ_mem := ⟨by norm_num, by norm_num⟩
  β_T := 1/2
  β_T_mem := ⟨by norm_num, by norm_num⟩
  β_S := 1/2
  β_S_mem := ⟨by norm_num, by norm_num⟩
  U_T := fun x a s => 5 * x - s + a
  -- Concave in `s` with interior argmax `1/2`; the `¾x` term gives `V_S` slope 1.
  U_S := fun x _ s => 1/2 * s - 1/2 * s ^ 2 + 3/4 * x
  -- Interior static Sender argmax of `½s − ½s²` on `[0,1]`.
  σ := fun _ _ => 1/2
  σ_mem := fun _ _ => ⟨by norm_num, by norm_num⟩
  σ_isMaxOn_U_S := fun x _ s _hs => by
    -- `½s − ½s² ≤ 1/8 = ½·½ − ½·(½)²`, since `1/8 − (½s − ½s²) = ½(s − ½)² ≥ 0`.
    show 1/2 * s - 1/2 * s ^ 2 + 3/4 * x ≤ 1/2 * (1/2) - 1/2 * (1/2) ^ 2 + 3/4 * x
    nlinarith [sq_nonneg (s - 1/2)]
  U_T_continuous := by fun_prop
  U_S_continuous := by fun_prop
  F := AbstractGame.affineF (1 / 2)
  F_continuous := AbstractGame.affineF_continuous _
  F_mono_x := AbstractGame.affineF_mono_x ⟨by norm_num, by norm_num⟩
  F_mono_s := AbstractGame.affineF_mono_s ⟨by norm_num, by norm_num⟩
  F_diag := AbstractGame.affineF_diag _

/-- **`substantiveParams` has a continuous static Sender selector.** Affine-restricted: a
concrete member with the affine transition `affineF (1/2)`; the selector itself does not
read the transition. The proof is the one that was the economy's `σ_continuous` field
until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance substantiveParams_staticSelectorContinuous :
    substantiveParams.StaticSelectorContinuous where
  σ_continuous := continuous_const

/-- Sanity: the static Sender argmax is interior at `1/2` (not the corner), so
the myopic comparator does **not** saturate — the source of non-degeneracy. -/
example : substantiveParams.σ 0 0 = 1/2 := rfl

/-- Sanity: `½s − ½s²` is maximised on `[0,1]` at `s = 1/2` with value `1/8`. -/
example : ∀ s ∈ Sanctions.I,
    1/2 * s - 1/2 * s ^ 2 ≤ (1/8 : ℝ) := by
  intro s _hs; nlinarith [sq_nonneg (s - 1/2)]

/-! ## Affine BCF helper + gain-ball carriers -/

/-- The affine BCF `y ↦ c·y` on the compact state space `↥S = [0,1]`. -/
def affineBCF (c : ℝ) : Val :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => c * y.val) (by fun_prop))

@[simp] theorem affineBCF_apply (c : ℝ) (y : ↥(Sanctions.S : Set ℝ)) :
    affineBCF c y = c * y.val := rfl

/-- `affineBCF c ∈ valLipGainBall M c c 0` for `0 ≤ c ≤ M`: sup-norm `≤ M`,
Lipschitz `c`, and minimum upward slope `c` (last two tight at slope `c`). -/
theorem affineBCF_mem_gainBall {c M : ℝ} (hc : 0 ≤ c) (hcM : c ≤ M) :
    affineBCF c ∈ valLipGainBall M c c 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BoundedContinuousFunction.norm_le (le_trans hc hcM)]
    intro y
    rw [affineBCF_apply, Real.norm_eq_abs, abs_le]
    exact ⟨by nlinarith [y.property.1, y.property.2], by nlinarith [y.property.1, y.property.2]⟩
  · intro y₁ y₂
    rw [affineBCF_apply, affineBCF_apply, Subtype.dist_eq, Real.dist_eq,
        show c * y₂.val - c * y₁.val = c * (y₂.val - y₁.val) by ring, abs_mul,
        abs_of_nonneg hc]
    exact le_of_eq (by rw [abs_sub_comm])
  · intro y₁ y₂ _ _ hle
    have hle' : y₁.val ≤ y₂.val := Subtype.coe_le_coe.mpr hle
    rw [affineBCF_apply, affineBCF_apply, Subtype.dist_eq, Real.dist_eq,
        abs_of_nonpos (by linarith : y₁.val - y₂.val ≤ 0)]
    nlinarith [hle']

/-- Sender carrier: affine slope-exactly-`1` functions (`valLipGainBall 2 1 1 0`).
Pinning the slope to `1` is what makes `σ_dyn` the constant `3/4`. -/
def substCarrierS : Set Val := valLipGainBall 2 1 1 0

/-- Target carrier: affine slope-exactly-`20/3` functions
(`valLipGainBall 12 (20/3) (20/3) 0`), unchanged from the polynomial witness. -/
def substCarrierT : Set Val := valLipGainBall 12 (20/3) (20/3) 0

theorem substCarrierS_nonempty : substCarrierS.Nonempty :=
  ⟨affineBCF 1, affineBCF_mem_gainBall (by norm_num) (by norm_num)⟩

theorem substCarrierT_nonempty : substCarrierT.Nonempty :=
  ⟨affineBCF (20/3), affineBCF_mem_gainBall (by norm_num) (by norm_num)⟩

/-! ## Affine extraction: `V_S` has slope exactly 1 on the gain carrier -/

/-- `clipS'` is the identity (in value) on `[0,1]`. -/
theorem clipS'_val_of_mem {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) :
    (Sanctions.clipS' z).val = z := by
  show Sanctions.clipS z = z
  unfold Sanctions.clipS
  rw [min_eq_right hz.2, max_eq_right hz.1]

/-- **Affine extraction.** Every `V_S` in the slope-1 gain carrier satisfies
`V_S(clip z₂) − V_S(clip z₁) = z₂ − z₁` for `z₁, z₂ ∈ [0,1]` — i.e. `V_S` is
affine with slope exactly `1` on `[0,1]`. This is what pins `σ_dyn` to `3/4`. -/
theorem substV_S_clip_diff {V_S : Val} (hV_S : V_S ∈ substCarrierS)
    {z₁ z₂ : ℝ} (h1 : z₁ ∈ Set.Icc (0:ℝ) 1) (h2 : z₂ ∈ Set.Icc (0:ℝ) 1) :
    V_S (Sanctions.clipS' z₂) - V_S (Sanctions.clipS' z₁) = z₂ - z₁ := by
  have hLip : ValueLipschitzWith V_S 1 := hV_S.2.1
  have hGain : LowerSlopeOnValueOn V_S (Set.Icc 0 1) 1 := hV_S.2.2
  have hmem₁ : (Sanctions.clipS' z₁).val ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem _
  have hmem₂ : (Sanctions.clipS' z₂).val ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem _
  -- distances reduce to `|z₁ − z₂|` via the clip identity.
  have hd : dist (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) = |z₁ - z₂| := by
    rw [Subtype.dist_eq, Real.dist_eq, clipS'_val_of_mem h1, clipS'_val_of_mem h2]
  rcases le_total z₁ z₂ with hle | hle
  · have hord : Sanctions.clipS' z₁ ≤ Sanctions.clipS' z₂ := Sanctions.clipS'_mono hle
    have hlow := hGain (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) hmem₁ hmem₂ hord
    have hup := hLip (Sanctions.clipS' z₁) (Sanctions.clipS' z₂)
    rw [hd, one_mul, abs_of_nonpos (by linarith : z₁ - z₂ ≤ 0)] at hlow
    rw [hd, one_mul, abs_of_nonpos (by linarith : z₁ - z₂ ≤ 0)] at hup
    have := abs_le.mp hup
    linarith [this.2]
  · have hord : Sanctions.clipS' z₂ ≤ Sanctions.clipS' z₁ := Sanctions.clipS'_mono hle
    have hlow := hGain (Sanctions.clipS' z₂) (Sanctions.clipS' z₁) hmem₂ hmem₁ hord
    have hup := hLip (Sanctions.clipS' z₂) (Sanctions.clipS' z₁)
    rw [dist_comm, hd, one_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ z₁ - z₂)] at hlow
    rw [dist_comm, hd, one_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ z₁ - z₂)] at hup
    have := abs_le.mp hup
    linarith [this.2]

/-- **`V_S` in closed form on the whole line.** Using the affine extraction plus
clip idempotence, `V_S(clip t) = clip t + V_S(clip 0)` for every `t`. -/
theorem substV_S_eq {V_S : Val} (hV_S : V_S ∈ substCarrierS) (t : ℝ) :
    V_S (Sanctions.clipS' t)
      = Sanctions.clipS t + V_S (Sanctions.clipS' 0) := by
  have hmem : Sanctions.clipS t ∈ Set.Icc (0:ℝ) 1 := Sanctions.clipS_mem t
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hdiff := substV_S_clip_diff hV_S h0 hmem
  have hidem : Sanctions.clipS' (Sanctions.clipS t) = Sanctions.clipS' t := by
    apply Subtype.ext
    exact clipS'_val_of_mem hmem
  rw [hidem] at hdiff
  linarith [hdiff]

/-- **The Sender dynamic objective in explicit closed form.** With
`c₀ := V_S(clip 0)` and `F x s = (x+s)/2`,
`obj(s) = ½s − ½s² + ¾x + ½·clip((x+s)/2) + ½c₀`. The only non-smooth part is
`clip((x+s)/2)`; everything else is the strictly-concave quadratic. -/
theorem subst_obj_eq {V_S : Val} (hV_S : V_S ∈ substCarrierS) (x a s : ℝ) :
    substantiveParams.U_S x a s
        + substantiveParams.β_S * V_S (Sanctions.clipS' (substantiveParams.F x s))
      = 1/2 * s - 1/2 * s ^ 2 + 3/4 * x
        + 1/2 * Sanctions.clipS ((x + s) / 2)
        + 1/2 * V_S (Sanctions.clipS' 0) := by
  have hF : substantiveParams.F x s = (x + s) / 2 := by
    simp only [substantiveParams, AbstractGame.affineF]; ring
  rw [hF, substV_S_eq hV_S]
  simp only [substantiveParams]
  ring

/-! ## Rule-11 disproof: the `∀x` `DynamicArgmaxUnique` FAILS -/

/-- **The Sender objective at the pathological state `x = −5/8`, in closed form.**
For `V_S = affineBCF 1` and `s ∈ [0,1]`,
`obj(s) = ½s − ½s² − 15/32 + ½·max(0, −5/16 + s/2)`. -/
theorem subst_obj_at_neg58 {s : ℝ} (hs : s ∈ Sanctions.I) :
    substantiveParams.U_S (-5/8) 0 s
        + substantiveParams.β_S * (affineBCF 1) (Sanctions.clipS' (substantiveParams.F (-5/8) s))
      = 1/2 * s - 1/2 * s ^ 2 - 15/32 + 1/2 * max 0 (-5/16 + s/2) := by
  have hF : substantiveParams.F (-5/8) s = -5/16 + s/2 := by
    simp only [substantiveParams, AbstractGame.affineF]; ring
  have hclip : Sanctions.clipS (-5/16 + s/2) = max 0 (-5/16 + s/2) := by
    unfold Sanctions.clipS
    rw [min_eq_right (by nlinarith [hs.2] : -5/16 + s/2 ≤ 1)]
  rw [hF, affineBCF_apply, one_mul]
  show 1/2 * s - 1/2 * s ^ 2 + 3/4 * (-5/8)
      + 1/2 * Sanctions.clipS (-5/16 + s/2) = _
  rw [hclip]; ring

/-- **Rule-11 counterexample.** The witness's *state-global*
`DynamicArgmaxUniqueGlobal` (the legacy `∀ x : ℝ` form) is FALSE: at the
unphysical `x = −5/8` the Sender objective has two distinct global maximizers,
`½` and `¾` (both attaining `−11/32`). The lower clip's convex kink makes the two
local maxima coincide in height exactly at `x = −5/8`. Consequence: an
**interior-argmax** substantive witness cannot satisfy the state-global form —
only the **state-local** (`x ∈ [0,1]`) `DynamicArgmaxUnique` can hold. That
weakening (Design A) is now in place, and `substParams_DAU_on_carrier_S` below
discharges the state-local form for the whole Sender carrier, so this witness
DOES instantiate the compliance certificate. -/
theorem substParams_DAU_counterexample :
    ¬ substantiveParams.DynamicArgmaxUniqueGlobal (affineBCF 1) := by
  intro hDAU
  -- pointwise upper bound: obj s ≤ -11/32 on `[0,1]`.
  have hbound : ∀ s ∈ Sanctions.I,
      substantiveParams.U_S (-5/8) 0 s
        + substantiveParams.β_S * (affineBCF 1) (Sanctions.clipS' (substantiveParams.F (-5/8) s))
        ≤ -11/32 := by
    intro s hs
    rw [subst_obj_at_neg58 hs]
    rcases le_total (-5/16 + s/2) 0 with hc | hc
    · rw [max_eq_left hc]; nlinarith [sq_nonneg (s - 1/2)]
    · rw [max_eq_right hc]; nlinarith [sq_nonneg (s - 3/4)]
  -- both `½` and `¾` attain `-11/32`.
  have hhalf : substantiveParams.U_S (-5/8) 0 (1/2)
        + substantiveParams.β_S * (affineBCF 1) (Sanctions.clipS' (substantiveParams.F (-5/8) (1/2)))
      = -11/32 := by
    rw [subst_obj_at_neg58 ⟨by norm_num, by norm_num⟩]
    rw [max_eq_left (by norm_num : (-5/16 + (1/2:ℝ)/2) ≤ 0)]; norm_num
  have h34 : substantiveParams.U_S (-5/8) 0 (3/4)
        + substantiveParams.β_S * (affineBCF 1) (Sanctions.clipS' (substantiveParams.F (-5/8) (3/4)))
      = -11/32 := by
    rw [subst_obj_at_neg58 ⟨by norm_num, by norm_num⟩]
    rw [max_eq_right (by norm_num : (0:ℝ) ≤ -5/16 + (3/4)/2)]; norm_num
  -- `½` and `¾` are both `IsMaxOn`.
  have hmax_half : IsMaxOn (fun s => substantiveParams.U_S (-5/8) 0 s
      + substantiveParams.β_S * (affineBCF 1) (Sanctions.clipS' (substantiveParams.F (-5/8) s)))
      Sanctions.I (1/2) := by
    rw [isMaxOn_iff]; intro s hs
    exact le_trans (hbound s hs) (le_of_eq hhalf.symm)
  have hmax_34 : IsMaxOn (fun s => substantiveParams.U_S (-5/8) 0 s
      + substantiveParams.β_S * (affineBCF 1) (Sanctions.clipS' (substantiveParams.F (-5/8) s)))
      Sanctions.I (3/4) := by
    rw [isMaxOn_iff]; intro s hs
    exact le_trans (hbound s hs) (le_of_eq h34.symm)
  have : (1/2 : ℝ) = 3/4 :=
    hDAU (-5/8) 0 (1/2) (3/4) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      hmax_half hmax_34
  norm_num at this

/-! ## State-local Sender uniqueness — the certificate is now instantiable -/

/-- **State-local `DynamicArgmaxUnique` on the whole Sender carrier (Design A
discharge).** For every `V_S` in the slope-1 gain carrier, the state-local
uniqueness holds: on the physical state space `S = [0,1]` the Sender objective is
the strictly concave quadratic `−½s² + ¾s + const` (the lower clip is inactive
because `F x s = (x+s)/2 ∈ [0,1]` there), whose maximiser on `[0,1]` is the unique
interior point `s = ¾`. This is precisely the `sender_unique_on` field the
compliance certificate consumes — the fact the old `∀ x : ℝ` form could NOT provide
(see `substParams_DAU_counterexample`). Interior argmax `¾ > ½ = σ_myopic` is the
strict-dominance content. -/
theorem substParams_DAU_on_carrier_S {V_S : Val} (hV_S : V_S ∈ substCarrierS) :
    substantiveParams.DynamicArgmaxUnique V_S := by
  apply substantiveParams.dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  obtain ⟨hx0, hx1⟩ := hx
  set c₀ := V_S (Sanctions.clipS' 0) with hc₀
  -- On `I` (with `x ∈ S`), the objective equals the concave quadratic `Q`.
  have hQ : ∀ s ∈ Sanctions.I,
      substantiveParams.U_S x a s
          + substantiveParams.β_S * V_S (Sanctions.clipS' (substantiveParams.F x s))
        = -(1/2) * s ^ 2 + 3/4 * s + (3/4 * x + x / 4 + 1/2 * c₀) := by
    intro s hs
    rw [subst_obj_eq hV_S]
    have hmem : (x + s) / 2 ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
    have hclip : Sanctions.clipS ((x + s) / 2) = (x + s) / 2 :=
      clipS'_val_of_mem hmem
    rw [hclip, hc₀]; ring
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne p q hp hq hpq
  have hq_eq : q = 1 - p := by linarith
  subst hq_eq
  have hmid : p * s₁ + (1 - p) * s₂ ∈ Sanctions.I :=
    ⟨by nlinarith [hs₁.1, hs₂.1, hp.le, hq.le],
     by nlinarith [hs₁.2, hs₂.2, hp.le, hq.le]⟩
  simp only [smul_eq_mul, hQ s₁ hs₁, hQ s₂ hs₂, hQ _ hmid]
  have hsq : (s₁ - s₂) ^ 2 > 0 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  nlinarith [mul_pos (mul_pos hp hq) hsq]

/-! ## Rule-11 plan disconfirmation: this witness cannot complete the
`StandardComplianceLocalCoreCertificate` Sender side

The certificate requires, simultaneously:
* `hV_S_lip_carrier` — every carrier `V_S` is `KS`-Lipschitz (the slope-1
  gain carrier forces `KS ≥ 1`);
* `hS_margin` — `β_S·KS·δ < mS` (hence `mS > 1/4`);
* `h_stage_sender_on` — the stage payoff `s ↦ U_S(x, ·, s)` has minimum
  upward chord slope `mS` on `[0, max x s̄]` at every basin state
  `x ∈ [x_S, 1]`, in particular at `x = 1` where the domain is `[0,1]`.

But `U_S = ½s − ½s² + ¾x` peaks at `s = ½`: on `[9/10, 1]` its chord slope
is `−9/20 < 0 < 1/4 < mS`. Contradiction. (Note `U_S` ignores the
compliance argument `a`, so this covers the field's `α_on`-evaluated form
at every carrier pair.) A substantive certificate witness therefore needs
an `a`-DEPENDENT `U_S` — the Eaton-Engers "compliance placates" cross
term `∂²U_S/∂s∂a < 0` — so that the *myopic* action supports a low
sanction ceiling (`hMyoCeiling`) while the *dynamic* action supports the
high-sanction stage slope (`h_stage_sender_on`). -/

/-- **Rule-11 infeasibility (plan disconfirmation).** No scalars
`(KS, mS, sbar)` can satisfy the certificate's three Sender-side fields at
`substantiveParams` with the slope-1 gain carrier. -/
theorem substParams_certificate_senderSide_infeasible :
    ¬ ∃ (KS mS sbar : ℝ),
        (∀ V_S ∈ substCarrierS, ValueLipschitzWith V_S KS)
        ∧ substantiveParams.β_S * KS * substantiveParams.δ < mS
        ∧ LowerSlopeOn (fun s => substantiveParams.U_S 1 0 s)
            (Set.Icc (0:ℝ) (max 1 sbar)) mS := by
  rintro ⟨KS, mS, sbar, hLip, hMargin, hSlope⟩
  -- Step 1: the slope-1 carrier member `affineBCF 1` forces `KS ≥ 1`.
  have hmem : affineBCF 1 ∈ substCarrierS :=
    affineBCF_mem_gainBall (by norm_num) (by norm_num)
  have hKS : (1:ℝ) ≤ KS := by
    have h := hLip (affineBCF 1) hmem
      ⟨0, by constructor <;> norm_num⟩ ⟨1, by constructor <;> norm_num⟩
    rw [affineBCF_apply, affineBCF_apply, Subtype.dist_eq, Real.dist_eq] at h
    norm_num at h
    linarith [h]
  -- Step 2: the margin forces `mS > 1/4`.
  have hmS_pos : (1:ℝ)/4 < mS := by
    have : substantiveParams.β_S * KS * substantiveParams.δ = KS / 4 := by
      show (1/2 : ℝ) * KS * (1/2) = KS / 4; ring
    rw [this] at hMargin
    linarith
  -- Step 3: the stage chord on `[9/10, 1] ⊆ [0, max 1 sbar]` has slope `−9/20`.
  have h₉ : (9/10 : ℝ) ∈ Set.Icc (0:ℝ) (max 1 sbar) :=
    ⟨by norm_num, le_trans (by norm_num) (le_max_left 1 sbar)⟩
  have h₁ : (1 : ℝ) ∈ Set.Icc (0:ℝ) (max 1 sbar) :=
    ⟨by norm_num, le_max_left 1 sbar⟩
  have hchord := hSlope (9/10) h₉ 1 h₁ (by norm_num)
  have hval : substantiveParams.U_S 1 0 1 - substantiveParams.U_S 1 0 (9/10)
      = -9/200 := by
    show (1/2 * 1 - 1/2 * 1 ^ 2 + 3/4 * 1)
        - (1/2 * (9/10) - 1/2 * (9/10) ^ 2 + 3/4 * 1) = -9/200
    norm_num
  rw [hval] at hchord
  -- `mS · (1/10) ≤ −9/200` vs `mS > 1/4`: contradiction.
  nlinarith [hchord, hmS_pos]

end -- noncomputable section

#print axioms substParams_DAU_counterexample
#print axioms substParams_DAU_on_carrier_S
#print axioms substParams_certificate_senderSide_infeasible

end Examples

end Sanctions
