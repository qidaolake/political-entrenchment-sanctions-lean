/-
Sanctions/Examples/LossOffsetConverseCounterexample.lean

**The loss-offset margin is sufficient, not necessary: an economy at which the
margin fails and the forward-looking Target still uniquely defies** (doc 68, L3;
the reader's finding B).

The placable family's loss-offset margin `LossOffset`, `c ≤ β_T d_lo g_T` (a hypothesis of its defiance results since round AP), makes the forward-looking
Target defy. The manuscript once said that when it fails the Target complies.
That is an unproved converse, and it is false in the family's own functional
forms: take the boundary member's coefficients (`q = 2, u₀ = w = c = 1,
k = 4/3, r = n = 0, ℓ = 1/10`, affine transition at rate `1/2`, both discounts
`1/2`) with the Target's state valuation lowered to `v = 11/4`. Then
`c = 1 > 11/12 = β_T d_lo g_T`, so the economy is **not** a family member (the
floor-refined form of round J coincides with this one at `n = 0`,
`lossOffset_fails_floor`), and yet

    V_S(x) = 8/9 + 4x/3,   V_T(x) = −1/9 + 11x/3,   ρ(x,a) = (2/3)(1 − a),   α ≡ 0

is a top-selector feedback Stackelberg equilibrium in which defiance is the
Target's unique optimum: the Target's objective gap between `0` and `a` is
`(2/45)a`. Nothing is posited — the response is the unique maximiser of the
quadratic Sender objective (gap `(s − ρ)²`), both Bellman equations are
verified, and uniqueness of the argmax is proved.

The economy is built as a `Params` directly (the family structure cannot hold
it, since one of its fields is false there); its payoffs are the family's
closed forms, so nothing about the payoff shape changed. Rule 9: an existence
certificate refuting one converse. Rule 22: affine-restricted and marked so.
-/
import Sanctions.Examples.PlacableSenderBoundaryMember

namespace Sanctions
namespace Examples

open Set AbstractGame

noncomputable section

/-- The economy: the boundary member's `Params` with `v` lowered to `11/4`. -/
def lossOffsetParams : Params :=
  { placableBoundaryBase.toParams with
    U_T := symU_T (1 / 10) 1 0 (11 / 4)
    U_T_continuous := symU_T_continuous _ _ _ _ }

theorem lo_U_S : lossOffsetParams.U_S = symU_S 2 1 (4 / 3) 0 1 := rfl
theorem lo_U_T : lossOffsetParams.U_T = symU_T (1 / 10) 1 0 (11 / 4) := rfl
theorem lo_F : lossOffsetParams.F = affineF (1 / 2) := rfl
theorem lo_β_S : lossOffsetParams.β_S = 1 / 2 := rfl
theorem lo_β_T : lossOffsetParams.β_T = 1 / 2 := rfl

/-- **The loss-offset margin fails**: `c = 1 > β_T d_lo g_T = 11/12`. -/
theorem lossOffset_fails : (1 : ℝ) > 1 / 2 * (1 / 2) * plGT (1 / 2) (1 / 2) (11 / 4) := by
  unfold plGT; norm_num

/-- The floor-refined form (round J) coincides with the previous one at `n = 0`,
so the economy is still outside the family's current class. -/
theorem lossOffset_fails_floor :
    (1 : ℝ) > 1 / 2 * (1 / 2) * plGTn (1 / 2) (1 / 2) (11 / 4) 0 1 2 := by
  unfold plGTn; norm_num

/-- The Sender's value `8/9 + 4x/3`. -/
def loVS : ChordEconomy.Val := ChordEconomy.affBCF (4 / 3) (8 / 9)
/-- The Target's value `−1/9 + 11x/3`. -/
def loVT : ChordEconomy.Val := ChordEconomy.affBCF (11 / 3) (-(1 / 9))
/-- The response `(2/3)(1 − a)`. -/
def loρ (a : ℝ) : ℝ := 2 / 3 * (1 - a)

theorem loρ_mem {a : ℝ} (ha : a ∈ Sanctions.I) : loρ a ∈ Sanctions.I := by
  unfold loρ; constructor <;> nlinarith [ha.1, ha.2]

theorem lo_F_mem {x s : ℝ} (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    lossOffsetParams.F x s ∈ (Sanctions.S : Set ℝ) := by
  rw [lo_F]; unfold affineF; constructor <;> nlinarith [hx.1, hx.2, hs.1, hs.2]

/-- The Sender's objective on the square. -/
theorem lo_senderObj {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ} (hs : s ∈ Sanctions.I) :
    lossOffsetParams.U_S x a s + lossOffsetParams.β_S * loVS (Sanctions.clipS' (lossOffsetParams.F x s))
      = -(s ^ 2) + s * (4 / 3 - 4 / 3 * a) + 4 / 3 * x + 4 / 9 := by
  unfold loVS
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (lo_F_mem hx hs), lo_U_S, lo_β_S,
    lo_F]
  unfold symU_S affineF; ring

/-- **The top response is `(2/3)(1 − a)`**: the objective is a quadratic with
that vertex, so its unique maximiser on `[0,1]` is the vertex. -/
theorem lo_σ_dyn_top {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    lossOffsetParams.σ_dyn_top loVS x a = loρ a := by
  set t := lossOffsetParams.σ_dyn_top loVS x a with ht
  have htmem : t ∈ Sanctions.I := lossOffsetParams.σ_dyn_top_mem_I loVS x a
  have hmax := lossOffsetParams.σ_dyn_top_isMaxOn loVS x a (loρ_mem ha)
  simp only [Set.mem_setOf_eq] at hmax
  rw [← ht, lo_senderObj hx a (loρ_mem ha), lo_senderObj hx a htmem] at hmax
  unfold loρ at hmax ⊢
  have : t - 2 / 3 * (1 - a) = 0 := by nlinarith [sq_nonneg (t - 2 / 3 * (1 - a))]
  linarith

/-- The Target's joint objective at the constructed values, on the square. -/
theorem lo_joint {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    lossOffsetParams.joint_T_top_integrand loVT loVS x a
      = -(1 / 9) + 11 / 3 * x - 2 / 45 * a := by
  simp only [Params.joint_T_top_integrand]
  rw [lo_σ_dyn_top hx ha]
  unfold loVT
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (lo_F_mem hx (loρ_mem ha)),
    lo_U_T, lo_β_T, lo_F]
  unfold symU_T affineF loρ; ring

theorem lo_zero_isMaxOn {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => lossOffsetParams.joint_T_top_integrand loVT loVS x a) Sanctions.I 0 := by
  intro a ha
  show lossOffsetParams.joint_T_top_integrand loVT loVS x a
    ≤ lossOffsetParams.joint_T_top_integrand loVT loVS x 0
  rw [lo_joint hx ha, lo_joint hx ⟨le_rfl, zero_le_one⟩]
  linarith [ha.1]

/-- **The equilibrium.** Rule 15: constructed; Rule 1: `α ≡ 0` is proved to be
the unique argmax (`lo_argmax_unique`), not assumed. -/
def lossOffsetEquilibrium : lossOffsetParams.FeedbackStackelbergEquilibriumTop where
  V_T := loVT
  V_S := loVS
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_rfl, zero_le_one⟩
  V_S_fix := by
    ext y
    change loVS y = sSup ((fun s => lossOffsetParams.integrandS (fun _ => 0) (fun z => loVS z)
      (y.val, s)) '' Sanctions.I)
    have hval : ∀ s ∈ Sanctions.I,
        lossOffsetParams.integrandS (fun _ => 0) (fun z => loVS z) (y.val, s)
          = -(s ^ 2) + s * (4 / 3) + 4 / 3 * y.val + 4 / 9 := by
      intro s hs
      have := lo_senderObj y.property 0 hs
      simp only [Params.integrandS]
      rw [this]; ring
    have hgt : IsGreatest ((fun s => lossOffsetParams.integrandS (fun _ => 0) (fun z => loVS z)
        (y.val, s)) '' Sanctions.I) (loVS y) := by
      refine ⟨⟨2 / 3, ⟨by norm_num, by norm_num⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [hval (2 / 3) ⟨by norm_num, by norm_num⟩]
        unfold loVS; rw [ChordEconomy.affBCF_apply]; ring
      · rintro _ ⟨s, hs, rfl⟩
        dsimp only
        rw [hval s hs]
        unfold loVS; rw [ChordEconomy.affBCF_apply]
        nlinarith [sq_nonneg (s - 2 / 3)]
    exact hgt.csSup_eq.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest ((fun a => lossOffsetParams.joint_T_top_integrand loVT loVS y.val a)
        '' Sanctions.I) (loVT y) := by
      refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [lo_joint y.property ⟨le_rfl, zero_le_one⟩]
        unfold loVT; rw [ChordEconomy.affBCF_apply]; ring
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        rw [lo_joint y.property ha]
        unfold loVT; rw [ChordEconomy.affBCF_apply]
        linarith [ha.1]
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => lo_zero_isMaxOn hx

/-- **Defiance is the unique optimum** at every feasible state. -/
theorem lo_argmax_unique {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => lossOffsetParams.joint_T_top_integrand
      lossOffsetEquilibrium.V_T lossOffsetEquilibrium.V_S x b) Sanctions.I a) :
    a = 0 := by
  have h := hmax ⟨le_rfl, zero_le_one⟩
  simp only [Set.mem_setOf_eq] at h
  change lossOffsetParams.joint_T_top_integrand loVT loVS x 0
    ≤ lossOffsetParams.joint_T_top_integrand loVT loVS x a at h
  rw [lo_joint hx ha, lo_joint hx ⟨le_rfl, zero_le_one⟩] at h
  linarith [ha.1]

/-- **Rule 9 form.** There is an economy with the family's payoff shapes at
which the loss-offset margin fails, the other family margins hold (they are the
boundary member's, which do not involve `v`), and a constructed forward-looking
equilibrium has defiance as the Target's unique optimum. The margin is
sufficient, not necessary. -/
theorem loss_offset_converse_counterexample :
    ∃ (p : Params) (E : p.FeedbackStackelbergEquilibriumTop),
      p.U_S = symU_S 2 1 (4 / 3) 0 1 ∧ p.U_T = symU_T (1 / 10) 1 0 (11 / 4) ∧
      p.F = affineF (1 / 2) ∧ p.β_T = 1 / 2 ∧ p.β_S = 1 / 2 ∧
      (1 : ℝ) > p.β_T * (1 / 2) * plGT p.β_T (1 / 2) (11 / 4) ∧
      (∀ x ∈ Sanctions.I, E.α x = 0) ∧
      (∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => p.joint_T_top_integrand E.V_T E.V_S x b) Sanctions.I a → a = 0) :=
  ⟨lossOffsetParams, lossOffsetEquilibrium, rfl, rfl, rfl, rfl, rfl,
    by rw [lo_β_T]; exact lossOffset_fails,
    fun _ _ => rfl, fun _ hx _ ha hmax => lo_argmax_unique hx ha hmax⟩

end

#print axioms Sanctions.Examples.lossOffsetEquilibrium
#print axioms Sanctions.Examples.loss_offset_converse_counterexample

end Examples
end Sanctions
