/-
Sanctions/Theory/Shocked/ShockedInteriorExistence.lean

**Interior (non-corner) shocked feedback-Stackelberg existence via Banach.**

The corner case (`ShockedEquilibrium`, `HeSunShockExistence`) pins the leader at
a constant policy. The *interior* case lets the leader policy vary with the
Sender value, `α = lead(V_S)` (the slaved leader argmax), and runs Banach on the
**slaved shocked operator**

  `Φ(V_S) = bellmanS_shock(lead(V_S), V_S)`.

Its contraction modulus decomposes into two channels:

  ‖Φ(V) − Φ(W)‖ ≤ β_S·‖V−W‖   (continuation — `bellmanS_shock` value contraction)
              + L_{U_S,a}·‖lead V − lead W‖   (policy — `bellmanS_BCF` policy bound)
              ≤ (β_S + L_{U_S,a}·L_α)·‖V−W‖.

So `Φ` is a contraction **iff** `β_S + L_{U_S,a}·L_α < 1`, where `L_α` is the
Lipschitz constant of the leader policy in `V_S`. The continuation channel is
done (`smear` nonexpansive); the policy channel needs the new
`bellmanS_BCF_policy_pointwise_dist` (here) plus two regularity inputs — `U_S`
Lipschitz in the Target action, and **`lead` Lipschitz in `V_S`**. The latter is
the one irreducible analytic input: deterministically the leader argmax is only
Hölder-½ in `V_S`. The ACCEPTED resolution is route (a): consume the leader
objective-difference action-Lipschitz estimate `h_obj_diff` and derive
`lead_lip` from it via `lead_lipschitz_via_core`
(`ShockedLeaderLipschitz.lean`); see
`shockedFeedbackStackelbergTop_interior_discharged`. A mollifier
kernel-regularity upgrade (deriving the Lipschitz constant from a smooth shock
kernel instead) was once envisaged but never shipped, and a quantitative
kernel-width audit (2026-07-04) showed the C²-kernel route is quantitatively
DEAD at the P3 mechanism witness: the admissible-width window is empty (no
kernel width simultaneously preserves smeared concavity and the no-clip
window), and the derived coupling constant exceeds the contraction margin by
orders of magnitude even at zero carrier norms. The named-hypothesis boundary
(`h_obj_diff`) is therefore final at that economy. `lead_lip` is consumed here
exactly as the deterministic `AlphaOnLipschitzOn` primitive isolates it.

**Rule-15.** The interior Sender value is *constructed* by Banach
(`ContractingWith.fixedPoint`); only the leader-policy regularity is consumed.
The result is a genuine `ShockedFeedbackStackelbergEquilibriumTop` with an
interior (state-varying) leader policy.
-/

import Sanctions.Theory.Shocked.ShockedEquilibrium

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Policy-channel bound for the Sender Bellman operator.** If the stage payoff
difference under two leader policies is uniformly bounded by `M` over the sanction
set, then the Sender Bellman values differ by at most `M`. The continuation term
cancels (same value `V`), so only the `U_S` policy difference survives. -/
theorem bellmanS_BCF_policy_pointwise_dist
    (α α' : ℝ → ℝ) (hα : Continuous α) (hα' : Continuous α')
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)) (M : ℝ)
    (hM : ∀ s ∈ Sanctions.I, |p.U_S x.val (α x.val) s - p.U_S x.val (α' x.val) s| ≤ M) :
    |p.bellmanS_BCF α hα V x - p.bellmanS_BCF α' hα' V x| ≤ M := by
  have heq_V : p.bellmanS_BCF α hα V x =
      sSup ((fun s => p.integrandS α (fun y => V y) (x.val, s)) '' Sanctions.I) := rfl
  have heq_W : p.bellmanS_BCF α' hα' V x =
      sSup ((fun s => p.integrandS α' (fun y => V y) (x.val, s)) '' Sanctions.I) := rfl
  rw [heq_V, heq_W]
  apply Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd
    (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩ (M := M)
    (Bf := sSup ((fun s => p.integrandS α (fun y => V y) (x.val, s)) '' Sanctions.I))
    (Bg := sSup ((fun s => p.integrandS α' (fun y => V y) (x.val, s)) '' Sanctions.I))
  · intro s hs
    have hcancel : p.integrandS α (fun y => V y) (x.val, s)
                   - p.integrandS α' (fun y => V y) (x.val, s)
                 = p.U_S x.val (α x.val) s - p.U_S x.val (α' x.val) s := by
      unfold integrandS; ring
    rw [hcancel]; exact hM s hs
  · intro s hs
    exact le_csSup (p.integrandS_image_bddAbove hα V.continuous x.val) ⟨s, hs, rfl⟩
  · intro s hs
    exact le_csSup (p.integrandS_image_bddAbove hα' V.continuous x.val) ⟨s, hs, rfl⟩

end Params

namespace ShockedParams

variable (sp : Sanctions.AbstractGame.ShockedParams)

/-- **Fixed point of the slaved shocked Sender operator.**
This is the Banach core of interior shocked existence, separated from the Target
value construction. It proves that `V ↦ bellmanS_shock (lead V) V` has a fixed
point whenever the continuation and policy channels satisfy the existing
contraction margin. -/
theorem exists_fixedPoint_slaved_shocked
    (lead : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (ℝ → ℝ))
    (lead_cont : ∀ V, Continuous (lead V))
    (lead_mem : ∀ V, ∀ x ∈ Sanctions.S, lead V x ∈ Sanctions.I)
    (L_α L_Ua : ℝ) (hLα : 0 ≤ L_α) (hLUa : 0 ≤ L_Ua)
    (lead_lip : ∀ V W, ∀ x : ↥(Sanctions.S : Set ℝ),
      |lead V x.val - lead W x.val| ≤ L_α * dist V W)
    (hU_lip : ∀ (x : ↥(Sanctions.S : Set ℝ)) (a a' : ℝ),
      a ∈ Sanctions.I → a' ∈ Sanctions.I → ∀ s ∈ Sanctions.I,
      |sp.toParams.U_S x.val a s - sp.toParams.U_S x.val a' s| ≤
        L_Ua * |a - a'|)
    (hmargin : sp.toParams.β_S + L_Ua * L_α < 1) :
    ∃ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      sp.bellmanS_shock (lead V) (lead_cont V) V = V := by
  set Φ : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :=
    fun V => sp.bellmanS_shock (lead V) (lead_cont V) V with hΦdef
  have hK0 : (0 : ℝ) ≤ sp.toParams.β_S + L_Ua * L_α :=
    add_nonneg sp.toParams.β_S_mem.1 (mul_nonneg hLUa hLα)
  set K : ℝ≥0 := ⟨sp.toParams.β_S + L_Ua * L_α, hK0⟩ with hKdef
  have hKlt : K < 1 := by rw [← NNReal.coe_lt_coe]; exact hmargin
  have hlip : LipschitzWith K Φ := by
    apply Sanctions.lipschitzWith_of_pointwise_dist_le
    intro V W x
    have h1 : dist (sp.bellmanS_shock (lead V) (lead_cont V) V x)
                   (sp.bellmanS_shock (lead V) (lead_cont V) W x) ≤
                sp.toParams.β_S * dist V W :=
      sp.bellmanS_shock_pointwise_dist (lead_cont V) V W x
    have h2 : dist (sp.bellmanS_shock (lead V) (lead_cont V) W x)
                   (sp.bellmanS_shock (lead W) (lead_cont W) W x) ≤
                L_Ua * L_α * dist V W := by
      have hpol :
          |sp.toParams.bellmanS_BCF (lead V) (lead_cont V) (sp.smear W) x -
            sp.toParams.bellmanS_BCF (lead W) (lead_cont W) (sp.smear W) x| ≤
              L_Ua * |lead V x.val - lead W x.val| :=
        sp.toParams.bellmanS_BCF_policy_pointwise_dist (lead V) (lead W)
          (lead_cont V) (lead_cont W) (sp.smear W) x
          (M := L_Ua * |lead V x.val - lead W x.val|)
          (fun s hs => hU_lip x (lead V x.val) (lead W x.val)
            (lead_mem V x.val x.property) (lead_mem W x.val x.property) s hs)
      have hstep : L_Ua * |lead V x.val - lead W x.val| ≤
          L_Ua * L_α * dist V W := by
        calc
          L_Ua * |lead V x.val - lead W x.val| ≤
              L_Ua * (L_α * dist V W) :=
            mul_le_mul_of_nonneg_left (lead_lip V W x) hLUa
          _ = L_Ua * L_α * dist V W := by ring
      rw [Real.dist_eq]
      exact le_trans hpol hstep
    rw [Real.dist_eq] at h1 ⊢
    have htri :
        |sp.bellmanS_shock (lead V) (lead_cont V) V x -
            sp.bellmanS_shock (lead W) (lead_cont W) W x| ≤
          |sp.bellmanS_shock (lead V) (lead_cont V) V x -
            sp.bellmanS_shock (lead V) (lead_cont V) W x| +
          |sp.bellmanS_shock (lead V) (lead_cont V) W x -
            sp.bellmanS_shock (lead W) (lead_cont W) W x| :=
      abs_sub_le _ _ _
    rw [Real.dist_eq] at h2
    calc
      |Φ V x - Φ W x| ≤
          |sp.bellmanS_shock (lead V) (lead_cont V) V x -
            sp.bellmanS_shock (lead V) (lead_cont V) W x| +
          |sp.bellmanS_shock (lead V) (lead_cont V) W x -
            sp.bellmanS_shock (lead W) (lead_cont W) W x| := htri
      _ ≤ sp.toParams.β_S * dist V W + L_Ua * L_α * dist V W :=
        add_le_add h1 h2
      _ = (K : ℝ) * dist V W := by rw [hKdef]; push_cast; ring
  have hcontr : ContractingWith K Φ := ⟨hKlt, hlip⟩
  set Vfp := ContractingWith.fixedPoint Φ hcontr with hVfpdef
  have hfp : Φ Vfp = Vfp := ContractingWith.fixedPoint_isFixedPt hcontr
  exact ⟨Vfp, hfp⟩

/-- **Interior shocked feedback-Stackelberg existence.** With a leader response
`lead : V_S ↦ α` that is continuous, feasible, and **Lipschitz in `V_S`**
(`lead_lip`, constant `L_α` — the mollifier-shock regularity), a stage payoff
`U_S` Lipschitz in the Target action (`hU_lip`, constant `L_Ua`), and the
contraction margin `β_S + L_Ua·L_α < 1`, the slaved shocked operator
`Φ(V) = bellmanS_shock(lead V, V)` is a Banach contraction; its fixed point is
the interior Sender value, and the shocked-game equilibrium exists with the
**interior** (state-varying) leader policy `lead(V_S)`. -/
theorem shockedFeedbackStackelbergTop_interior
    (lead : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (ℝ → ℝ))
    (lead_cont : ∀ V, Continuous (lead V))
    (lead_mem : ∀ V, ∀ x ∈ Sanctions.S, lead V x ∈ Sanctions.I)
    (L_α L_Ua : ℝ) (hLα : 0 ≤ L_α) (hLUa : 0 ≤ L_Ua)
    (lead_lip : ∀ V W, ∀ x : ↥(Sanctions.S : Set ℝ),
      |lead V x.val - lead W x.val| ≤ L_α * dist V W)
    (hU_lip : ∀ (x : ↥(Sanctions.S : Set ℝ)) (a a' : ℝ),
      a ∈ Sanctions.I → a' ∈ Sanctions.I → ∀ s ∈ Sanctions.I,
      |sp.toParams.U_S x.val a s - sp.toParams.U_S x.val a' s| ≤ L_Ua * |a - a'|)
    (hmargin : sp.toParams.β_S + L_Ua * L_α < 1)
    (hσc : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      Continuous (fun xa : ℝ × ℝ => sp.toParams.σ_dyn_top (sp.smear V) xa.1 xa.2))
    (lead_opt : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      sp.bellmanS_shock (lead V) (lead_cont V) V = V →
      ∀ x ∈ Sanctions.S, IsMaxOn (fun a => sp.toParams.joint_T_top_integrand
        (sp.smear (sp.V_T_dyn_shock V (hσc V))) (sp.smear V) x a) Sanctions.I (lead V x)) :
    Nonempty sp.ShockedFeedbackStackelbergEquilibriumTop := by
  -- The slaved shocked operator.
  set Φ : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :=
    fun V => sp.bellmanS_shock (lead V) (lead_cont V) V with hΦdef
  -- Modulus.
  have hK0 : (0 : ℝ) ≤ sp.toParams.β_S + L_Ua * L_α :=
    add_nonneg sp.toParams.β_S_mem.1 (mul_nonneg hLUa hLα)
  set K : ℝ≥0 := ⟨sp.toParams.β_S + L_Ua * L_α, hK0⟩ with hKdef
  have hKlt : K < 1 := by rw [← NNReal.coe_lt_coe]; exact hmargin
  -- Contraction: pointwise modulus bound.
  have hlip : LipschitzWith K Φ := by
    apply Sanctions.lipschitzWith_of_pointwise_dist_le
    intro V W x
    -- continuation channel (same policy `lead V`, value V vs W)
    have h1 : dist (sp.bellmanS_shock (lead V) (lead_cont V) V x)
                   (sp.bellmanS_shock (lead V) (lead_cont V) W x)
                ≤ sp.toParams.β_S * dist V W :=
      sp.bellmanS_shock_pointwise_dist (lead_cont V) V W x
    -- policy channel (same value W, policy `lead V` vs `lead W`)
    have h2 : dist (sp.bellmanS_shock (lead V) (lead_cont V) W x)
                   (sp.bellmanS_shock (lead W) (lead_cont W) W x)
                ≤ L_Ua * L_α * dist V W := by
      have hpol : |sp.toParams.bellmanS_BCF (lead V) (lead_cont V) (sp.smear W) x
                   - sp.toParams.bellmanS_BCF (lead W) (lead_cont W) (sp.smear W) x|
                  ≤ L_Ua * |lead V x.val - lead W x.val| :=
        sp.toParams.bellmanS_BCF_policy_pointwise_dist (lead V) (lead W)
          (lead_cont V) (lead_cont W) (sp.smear W) x
          (M := L_Ua * |lead V x.val - lead W x.val|)
          (fun s hs => hU_lip x (lead V x.val) (lead W x.val)
            (lead_mem V x.val x.property) (lead_mem W x.val x.property) s hs)
      have hstep : L_Ua * |lead V x.val - lead W x.val| ≤ L_Ua * L_α * dist V W := by
        calc L_Ua * |lead V x.val - lead W x.val|
            ≤ L_Ua * (L_α * dist V W) :=
              mul_le_mul_of_nonneg_left (lead_lip V W x) hLUa
          _ = L_Ua * L_α * dist V W := by ring
      rw [Real.dist_eq]
      -- bellmanS_shock _ _ W = bellmanS_BCF _ _ (smear W) definitionally
      exact le_trans hpol hstep
    -- combine
    rw [Real.dist_eq] at h1 ⊢
    have htri : |sp.bellmanS_shock (lead V) (lead_cont V) V x
                 - sp.bellmanS_shock (lead W) (lead_cont W) W x|
              ≤ |sp.bellmanS_shock (lead V) (lead_cont V) V x
                 - sp.bellmanS_shock (lead V) (lead_cont V) W x|
              + |sp.bellmanS_shock (lead V) (lead_cont V) W x
                 - sp.bellmanS_shock (lead W) (lead_cont W) W x| :=
      abs_sub_le _ _ _
    rw [Real.dist_eq] at h2
    calc |Φ V x - Φ W x|
        ≤ |sp.bellmanS_shock (lead V) (lead_cont V) V x
           - sp.bellmanS_shock (lead V) (lead_cont V) W x|
        + |sp.bellmanS_shock (lead V) (lead_cont V) W x
           - sp.bellmanS_shock (lead W) (lead_cont W) W x| := htri
      _ ≤ sp.toParams.β_S * dist V W + L_Ua * L_α * dist V W := add_le_add h1 h2
      _ = (K : ℝ) * dist V W := by rw [hKdef]; push_cast; ring
  -- Banach fixed point.
  have hcontr : ContractingWith K Φ := ⟨hKlt, hlip⟩
  set Vfp := ContractingWith.fixedPoint Φ hcontr with hVfpdef
  have hfp : Φ Vfp = Vfp := ContractingWith.fixedPoint_isFixedPt hcontr
  -- Package the interior shocked equilibrium with leader policy `lead Vfp`.
  refine ⟨{
    V_T := sp.V_T_dyn_shock Vfp (hσc Vfp)
    V_S := Vfp
    α := lead Vfp
    hα := lead_cont Vfp
    α_mem := lead_mem Vfp
    V_S_fix_shock := hfp.symm
    V_T_fix_shock := fun x => sp.V_T_dyn_shock_bellman_eq Vfp (hσc Vfp) x
    α_opt_shock := lead_opt Vfp hfp }⟩

/-- **Interior shocked existence from physical-state Sender continuity.**
This is the state-local companion of `shockedFeedbackStackelbergTop_interior`.
The Banach construction of the slaved Sender value is unchanged. The Target
value uses the continuous clipped extension of the equilibrium-derived Sender
argmax, which agrees with that argmax on every physical state; consequently the
packaged equilibrium satisfies the original shocked Bellman equations. -/
theorem shockedFeedbackStackelbergTop_interior_local
    (lead : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) → (ℝ → ℝ))
    (lead_cont : ∀ V, Continuous (lead V))
    (lead_mem : ∀ V, ∀ x ∈ Sanctions.S, lead V x ∈ Sanctions.I)
    (L_α L_Ua : ℝ) (hLα : 0 ≤ L_α) (hLUa : 0 ≤ L_Ua)
    (lead_lip : ∀ V W, ∀ x : ↥(Sanctions.S : Set ℝ),
      |lead V x.val - lead W x.val| ≤ L_α * dist V W)
    (hU_lip : ∀ (x : ↥(Sanctions.S : Set ℝ)) (a a' : ℝ),
      a ∈ Sanctions.I → a' ∈ Sanctions.I → ∀ s ∈ Sanctions.I,
      |sp.toParams.U_S x.val a s - sp.toParams.U_S x.val a' s| ≤
        L_Ua * |a - a'|)
    (hmargin : sp.toParams.β_S + L_Ua * L_α < 1)
    (hσc : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
        sp.toParams.σ_dyn_top (sp.smear V) xa.1.val xa.2))
    (lead_opt : ∀ V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ,
      sp.bellmanS_shock (lead V) (lead_cont V) V = V →
      ∀ x ∈ Sanctions.S, IsMaxOn (fun a => sp.toParams.joint_T_top_integrand
        (sp.smear (sp.V_T_dyn_shock_local V (hσc V)))
        (sp.smear V) x a) Sanctions.I (lead V x)) :
    Nonempty sp.ShockedFeedbackStackelbergEquilibriumTop := by
  obtain ⟨Vfp, hfp⟩ := sp.exists_fixedPoint_slaved_shocked
    lead lead_cont lead_mem L_α L_Ua hLα hLUa lead_lip hU_lip hmargin
  refine ⟨{
    V_T := sp.V_T_dyn_shock_local Vfp (hσc Vfp)
    V_S := Vfp
    α := lead Vfp
    hα := lead_cont Vfp
    α_mem := lead_mem Vfp
    V_S_fix_shock := hfp.symm
    V_T_fix_shock := fun x => sp.V_T_dyn_shock_local_bellman_eq Vfp (hσc Vfp) x
    α_opt_shock := lead_opt Vfp hfp }⟩

end ShockedParams
end AbstractGame

end -- noncomputable section

end Sanctions
