/-
Sanctions/Examples/MechanismWitnessShockedDominance.lean

Full-width P3 dominance monotonicity.  The box average at half-width `1`
is affine on the physical state interval.  Reparameterizing the Target action
as `b = a - (27/10)x` cancels state from the Sender's sanction incentive.
The transformed Target objective then has strict decreasing differences,
forcing the canonical leader's adjusted action to be antitone.  This yields
increasing differences, interval dominance, and a monotone greatest Sender
response without a strong-rally assumption.
-/

import Sanctions.Examples.MechanismWitnessShocked

namespace Sanctions.Examples

open Set Filter
open AbstractGame
open scoped NNReal Topology
open BoundedContinuousFunction

/-- At shock half-width one, the Sender's dynamic objective is a quadratic
whose unconstrained vertex is the static P3 vertex plus the endpoint-spread
correction `(V(1) - V(0)) / 24`. -/
noncomputable def mwSenderVertexOne (V : SBCF) (x a : ℝ) : ℝ :=
  (9 / 8) * x - 1 / 12 - (5 / 12) * a
    + (1 / 24) * (V (Sanctions.clipS' 1) - V (Sanctions.clipS' 0))

/-- **Exact full-width Sender selector.**  On the physical state interval,
the greatest dynamic Sender response is the P3 clipped quadratic vertex.
Thus the remaining floor question is quantitative, not an argmax-selection
question: it is exactly a lower bound on `mwSenderVertexOne`. -/
theorem mwSigmaDynTop_eq_clip_vertex_one
    (V : SBCF) {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V) x a =
      max 0 (min 1 (mwSenderVertexOne V x a)) := by
  let t := mwSenderVertexOne V x a
  let C := a + (2 / 5) * x
    + (1 / 2) * Sanctions.movAvgBCF one_pos V
        (Sanctions.clipS' (mechanismWitnessParams.F x 0))
    + (3 / 5) * t ^ 2
  let q : ℝ → ℝ := fun s => C - (3 / 5) * (s - t) ^ 2
  have hqmax : IsMaxOn q Sanctions.I (max 0 (min 1 t)) :=
    WitnessKit.clipVertex_isMaxOn (k := 3 / 5) (C := C) (t := t)
      (by norm_num) (fun s => rfl)
  have hagree : ∀ s ∈ Sanctions.I,
      mechanismWitnessParams.senderDynObjective (mwSenderValueOne V) x a s = q s := by
    intro s hs
    have hx0 : (0 : ℝ) ∈ Sanctions.I := by norm_num
    have hF0 : mechanismWitnessParams.F x 0 ∈ Sanctions.S :=
      mechanismWitnessParams.F_mem x 0 hx hx0
    have hFs : mechanismWitnessParams.F x s ∈ Sanctions.S :=
      mechanismWitnessParams.F_mem x s hx hs
    have hslope := Sanctions.movAvgBCF_one_sub_eq V
      (Sanctions.clipS' (mechanismWitnessParams.F x 0))
      (Sanctions.clipS' (mechanismWitnessParams.F x s))
    rw [Sanctions.clipS'_val_eq_of_mem hF0,
      Sanctions.clipS'_val_eq_of_mem hFs] at hslope
    change mwU_S x a s
        + (1 / 2) * Sanctions.movAvgBCF one_pos V
          (Sanctions.clipS' (mechanismWitnessParams.F x s)) = q s
    simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hslope
    unfold q C t mwSenderVertexOne mwU_S
    simp only [mechanismWitnessParams_F, AbstractGame.affineF]
    nlinarith [hslope]
  have hclip_mem : max 0 (min 1 t) ∈ Sanctions.I :=
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hclip_max : IsMaxOn
      (fun s => mechanismWitnessParams.senderDynObjective
        (mwSenderValueOne V) x a s)
      Sanctions.I (max 0 (min 1 t)) := by
    intro s hs
    change mechanismWitnessParams.senderDynObjective
        (mwSenderValueOne V) x a s ≤
      mechanismWitnessParams.senderDynObjective
        (mwSenderValueOne V) x a (max 0 (min 1 t))
    rw [hagree s hs, hagree _ hclip_mem]
    exact hqmax hs
  have htop := mechanismWitnessParams.σ_dyn_top_isMaxOn
    (mwSenderValueOne V) x a
  have htop_mem := mechanismWitnessParams.σ_dyn_top_mem_I
    (mwSenderValueOne V) x a
  exact mechanismWitnessParams_dynamicArgmaxUnique_one V x hx a
    (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V) x a)
    (max 0 (min 1 t)) htop_mem hclip_mem
    (by simpa [AbstractGame.Params.senderDynObjective] using htop)
    (by simpa [AbstractGame.Params.senderDynObjective] using hclip_max)

/-- Any feasible sanction below the exact full-width vertex is below the
greatest dynamic response. -/
theorem le_mwSigmaDynTop_one_of_le_vertex
    (V : SBCF) {x y a : ℝ} (hx : x ∈ Sanctions.S)
    (hy : y ∈ Sanctions.I) (hyt : y ≤ mwSenderVertexOne V x a) :
    y ≤ mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V) x a := by
  rw [mwSigmaDynTop_eq_clip_vertex_one V hx a]
  exact le_trans (le_min hy.2 hyt) (le_max_right 0 _)

/-- At full width, the Sender response is monotone in the state when the
leader action is held fixed. -/
theorem mwSigmaDynTop_one_monotone_state_fixed_action
    (V : SBCF) {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ Sanctions.S)
    (hx₂ : x₂ ∈ Sanctions.S) (hxx : x₁ ≤ x₂) (a : ℝ) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V) x₁ a ≤
      mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V) x₂ a := by
  rw [mwSigmaDynTop_eq_clip_vertex_one V hx₁ a,
    mwSigmaDynTop_eq_clip_vertex_one V hx₂ a]
  apply max_le_max_left
  apply min_le_min_left
  unfold mwSenderVertexOne
  linarith

/-- At the top state, the full-width dynamic response is one exactly when the
Sender endpoint spread clears the compliance-adjusted threshold. -/
theorem mwSigmaDynTop_one_top_eq_one_iff (V : SBCF) (a : ℝ) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V) 1 a = 1 ↔
      10 * a - 1 ≤ V (Sanctions.clipS' 1) - V (Sanctions.clipS' 0) := by
  rw [mwSigmaDynTop_eq_clip_vertex_one V (by norm_num) _]
  constructor
  · intro h
    have hle : (1 : ℝ) ≤
        mwSenderVertexOne V 1 a := by
      have hmin : (1 : ℝ) ≤
          min 1 (mwSenderVertexOne V 1 a) := by
        by_contra hnot
        have hlt : min 1 (mwSenderVertexOne V 1 a) < 1 :=
          lt_of_not_ge hnot
        have hmax : max 0 (min 1 (mwSenderVertexOne V 1 a)) < 1 := by
          rw [max_lt_iff]
          exact ⟨by norm_num, hlt⟩
        linarith
      exact le_trans hmin (min_le_right _ _)
    unfold mwSenderVertexOne at hle
    linarith
  · intro h
    have hv : (1 : ℝ) ≤
        mwSenderVertexOne V 1 a := by
      unfold mwSenderVertexOne
      linarith
    have hmin : min 1 (mwSenderVertexOne V 1 a) = 1 := min_eq_left hv
    rw [hmin]
    norm_num

/-- Canonical-leader specialization of the exact top-state test. -/
theorem mwDynamicTopRealizedRule_canonical_one_top_eq_one_iff (V : SBCF) :
    mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne V) (mwCanonicalLeaderOne V) 1 = 1 ↔
      10 * mwCanonicalLeaderOne V 1 - 1 ≤
        V (Sanctions.clipS' 1) - V (Sanctions.clipS' 0) :=
  mwSigmaDynTop_one_top_eq_one_iff V (mwCanonicalLeaderOne V 1)

/-- The exact quantitative discharger for the canonical full-width floor.
It introduces no new headline assumption: it records precisely the residual
inequality that would have to be proved from the equilibrium fixed point. -/
theorem mwDynamicTopRealizedRule_canonical_one_floor_of_vertex
    (V : SBCF) {xbar sbar : ℝ} (hxbar0 : 0 ≤ xbar)
    (hsbar : sbar ∈ Sanctions.I)
    (hvertex : ∀ x ∈ Set.Icc xbar 1,
      max x sbar ≤ mwSenderVertexOne V x (mwCanonicalLeaderOne V x)) :
    ∀ x ∈ Set.Icc xbar 1, max x sbar ≤
      mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne V) (mwCanonicalLeaderOne V) x := by
  intro x hx
  have hxS : x ∈ Sanctions.S := ⟨le_trans hxbar0 hx.1, hx.2⟩
  have hmaxI : max x sbar ∈ Sanctions.I := by
    exact ⟨le_trans (le_trans hxbar0 hx.1) (le_max_left x sbar),
      max_le hx.2 hsbar.2⟩
  exact le_mwSigmaDynTop_one_of_le_vertex V hxS hmaxI (hvertex x hx)

/-- Conversely, every nonempty-basin floor reaches the top state and hence
forces the endpoint-spread inequality.  This is the sharp obstruction to
upgrading the selector monotonicity theorem to the full `hDynReg` package. -/
theorem mwCanonicalLeaderOne_endpoint_spread_of_floor
    (V : SBCF) {xbar sbar : ℝ} (hxbar1 : xbar ≤ 1)
    (hfloor : ∀ x ∈ Set.Icc xbar 1, max x sbar ≤
      mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne V) (mwCanonicalLeaderOne V) x) :
    10 * mwCanonicalLeaderOne V 1 - 1 ≤
      V (Sanctions.clipS' 1) - V (Sanctions.clipS' 0) := by
  have htop := hfloor 1 ⟨hxbar1, le_rfl⟩
  have hrule_mem := mechanismWitnessParams.σ_dyn_top_mem_I
    (mwSenderValueOne V) 1 (mwCanonicalLeaderOne V 1)
  have hrule_eq : mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne V) (mwCanonicalLeaderOne V) 1 = 1 := by
    change mechanismWitnessParams.σ_dyn_top
      (mwSenderValueOne V) 1 (mwCanonicalLeaderOne V 1) = 1
    have hone_le : (1 : ℝ) ≤ mechanismWitnessParams.σ_dyn_top
        (mwSenderValueOne V) 1 (mwCanonicalLeaderOne V 1) :=
      le_trans (le_max_left 1 sbar) htop
    exact le_antisymm hrule_mem.2 hone_le
  exact (mwDynamicTopRealizedRule_canonical_one_top_eq_one_iff V).mp hrule_eq

/-- A bounded continuous test value with a steeply negative endpoint spread.
It is not asserted to be an equilibrium value; it is used to test whether the
canonical selector result can be upgraded uniformly over continuation values. -/
noncomputable def mwSteeplyDecreasingValue : SBCF :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk (fun y : ↥(Sanctions.S : Set ℝ) => -100 * y.val)
      (by fun_prop))

@[simp] theorem mwSteeplyDecreasingValue_apply
    (y : ↥(Sanctions.S : Set ℝ)) :
    mwSteeplyDecreasingValue y = -100 * y.val := rfl

/-- **Disproof-first boundary check.**  Canonical full-width monotonicity does
not imply a selector-uniform dynamic floor: for a legitimate bounded
continuous continuation, the canonical realized response at the top state is
zero.  Any equilibrium floor must therefore use the fixed-point restrictions
on `V`, specifically the endpoint-spread inequality above. -/
theorem mwDynamicTopRealizedRule_canonical_one_no_uniform_floor_test :
    mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne mwSteeplyDecreasingValue)
      (mwCanonicalLeaderOne mwSteeplyDecreasingValue) 1 = 0 := by
  change mechanismWitnessParams.σ_dyn_top
    (mwSenderValueOne mwSteeplyDecreasingValue) 1
      (mwCanonicalLeaderOne mwSteeplyDecreasingValue 1) = 0
  rw [mwSigmaDynTop_eq_clip_vertex_one mwSteeplyDecreasingValue
    (by norm_num) _]
  have ha := mwCanonicalLeaderOne_mem mwSteeplyDecreasingValue 1
  have hclip1 := Sanctions.clipS'_val_eq_of_mem
    (by norm_num : (1 : ℝ) ∈ Sanctions.S)
  have hclip0 := Sanctions.clipS'_val_eq_of_mem
    (by norm_num : (0 : ℝ) ∈ Sanctions.S)
  have hv : mwSenderVertexOne mwSteeplyDecreasingValue 1
      (mwCanonicalLeaderOne mwSteeplyDecreasingValue 1) ≤ 0 := by
    unfold mwSenderVertexOne
    simp only [mwSteeplyDecreasingValue_apply]
    rw [hclip1, hclip0]
    nlinarith [ha.1]
  have hmin : min 1 (mwSenderVertexOne mwSteeplyDecreasingValue 1
      (mwCanonicalLeaderOne mwSteeplyDecreasingValue 1)) =
      mwSenderVertexOne mwSteeplyDecreasingValue 1
        (mwCanonicalLeaderOne mwSteeplyDecreasingValue 1) :=
    min_eq_right (le_trans hv (by norm_num))
  rw [hmin, max_eq_left hv]

/-- At a full-width shocked equilibrium, the Sender Bellman value equals its
dynamic objective evaluated at the greatest response. -/
theorem mwShockedOne_sender_bellman_eq_at_sigma
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    (x : ↥(Sanctions.S : Set ℝ)) :
    E.V_S x =
      mechanismWitnessParams.senderDynObjective (mwSenderValueOne E.V_S)
        x.val (E.α x.val)
        (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S)
          x.val (E.α x.val)) := by
  have hfix := congrArg (fun V : SBCF => V x) E.V_S_fix_shock
  change E.V_S x = mechanismWitnessParams.bellmanS_at E.α
    (fun y => mwSenderValueOne E.V_S y) x.val at hfix
  rw [hfix]
  unfold AbstractGame.Params.bellmanS_at
  let f : ℝ → ℝ := fun s =>
    mechanismWitnessParams.integrandS E.α
      (fun y => mwSenderValueOne E.V_S y) (x.val, s)
  let sstar := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S)
    x.val (E.α x.val)
  have hsstar : sstar ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hmax : IsMaxOn f Sanctions.I sstar := by
    intro s hs
    change mechanismWitnessParams.senderDynObjective (mwSenderValueOne E.V_S)
        x.val (E.α x.val) s ≤
      mechanismWitnessParams.senderDynObjective (mwSenderValueOne E.V_S)
        x.val (E.α x.val) sstar
    exact mechanismWitnessParams.σ_dyn_top_isMaxOn _ _ _ hs
  have himage_nonempty : (f '' Sanctions.I).Nonempty :=
    ⟨f sstar, ⟨sstar, hsstar, rfl⟩⟩
  have himage_bdd : BddAbove (f '' Sanctions.I) := by
    exact mechanismWitnessParams.integrandS_image_bddAbove E.hα
      (mwSenderValueOne E.V_S).continuous x.val
  have heq : sSup (f '' Sanctions.I) = f sstar := by
    apply le_antisymm
    · exact csSup_le himage_nonempty (fun y hy => by
        rcases hy with ⟨s, hs, rfl⟩
        exact hmax hs)
    · exact le_csSup himage_bdd ⟨sstar, hsstar, rfl⟩
  rw [heq]
  rfl

/-- At a full-width shocked equilibrium, the Target Bellman value equals its
joint objective evaluated at the equilibrium leader action. -/
theorem mwShockedOne_target_bellman_eq_at_alpha
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    (x : ↥(Sanctions.S : Set ℝ)) :
    E.V_T x =
      mechanismWitnessParams.joint_T_top_integrand
        (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S)
        x.val (E.α x.val) := by
  have hfix := E.V_T_fix_shock x
  change E.V_T x = sSup
    ((fun a => mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S)
      x.val a) '' Sanctions.I) at hfix
  rw [hfix]
  apply le_antisymm
  · apply csSup_le
    · refine ⟨mechanismWitnessParams.joint_T_top_integrand
        (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S)
        x.val 0, 0, ?_, rfl⟩
      norm_num [Sanctions.I]
    · rintro y ⟨a, ha, rfl⟩
      exact E.α_opt_shock x.val x.property ha
  · have h_bdd : BddAbove
        ((fun a => mechanismWitnessParams.joint_T_top_integrand
          (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S)
          x.val a) '' Sanctions.I) := by
      refine ⟨mechanismWitnessParams.joint_T_top_integrand
        (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S)
        x.val (E.α x.val), ?_⟩
      rintro y ⟨a, ha, rfl⟩
      exact E.α_opt_shock x.val x.property ha
    exact le_csSup h_bdd
      ⟨E.α x.val, E.α_mem x.val x.property, rfl⟩

/-- The full-width Sender fixed point imposes a sharp elementary upper bound
on its endpoint spread.  The proof compares the top-state optimum with the
same sanction at the bottom state and uses the exact affine smear slope. -/
theorem mwShockedOne_sender_endpoint_spread_le
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0) ≤
      (5 / 8) * (E.α 1 - E.α 0) + 35 / 16 := by
  let x0 := Sanctions.clipS' 0
  let x1 := Sanctions.clipS' 1
  let s1 := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S)
    1 (E.α 1)
  have hx0val : (x0 : ℝ) = 0 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have hx1val : (x1 : ℝ) = 1 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have hs1 : s1 ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hbell0 := mwShockedOne_sender_bellman_eq_at_sigma E x0
  have hbell1 := mwShockedOne_sender_bellman_eq_at_sigma E x1
  rw [hx0val] at hbell0
  rw [hx1val] at hbell1
  change E.V_S x0 = mechanismWitnessParams.senderDynObjective
      (mwSenderValueOne E.V_S) 0 (E.α 0)
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S)
        0 (E.α 0)) at hbell0
  change E.V_S x1 = mechanismWitnessParams.senderDynObjective
      (mwSenderValueOne E.V_S) 1 (E.α 1) s1 at hbell1
  have hmax0 := mechanismWitnessParams.σ_dyn_top_isMaxOn
    (mwSenderValueOne E.V_S) 0 (E.α 0) hs1
  change mechanismWitnessParams.senderDynObjective (mwSenderValueOne E.V_S)
      0 (E.α 0) s1 ≤
    mechanismWitnessParams.senderDynObjective (mwSenderValueOne E.V_S)
      0 (E.α 0)
      (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S)
        0 (E.α 0)) at hmax0
  have hvalue : E.V_S x1 - E.V_S x0 ≤
      mechanismWitnessParams.senderDynObjective (mwSenderValueOne E.V_S)
          1 (E.α 1) s1 -
        mechanismWitnessParams.senderDynObjective (mwSenderValueOne E.V_S)
          0 (E.α 0) s1 := by
    linarith
  have hF0 : mechanismWitnessParams.F 0 s1 ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem 0 s1 (by norm_num) hs1
  have hF1 : mechanismWitnessParams.F 1 s1 ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem 1 s1 (by norm_num) hs1
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_S
    (Sanctions.clipS' (mechanismWitnessParams.F 0 s1))
    (Sanctions.clipS' (mechanismWitnessParams.F 1 s1))
  rw [Sanctions.clipS'_val_eq_of_mem hF0,
    Sanctions.clipS'_val_eq_of_mem hF1] at hslope
  have ha0 := E.α_mem 0 (by norm_num)
  have ha1 := E.α_mem 1 (by norm_num)
  change E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0) ≤ _
  dsimp only [x0, x1] at hvalue
  change mwU_S 1 (E.α 1) s1
      + (1 / 2) * Sanctions.movAvgBCF one_pos E.V_S
        (Sanctions.clipS' (mechanismWitnessParams.F 1 s1))
      - (mwU_S 0 (E.α 0) s1
        + (1 / 2) * Sanctions.movAvgBCF one_pos E.V_S
          (Sanctions.clipS' (mechanismWitnessParams.F 0 s1))) ≥
    E.V_S (Sanctions.clipS' 1) - E.V_S (Sanctions.clipS' 0) at hvalue
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hslope
  unfold mwU_S at hvalue
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hvalue
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1.2)
    (by nlinarith [ha0.1, ha1.2] :
      0 ≤ (27 / 20) - (1 / 2) * (E.α 1 - E.α 0))]

/-- If a full-width shocked equilibrium were floored at the top state, the
Sender fixed point would force very low top-state compliance. -/
theorem mwShockedOne_alpha_top_le_of_top_floor
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    (htop : (1 : ℝ) ≤ mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne E.V_S) E.α 1) :
    E.α 1 ≤ 17 / 50 := by
  have hrule_mem := mechanismWitnessParams.σ_dyn_top_mem_I
    (mwSenderValueOne E.V_S) 1 (E.α 1)
  have hrule_eq : mechanismWitnessParams.σ_dyn_top
      (mwSenderValueOne E.V_S) 1 (E.α 1) = 1 :=
    le_antisymm hrule_mem.2 htop
  have hlower := (mwSigmaDynTop_one_top_eq_one_iff E.V_S (E.α 1)).mp hrule_eq
  have hupper := mwShockedOne_sender_endpoint_spread_le E
  have ha0 := E.α_mem 0 (by norm_num)
  nlinarith [ha0.1]

/-- The full-width Target fixed point has a uniform endpoint-spread bound.
The proof compares the bottom-state optimum with the top-state action, bounds
the stage-payoff change by three, and then solves the affine-smear inequality. -/
theorem mwShockedOne_target_endpoint_spread_le
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0) ≤ 60 / 11 := by
  let x0 := Sanctions.clipS' 0
  let x1 := Sanctions.clipS' 1
  let a1 := E.α 1
  let s0 := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 0 a1
  let s1 := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 a1
  have hx0val : (x0 : ℝ) = 0 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have hx1val : (x1 : ℝ) = 1 :=
    Sanctions.clipS'_val_eq_of_mem (by norm_num)
  have ha1 : a1 ∈ Sanctions.I := E.α_mem 1 (by norm_num)
  have hs0 : s0 ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs1 : s1 ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hsmono : s0 ≤ s1 := by
    exact mwSigmaDynTop_one_monotone_state_fixed_action E.V_S
      (by norm_num) (by norm_num) (by norm_num) a1
  have hbell0 := mwShockedOne_target_bellman_eq_at_alpha E x0
  have hbell1 := mwShockedOne_target_bellman_eq_at_alpha E x1
  rw [hx0val] at hbell0
  rw [hx1val] at hbell1
  have hopt0 := E.α_opt_shock 0 (by norm_num) ha1
  change mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S)
      0 a1 ≤
    mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S)
      0 (E.α 0) at hopt0
  have hvalue : E.V_T x1 - E.V_T x0 ≤
      mechanismWitnessParams.joint_T_top_integrand
          (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S)
          1 a1 -
        mechanismWitnessParams.joint_T_top_integrand
          (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S)
          0 a1 := by
    linarith
  change E.V_T x1 - E.V_T x0 ≤
      mwU_T 1 a1 s1 + (9 / 10) * Sanctions.movAvgBCF one_pos E.V_T
          (Sanctions.clipS' (mechanismWitnessParams.F 1 s1)) -
        (mwU_T 0 a1 s0 + (9 / 10) * Sanctions.movAvgBCF one_pos E.V_T
          (Sanctions.clipS' (mechanismWitnessParams.F 0 s0))) at hvalue
  have hF0 : mechanismWitnessParams.F 0 s0 ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem 0 s0 (by norm_num) hs0
  have hF1 : mechanismWitnessParams.F 1 s1 ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem 1 s1 (by norm_num) hs1
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_T
    (Sanctions.clipS' (mechanismWitnessParams.F 0 s0))
    (Sanctions.clipS' (mechanismWitnessParams.F 1 s1))
  rw [Sanctions.clipS'_val_eq_of_mem hF0,
    Sanctions.clipS'_val_eq_of_mem hF1] at hslope
  have hstage : mwU_T 1 a1 s1 - mwU_T 0 a1 s0 ≤ 3 := by
    have hc1 : 0 ≤ (1 / 2 : ℝ) + (1 / 2) * a1 := by
      nlinarith [ha1.1]
    have hc0 : 0 ≤ (1 / 2 : ℝ) - (1 / 2) * a1 := by
      nlinarith [ha1.2]
    have hs1mul := mul_le_mul_of_nonneg_right hs1.2 hc1
    have hs0mul := mul_le_mul_of_nonneg_right hs0.2 hc0
    unfold mwU_T
    nlinarith
  have hFdiff0 : 0 ≤ mechanismWitnessParams.F 1 s1 -
      mechanismWitnessParams.F 0 s0 := by
    simp only [mechanismWitnessParams_F, AbstractGame.affineF]
    nlinarith
  have hFdiff1 : mechanismWitnessParams.F 1 s1 -
      mechanismWitnessParams.F 0 s0 ≤ 1 := by
    nlinarith [hF1.2, hF0.1]
  have hmaster : E.V_T x1 - E.V_T x0 ≤ 3 +
      (9 / 20) * (mechanismWitnessParams.F 1 s1 -
        mechanismWitnessParams.F 0 s0) *
        (E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0)) := by
    nlinarith
  change E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0) ≤ _
  dsimp only [x0, x1] at hmaster
  by_cases hspread : 0 ≤
      E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0)
  · have hprod :
        (mechanismWitnessParams.F 1 s1 - mechanismWitnessParams.F 0 s0) *
            (E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0)) ≤
          E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hFdiff1) hspread]
    nlinarith
  · have hneg : E.V_T (Sanctions.clipS' 1) -
        E.V_T (Sanctions.clipS' 0) < 0 := lt_of_not_ge hspread
    exact le_trans (le_of_lt hneg) (by norm_num)

/-- **The full-width equilibrium floor is impossible.**  If the top-state
Sender response were one, the Sender fixed point would force `α(1) ≤ 17/50`.
The Target can then profitably deviate to action `1/2`: the exact Sender vertex
controls the accompanying sanction loss, while the Target endpoint-spread bound
controls the worst continuation loss. -/
theorem mwShockedOne_no_top_floor
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop) :
    ¬ ((1 : ℝ) ≤ mechanismWitnessParams.dynamicTopRealizedRule
      (mwSenderValueOne E.V_S) E.α 1) := by
  intro htop
  let a1 := E.α 1
  let shalf := mechanismWitnessParams.σ_dyn_top
    (mwSenderValueOne E.V_S) 1 (1 / 2)
  have ha1 : a1 ∈ Sanctions.I := E.α_mem 1 (by norm_num)
  have ha1_le : a1 ≤ 17 / 50 := by
    exact mwShockedOne_alpha_top_le_of_top_floor E htop
  have hrule_mem := mechanismWitnessParams.σ_dyn_top_mem_I
    (mwSenderValueOne E.V_S) 1 a1
  have hrule_eq : mechanismWitnessParams.σ_dyn_top
      (mwSenderValueOne E.V_S) 1 a1 = 1 := by
    exact le_antisymm hrule_mem.2 htop
  have hsender_lower :=
    (mwSigmaDynTop_one_top_eq_one_iff E.V_S a1).mp hrule_eq
  have hcurrent_vertex : (1 : ℝ) ≤ mwSenderVertexOne E.V_S 1 a1 := by
    unfold mwSenderVertexOne
    nlinarith
  have hy_mem : (19 / 24 : ℝ) + (5 / 12) * a1 ∈ Sanctions.I := by
    constructor <;> nlinarith [ha1.1]
  have hy_vertex : (19 / 24 : ℝ) + (5 / 12) * a1 ≤
      mwSenderVertexOne E.V_S 1 (1 / 2) := by
    unfold mwSenderVertexOne at hcurrent_vertex ⊢
    nlinarith
  have hshalf_lower : (19 / 24 : ℝ) + (5 / 12) * a1 ≤ shalf := by
    exact le_mwSigmaDynTop_one_of_le_vertex E.V_S (by norm_num)
      hy_mem hy_vertex
  have hshalf : shalf ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hopt := E.α_opt_shock 1 (by norm_num)
    (by norm_num : (1 / 2 : ℝ) ∈ Sanctions.I)
  change mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S)
      1 (1 / 2) ≤
    mechanismWitnessParams.joint_T_top_integrand
      (Sanctions.movAvgBCF one_pos E.V_T) (mwSenderValueOne E.V_S)
      1 a1 at hopt
  unfold AbstractGame.Params.joint_T_top_integrand at hopt
  simp only [mechanismWitnessParams_U_T, mechanismWitnessParams_β_T] at hopt
  change mwU_T 1 (1 / 2) shalf +
      (9 / 10) * Sanctions.movAvgBCF one_pos E.V_T
        (Sanctions.clipS' (mechanismWitnessParams.F 1 shalf)) ≤
    mwU_T 1 a1
        (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 a1) +
      (9 / 10) * Sanctions.movAvgBCF one_pos E.V_T
        (Sanctions.clipS' (mechanismWitnessParams.F 1
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne E.V_S) 1 a1))) at hopt
  rw [hrule_eq] at hopt
  have hFhalf : mechanismWitnessParams.F 1 shalf ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem 1 shalf (by norm_num) hshalf
  have hFone : mechanismWitnessParams.F 1 1 ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem 1 1 (by norm_num) (by norm_num)
  have hslope := Sanctions.movAvgBCF_one_sub_eq E.V_T
    (Sanctions.clipS' (mechanismWitnessParams.F 1 1))
    (Sanctions.clipS' (mechanismWitnessParams.F 1 shalf))
  rw [Sanctions.clipS'_val_eq_of_mem hFone,
    Sanctions.clipS'_val_eq_of_mem hFhalf] at hslope
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hopt hslope
  have htarget_upper := mwShockedOne_target_endpoint_spread_le E
  have hspread_product :
      (60 / 11) * (shalf - 1) ≤
        (E.V_T (Sanctions.clipS' 1) - E.V_T (Sanctions.clipS' 0)) *
          (shalf - 1) := by
    have hnonneg := mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr htarget_upper) (sub_nonpos.mpr hshalf.2)
    nlinarith
  have hquad := mul_nonneg_of_nonpos_of_nonpos
    (show a1 - 17 / 50 ≤ 0 by nlinarith)
    (show a1 + 17 / 50 - 173 / 176 ≤ 0 by nlinarith)
  unfold mwU_T at hopt
  nlinarith

/-- Hence no nonempty basin ending at the top state can satisfy the full-width
dynamic floor component used by `hDynReg`. -/
theorem mwShockedOne_no_dynamic_floor
    (E : (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop)
    {xbar sbar : ℝ} (hxbar1 : xbar ≤ 1) :
    ¬ (∀ x ∈ Set.Icc xbar 1,
      max x sbar ≤ mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne E.V_S) E.α x) := by
  exact Sanctions.no_upper_basin_floor_of_top_lt_one _
    (lt_of_not_ge (mwShockedOne_no_top_floor E)) hxbar1

theorem mwSenderDynObjective_adjusted_state_diff_eq
    (V : SBCF) {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ Sanctions.S) (hx₂ : x₂ ∈ Sanctions.S)
    (b : ℝ) {s t : ℝ} (hs : s ∈ Sanctions.I) (ht : t ∈ Sanctions.I) :
    mechanismWitnessParams.senderDynObjective (mwSenderValueOne V)
        x₂ (b + (27 / 10) * x₂) s
      - mechanismWitnessParams.senderDynObjective (mwSenderValueOne V)
        x₁ (b + (27 / 10) * x₁) s
      =
    mechanismWitnessParams.senderDynObjective (mwSenderValueOne V)
        x₂ (b + (27 / 10) * x₂) t
      - mechanismWitnessParams.senderDynObjective (mwSenderValueOne V)
        x₁ (b + (27 / 10) * x₁) t := by
  have hF₁s : mechanismWitnessParams.F x₁ s ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x₁ s hx₁ hs
  have hF₂s : mechanismWitnessParams.F x₂ s ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x₂ s hx₂ hs
  have hF₁t : mechanismWitnessParams.F x₁ t ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x₁ t hx₁ ht
  have hF₂t : mechanismWitnessParams.F x₂ t ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x₂ t hx₂ ht
  have hslope_s := Sanctions.movAvgBCF_one_sub_eq V
    (Sanctions.clipS' (mechanismWitnessParams.F x₁ s))
    (Sanctions.clipS' (mechanismWitnessParams.F x₂ s))
  have hslope_t := Sanctions.movAvgBCF_one_sub_eq V
    (Sanctions.clipS' (mechanismWitnessParams.F x₁ t))
    (Sanctions.clipS' (mechanismWitnessParams.F x₂ t))
  rw [Sanctions.clipS'_val_eq_of_mem hF₁s,
    Sanctions.clipS'_val_eq_of_mem hF₂s] at hslope_s
  rw [Sanctions.clipS'_val_eq_of_mem hF₁t,
    Sanctions.clipS'_val_eq_of_mem hF₂t] at hslope_t
  change mwU_S x₂ (b + (27 / 10) * x₂) s
      + (1 / 2) * Sanctions.movAvgBCF one_pos V
        (Sanctions.clipS' (mechanismWitnessParams.F x₂ s))
      - (mwU_S x₁ (b + (27 / 10) * x₁) s
        + (1 / 2) * Sanctions.movAvgBCF one_pos V
          (Sanctions.clipS' (mechanismWitnessParams.F x₁ s)))
    =
    mwU_S x₂ (b + (27 / 10) * x₂) t
      + (1 / 2) * Sanctions.movAvgBCF one_pos V
        (Sanctions.clipS' (mechanismWitnessParams.F x₂ t))
      - (mwU_S x₁ (b + (27 / 10) * x₁) t
        + (1 / 2) * Sanctions.movAvgBCF one_pos V
          (Sanctions.clipS' (mechanismWitnessParams.F x₁ t)))
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hslope_s hslope_t
  unfold mwU_S
  simp only [mechanismWitnessParams_F, AbstractGame.affineF]
  nlinarith [hslope_s, hslope_t]

theorem mwSigmaDynTop_adjusted_state_eq_one
    (V : SBCF) {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ Sanctions.S) (hx₂ : x₂ ∈ Sanctions.S) (b : ℝ) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
        x₁ (b + (27 / 10) * x₁) =
      mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
        x₂ (b + (27 / 10) * x₂) := by
  let s₁ := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
    x₁ (b + (27 / 10) * x₁)
  let s₂ := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
    x₂ (b + (27 / 10) * x₂)
  have hs₁ : s₁ ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs₂ : s₂ ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hmax₁ : IsMaxOn
      (fun s => mechanismWitnessParams.senderDynObjective (mwSenderValueOne V)
        x₁ (b + (27 / 10) * x₁) s) Sanctions.I s₁ :=
    fun s hs => mechanismWitnessParams.σ_dyn_top_isMaxOn _ _ _ hs
  have hmax₂ : IsMaxOn
      (fun s => mechanismWitnessParams.senderDynObjective (mwSenderValueOne V)
        x₂ (b + (27 / 10) * x₂) s) Sanctions.I s₂ :=
    fun s hs => mechanismWitnessParams.σ_dyn_top_isMaxOn _ _ _ hs
  have hmax₁_at₂ : IsMaxOn
      (fun s => mechanismWitnessParams.senderDynObjective (mwSenderValueOne V)
        x₂ (b + (27 / 10) * x₂) s) Sanctions.I s₁ := by
    intro s hs
    have hdiff := mwSenderDynObjective_adjusted_state_diff_eq V hx₁ hx₂ b hs hs₁
    have hle := hmax₁ hs
    change mechanismWitnessParams.senderDynObjective (mwSenderValueOne V)
        x₁ (b + (27 / 10) * x₁) s ≤
      mechanismWitnessParams.senderDynObjective (mwSenderValueOne V)
        x₁ (b + (27 / 10) * x₁) s₁ at hle
    change mechanismWitnessParams.senderDynObjective (mwSenderValueOne V)
        x₂ (b + (27 / 10) * x₂) s ≤
      mechanismWitnessParams.senderDynObjective (mwSenderValueOne V)
        x₂ (b + (27 / 10) * x₂) s₁
    linarith
  exact mechanismWitnessParams_dynamicArgmaxUnique_one V
    x₂ hx₂ (b + (27 / 10) * x₂) s₁ s₂ hs₁ hs₂
    (by simpa [AbstractGame.Params.senderDynObjective] using hmax₁_at₂)
    (by simpa [AbstractGame.Params.senderDynObjective] using hmax₂)

theorem mwSigmaDynTop_antitone_action_one
    (V : SBCF) {x : ℝ}
    {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂) :
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V) x a₂ ≤
      mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V) x a₁ := by
  obtain rfl | halt := ha.eq_or_lt
  · exact le_rfl
  let s₁ := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V) x a₁
  let s₂ := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V) x a₂
  have hs₁ : s₁ ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs₂ : s₂ ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hmax₁ : IsMaxOn
      (fun s => mechanismWitnessParams.senderDynObjective
        (mwSenderValueOne V) x a₁ s) Sanctions.I s₁ :=
    fun s hs => mechanismWitnessParams.σ_dyn_top_isMaxOn _ _ _ hs
  have hmax₂ : IsMaxOn
      (fun s => mechanismWitnessParams.senderDynObjective
        (mwSenderValueOne V) x a₂ s) Sanctions.I s₂ :=
    fun s hs => mechanismWitnessParams.σ_dyn_top_isMaxOn _ _ _ hs
  by_contra hnot
  have hlt : s₁ < s₂ := lt_of_not_ge hnot
  have h₁ := hmax₁ hs₂
  have h₂ := hmax₂ hs₁
  change mechanismWitnessParams.senderDynObjective (mwSenderValueOne V) x a₁ s₂ ≤
    mechanismWitnessParams.senderDynObjective (mwSenderValueOne V) x a₁ s₁ at h₁
  change mechanismWitnessParams.senderDynObjective (mwSenderValueOne V) x a₂ s₁ ≤
    mechanismWitnessParams.senderDynObjective (mwSenderValueOne V) x a₂ s₂ at h₂
  unfold AbstractGame.Params.senderDynObjective at h₁ h₂
  simp only [mechanismWitnessParams_U_S, mechanismWitnessParams_β_S] at h₁ h₂
  unfold mwU_S at h₁ h₂
  nlinarith [mul_pos (sub_pos.mpr halt) (sub_pos.mpr hlt)]

noncomputable def mwLeaderObjectiveAdjustedOne
    (V : SBCF) (x b : ℝ) : ℝ :=
  mwLeaderObjectiveOne V x (b + (27 / 10) * x)

theorem mwLeaderObjectiveAdjustedOne_strict_decreasingDifferences
    (V : SBCF) {x₁ x₂ b₁ b₂ : ℝ}
    (hx₁ : x₁ ∈ Sanctions.S) (hx₂ : x₂ ∈ Sanctions.S)
    (hxx : x₁ < x₂) (hbb : b₁ < b₂) :
    mwLeaderObjectiveAdjustedOne V x₂ b₂
        - mwLeaderObjectiveAdjustedOne V x₁ b₂ <
      mwLeaderObjectiveAdjustedOne V x₂ b₁
        - mwLeaderObjectiveAdjustedOne V x₁ b₁ := by
  let s₁ := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
    x₁ (b₁ + (27 / 10) * x₁)
  let s₂ := mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
    x₁ (b₂ + (27 / 10) * x₁)
  have hs₁ : s₁ ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs₂ : s₂ ∈ Sanctions.I :=
    mechanismWitnessParams.σ_dyn_top_mem_I _ _ _
  have hs_mono : s₂ ≤ s₁ := by
    apply mwSigmaDynTop_antitone_action_one V
    linarith
  have hshift₁ := mwSigmaDynTop_adjusted_state_eq_one V hx₁ hx₂ b₁
  have hshift₂ := mwSigmaDynTop_adjusted_state_eq_one V hx₁ hx₂ b₂
  change mechanismWitnessParams.joint_T_top_integrand
        (mwTargetValueOne V) (mwSenderValueOne V)
        x₂ (b₂ + (27 / 10) * x₂)
      - mechanismWitnessParams.joint_T_top_integrand
        (mwTargetValueOne V) (mwSenderValueOne V)
        x₁ (b₂ + (27 / 10) * x₁) <
    mechanismWitnessParams.joint_T_top_integrand
        (mwTargetValueOne V) (mwSenderValueOne V)
        x₂ (b₁ + (27 / 10) * x₂)
      - mechanismWitnessParams.joint_T_top_integrand
        (mwTargetValueOne V) (mwSenderValueOne V)
        x₁ (b₁ + (27 / 10) * x₁)
  unfold AbstractGame.Params.joint_T_top_integrand
  change mwU_T x₂ (b₂ + (27 / 10) * x₂)
        (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
          x₂ (b₂ + (27 / 10) * x₂))
      + (9 / 10) * mwTargetValueOne V
        (Sanctions.clipS' (mechanismWitnessParams.F x₂
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
            x₂ (b₂ + (27 / 10) * x₂))))
      - (mwU_T x₁ (b₂ + (27 / 10) * x₁) s₂
        + (9 / 10) * mwTargetValueOne V
          (Sanctions.clipS' (mechanismWitnessParams.F x₁ s₂))) <
    mwU_T x₂ (b₁ + (27 / 10) * x₂)
        (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
          x₂ (b₁ + (27 / 10) * x₂))
      + (9 / 10) * mwTargetValueOne V
        (Sanctions.clipS' (mechanismWitnessParams.F x₂
          (mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
            x₂ (b₁ + (27 / 10) * x₂))))
      - (mwU_T x₁ (b₁ + (27 / 10) * x₁) s₁
        + (9 / 10) * mwTargetValueOne V
          (Sanctions.clipS' (mechanismWitnessParams.F x₁ s₁)))
  rw [← hshift₂, ← hshift₁]
  let UTV : SBCF := (mwShocked one_pos).V_T_dyn_shock_local V
    (mwSigmaDynTop_continuous_subtype_one V)
  change mwU_T x₂ (b₂ + (27 / 10) * x₂) s₂
        + (9 / 10) * Sanctions.movAvgBCF one_pos UTV
          (Sanctions.clipS' (mechanismWitnessParams.F x₂ s₂))
      - (mwU_T x₁ (b₂ + (27 / 10) * x₁) s₂
        + (9 / 10) * Sanctions.movAvgBCF one_pos UTV
          (Sanctions.clipS' (mechanismWitnessParams.F x₁ s₂))) <
    mwU_T x₂ (b₁ + (27 / 10) * x₂) s₁
        + (9 / 10) * Sanctions.movAvgBCF one_pos UTV
          (Sanctions.clipS' (mechanismWitnessParams.F x₂ s₁))
      - (mwU_T x₁ (b₁ + (27 / 10) * x₁) s₁
        + (9 / 10) * Sanctions.movAvgBCF one_pos UTV
          (Sanctions.clipS' (mechanismWitnessParams.F x₁ s₁)))
  have hF₁s₁ : mechanismWitnessParams.F x₁ s₁ ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x₁ s₁ hx₁ hs₁
  have hF₂s₁ : mechanismWitnessParams.F x₂ s₁ ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x₂ s₁ hx₂ hs₁
  have hF₁s₂ : mechanismWitnessParams.F x₁ s₂ ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x₁ s₂ hx₁ hs₂
  have hF₂s₂ : mechanismWitnessParams.F x₂ s₂ ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x₂ s₂ hx₂ hs₂
  have hslope₁ := Sanctions.movAvgBCF_one_sub_eq UTV
    (Sanctions.clipS' (mechanismWitnessParams.F x₁ s₁))
    (Sanctions.clipS' (mechanismWitnessParams.F x₂ s₁))
  have hslope₂ := Sanctions.movAvgBCF_one_sub_eq UTV
    (Sanctions.clipS' (mechanismWitnessParams.F x₁ s₂))
    (Sanctions.clipS' (mechanismWitnessParams.F x₂ s₂))
  rw [Sanctions.clipS'_val_eq_of_mem hF₁s₁,
    Sanctions.clipS'_val_eq_of_mem hF₂s₁] at hslope₁
  rw [Sanctions.clipS'_val_eq_of_mem hF₁s₂,
    Sanctions.clipS'_val_eq_of_mem hF₂s₂] at hslope₂
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hslope₁ hslope₂
  unfold mwU_T
  simp only [mechanismWitnessParams_F, AbstractGame.affineF]
  nlinarith [hslope₁, hslope₂,
    mul_pos (sub_pos.mpr hxx) (sub_pos.mpr hbb)]

theorem mwCanonicalLeaderOne_adjusted_antitoneOn (V : SBCF) :
    ∀ x₁ ∈ Sanctions.S, ∀ x₂ ∈ Sanctions.S, x₁ ≤ x₂ →
      mwCanonicalLeaderOne V x₂ - (27 / 10) * x₂ ≤
        mwCanonicalLeaderOne V x₁ - (27 / 10) * x₁ := by
  intro x₁ hx₁ x₂ hx₂ hxx_le
  obtain rfl | hxx := hxx_le.eq_or_lt
  · exact le_rfl
  let b₁ := mwCanonicalLeaderOne V x₁ - (27 / 10) * x₁
  let b₂ := mwCanonicalLeaderOne V x₂ - (27 / 10) * x₂
  by_contra hnot
  have hbb : b₁ < b₂ := lt_of_not_ge hnot
  have ha₁ := mwCanonicalLeaderOne_mem V x₁
  have ha₂ := mwCanonicalLeaderOne_mem V x₂
  have ha₁₂ : b₂ + (27 / 10) * x₁ ∈ Sanctions.I := by
    constructor <;> dsimp only [b₁, b₂] at hbb ⊢ <;> nlinarith [ha₁.1, ha₂.2]
  have ha₂₁ : b₁ + (27 / 10) * x₂ ∈ Sanctions.I := by
    constructor <;> dsimp only [b₁, b₂] at hbb ⊢ <;> nlinarith [ha₁.1, ha₂.2]
  have hopt₁ := mwCanonicalLeaderOne_isMaxOn V ⟨x₁, hx₁⟩ ha₁₂
  have hopt₂ := mwCanonicalLeaderOne_isMaxOn V ⟨x₂, hx₂⟩ ha₂₁
  change mwLeaderObjectiveOne V x₁ (b₂ + (27 / 10) * x₁) ≤
    mwLeaderObjectiveOne V x₁ (mwCanonicalLeaderOne V x₁) at hopt₁
  change mwLeaderObjectiveOne V x₂ (b₁ + (27 / 10) * x₂) ≤
    mwLeaderObjectiveOne V x₂ (mwCanonicalLeaderOne V x₂) at hopt₂
  have hstrict := mwLeaderObjectiveAdjustedOne_strict_decreasingDifferences
    V hx₁ hx₂ hxx hbb
  have hb₁₁ : b₁ + (27 / 10) * x₁ = mwCanonicalLeaderOne V x₁ := by
    dsimp only [b₁]
    ring
  have hb₂₂ : b₂ + (27 / 10) * x₂ = mwCanonicalLeaderOne V x₂ := by
    dsimp only [b₂]
    ring
  unfold mwLeaderObjectiveAdjustedOne at hstrict
  rw [hb₁₁, hb₂₂] at hstrict
  linarith

theorem mwDynamicTopRealizedRule_canonical_one_monotoneOn (V : SBCF) :
    MonotoneOn
      (mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne V) (mwCanonicalLeaderOne V))
      Sanctions.S := by
  intro x₁ hx₁ x₂ hx₂ hxx
  let b₁ := mwCanonicalLeaderOne V x₁ - (27 / 10) * x₁
  let b₂ := mwCanonicalLeaderOne V x₂ - (27 / 10) * x₂
  have hb : b₂ ≤ b₁ :=
    mwCanonicalLeaderOne_adjusted_antitoneOn V x₁ hx₁ x₂ hx₂ hxx
  have hshift := mwSigmaDynTop_adjusted_state_eq_one V hx₁ hx₂ b₁
  have hanti := mwSigmaDynTop_antitone_action_one (x := x₂) V
    (show b₂ + (27 / 10) * x₂ ≤ b₁ + (27 / 10) * x₂ by linarith)
  change mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
      x₁ (mwCanonicalLeaderOne V x₁) ≤
    mechanismWitnessParams.σ_dyn_top (mwSenderValueOne V)
      x₂ (mwCanonicalLeaderOne V x₂)
  have hb₁₁ : b₁ + (27 / 10) * x₁ = mwCanonicalLeaderOne V x₁ := by
    dsimp only [b₁]
    ring
  have hb₂₂ : b₂ + (27 / 10) * x₂ = mwCanonicalLeaderOne V x₂ := by
    dsimp only [b₂]
    ring
  rw [← hb₁₁, hshift, ← hb₂₂]
  exact hanti

theorem mwSenderDynObjective_canonical_one_increasingDifferencesOn
    (V : SBCF) :
    Sanctions.MilgromShannon.IncreasingDifferencesOn Sanctions.I Sanctions.S
      (fun s x => mechanismWitnessParams.senderDynObjective
        (mwSenderValueOne V) x (mwCanonicalLeaderOne V x) s) := by
  intro s s' x x' hs hs' hss hx hx' hxx
  have hb := mwCanonicalLeaderOne_adjusted_antitoneOn V x hx x' hx' hxx
  have hFxs : mechanismWitnessParams.F x s ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x s hx hs
  have hFxs' : mechanismWitnessParams.F x s' ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x s' hx hs'
  have hFx's : mechanismWitnessParams.F x' s ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x' s hx' hs
  have hFx's' : mechanismWitnessParams.F x' s' ∈ Sanctions.S :=
    mechanismWitnessParams.F_mem x' s' hx' hs'
  have hslope_x := Sanctions.movAvgBCF_one_sub_eq V
    (Sanctions.clipS' (mechanismWitnessParams.F x s))
    (Sanctions.clipS' (mechanismWitnessParams.F x s'))
  have hslope_x' := Sanctions.movAvgBCF_one_sub_eq V
    (Sanctions.clipS' (mechanismWitnessParams.F x' s))
    (Sanctions.clipS' (mechanismWitnessParams.F x' s'))
  rw [Sanctions.clipS'_val_eq_of_mem hFxs,
    Sanctions.clipS'_val_eq_of_mem hFxs'] at hslope_x
  rw [Sanctions.clipS'_val_eq_of_mem hFx's,
    Sanctions.clipS'_val_eq_of_mem hFx's'] at hslope_x'
  change mwU_S x (mwCanonicalLeaderOne V x) s'
        + (1 / 2) * Sanctions.movAvgBCF one_pos V
          (Sanctions.clipS' (mechanismWitnessParams.F x s'))
      - (mwU_S x (mwCanonicalLeaderOne V x) s
        + (1 / 2) * Sanctions.movAvgBCF one_pos V
          (Sanctions.clipS' (mechanismWitnessParams.F x s))) ≤
    mwU_S x' (mwCanonicalLeaderOne V x') s'
        + (1 / 2) * Sanctions.movAvgBCF one_pos V
          (Sanctions.clipS' (mechanismWitnessParams.F x' s'))
      - (mwU_S x' (mwCanonicalLeaderOne V x') s
        + (1 / 2) * Sanctions.movAvgBCF one_pos V
          (Sanctions.clipS' (mechanismWitnessParams.F x' s)))
  simp only [mechanismWitnessParams_F, AbstractGame.affineF] at hslope_x hslope_x'
  unfold mwU_S
  simp only [mechanismWitnessParams_F, AbstractGame.affineF]
  nlinarith [hslope_x, hslope_x']

theorem mwSenderDynObjective_canonical_one_IDOFamilyOn (V : SBCF) :
    Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I Sanctions.S
      (fun s x => mechanismWitnessParams.senderDynObjective
        (mwSenderValueOne V) x (mwCanonicalLeaderOne V x) s) :=
  Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn
    (mwSenderDynObjective_canonical_one_increasingDifferencesOn V).toSingleCrossingOn

theorem mwDynamicTopRealizedRule_canonical_one_monotoneOn_of_IDO
    (V : SBCF) :
    MonotoneOn
      (mechanismWitnessParams.dynamicTopRealizedRule
        (mwSenderValueOne V) (mwCanonicalLeaderOne V))
      Sanctions.S := by
  exact mechanismWitnessParams.dynamicTopRealizedRule_mono_of_IDOFamilyOn
    (xbar := 0) (mwSenderDynObjective_canonical_one_IDOFamilyOn V)

end Sanctions.Examples
