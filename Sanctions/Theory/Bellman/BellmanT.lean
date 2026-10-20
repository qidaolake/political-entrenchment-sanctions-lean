/-
Sanctions/Theory/Bellman/BellmanT.lean

**Abstract scalar Target Bellman fixed point on `AbstractGame.Params`.**

Parametric over the abstract structure
`Sanctions.AbstractGame.Params` (no LQ-specific formulas): the next
state is the abstract transition `p.F` evaluated at the Sender
response (`F_pair` below; canonical instance `affineF`), never a
hard-coded law. The Bellman operator on `(↥S →ᵇ ℝ)` is a
`β_T`-contraction; the Banach fixed point `V_T` exists and satisfies
the abstract Bellman equation pointwise on `↥S`.

**Rule-1 compliance.** The abstract `σ` is coupled to `U_S` via
`σ_isMaxOn_U_S` in `AbstractGame.Params` (Sender stage-game argmax).
The Target argmax is realized through the Bellman fixed point itself
(`V_T_bellman_eq` below): there is no fixed Target action plugged in.
Headline theorems built on this layer pass an α and a Bellman-
optimality hypothesis, satisfying Rule 1.

**Rule-3 compliance.** Every theorem here uses ONLY the structural
hypotheses of `AbstractGame.Params` — `U_T_continuous`, `F_continuous`,
`β_T_mem` — and the static-selector continuity instance
`[p.StaticSelectorContinuous]`. No new external hypothesis. (Uniform boundedness
of `U_T` on the feasible cube `[0,1]³` is derived locally from
continuity + compactness, not received as a postulate.)

**Round BJ5.1 (2026-10-07).** Joint continuity of the static selector `σ` was
the `Params` field `σ_continuous`; it is now the class
`Params.StaticSelectorContinuous`. This file is one of the places that reads
it: the integrand `U_T(x, a, σ(x, a)) + β_T V(F(x, σ(x, a)))` is continuous in
`(x, a)` only if `σ` is, and the Bellman operator `bellmanBCF` and its fixed
point `V_T` (the Target's value against the static Sender) are built from that
continuity. So `bellmanBCF`, `V_T` and every lemma about them take the instance
as a binder; the definitions `σ_pair`, `U_T_at`, `F_pair`, `integrand`,
`bellmanOn_at`, `bellmanOnS`, `integrand_pointwise_diff` and `β_T_nnreal` do
not. All general in `F`. The condition moved from every `Params` to these
binders; no statement says less than before at an economy that has it.

**Rule-5 compliance.** Parametric over `AbstractGame.Params`. No
witness-specific.
-/

import Sanctions.Postulates.AbstractGame
import Sanctions.Domain.UnitIntervalProjection
import Sanctions.Foundations.SupDiff
import Sanctions.Foundations.StokeyLucas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Bounded.Basic

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Bellman integrand on `ℝ × ℝ` (state × action), abstract version -/

/-- The Sender response `σ x a` packaged on `ℝ × ℝ`. -/
@[simp] noncomputable def σ_pair (xa : ℝ × ℝ) : ℝ := p.σ xa.1 xa.2

theorem σ_pair_continuous [p.StaticSelectorContinuous] : Continuous p.σ_pair := p.σ_continuous

/-- `U_T x a (σ x a)` packaged on `ℝ × ℝ`. -/
@[simp] noncomputable def U_T_at (xa : ℝ × ℝ) : ℝ :=
  p.U_T xa.1 xa.2 (p.σ_pair xa)

theorem U_T_at_continuous [p.StaticSelectorContinuous] : Continuous p.U_T_at := by
  unfold U_T_at σ_pair
  have hσ := p.σ_continuous
  have hU_T := p.U_T_continuous
  -- xas : ℝ × ℝ → (xas.1, xas.2, σ(xas)) and apply U_T which is continuous on ℝ³.
  have h_triple : Continuous
      (fun xa : ℝ × ℝ => (xa.1, xa.2, p.σ xa.1 xa.2)) := by
    refine .prodMk continuous_fst (.prodMk continuous_snd ?_)
    exact hσ
  exact hU_T.comp h_triple

/-- Next state `F(x, σ(x, a))` — the abstract transition `p.F`
evaluated at the Sender response — packaged on `ℝ × ℝ`. The canonical
instance is `affineF δ` (`x' = (1−δ)·x + δ·σ(x, a)`), but nothing here
unfolds it. -/
@[simp] noncomputable def F_pair (xa : ℝ × ℝ) : ℝ :=
  p.F xa.1 (p.σ_pair xa)

theorem F_pair_continuous [p.StaticSelectorContinuous] : Continuous p.F_pair := by
  unfold F_pair σ_pair
  have h_pair : Continuous (fun xa : ℝ × ℝ => (xa.1, p.σ xa.1 xa.2)) :=
    continuous_fst.prodMk p.σ_continuous
  exact p.F_continuous.comp h_pair

/-- Bellman integrand `U_T + β_T · V(F)`. -/
noncomputable def integrand (V : ↥(Sanctions.S : Set ℝ) → ℝ) (xa : ℝ × ℝ) : ℝ :=
  p.U_T_at xa + p.β_T * V (Sanctions.clipS' (p.F_pair xa))

theorem integrand_continuous [p.StaticSelectorContinuous]
    {V : ↥(Sanctions.S : Set ℝ) → ℝ} (hV : Continuous V) :
    Continuous (p.integrand V) := by
  unfold integrand
  have hU := p.U_T_at_continuous
  have hF := p.F_pair_continuous
  have hclip : Continuous (Sanctions.clipS' : ℝ → ↥(Sanctions.S : Set ℝ)) :=
    Sanctions.clipS'_continuous
  exact hU.add (continuous_const.mul (hV.comp (hclip.comp hF)))

/-! ## Pointwise Bellman value -/

noncomputable def bellmanOn_at
    (V : ↥(Sanctions.S : Set ℝ) → ℝ) (x : ℝ) : ℝ :=
  sSup ((fun a => p.integrand V (x, a)) '' Sanctions.I)

theorem bellmanOn_at_continuous [p.StaticSelectorContinuous]
    {V : ↥(Sanctions.S : Set ℝ) → ℝ} (hV : Continuous V) :
    Continuous (p.bellmanOn_at V) := by
  unfold bellmanOn_at
  have hI : IsCompact (Sanctions.I : Set ℝ) := isCompact_Icc
  have hf : Continuous ↿(fun (x : ℝ) (a : ℝ) => p.integrand V (x, a)) := by
    exact p.integrand_continuous hV
  exact hI.continuous_sSup hf

noncomputable def bellmanOnS
    (V : ↥(Sanctions.S : Set ℝ) → ℝ) : ↥(Sanctions.S : Set ℝ) → ℝ :=
  fun x => p.bellmanOn_at V x.val

theorem bellmanOnS_continuous [p.StaticSelectorContinuous]
    {V : ↥(Sanctions.S : Set ℝ) → ℝ} (hV : Continuous V) :
    Continuous (p.bellmanOnS V) := by
  unfold bellmanOnS
  exact (p.bellmanOn_at_continuous hV).comp continuous_subtype_val

/-! ## Bellman operator on `↥S →ᵇ ℝ` -/

noncomputable def bellmanBCF [p.StaticSelectorContinuous]
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨p.bellmanOnS (fun x => V x), p.bellmanOnS_continuous V.continuous⟩

@[simp] theorem bellmanBCF_apply [p.StaticSelectorContinuous]
    (V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)) :
    p.bellmanBCF V x = p.bellmanOnS (fun y => V y) x := rfl

/-! ## Contraction property -/

theorem integrand_at_continuous [p.StaticSelectorContinuous]
    {V : ↥(Sanctions.S : Set ℝ) → ℝ} (hV : Continuous V) (x : ℝ) :
    Continuous (fun a : ℝ => p.integrand V (x, a)) :=
  (p.integrand_continuous hV).comp
    (Continuous.prodMk continuous_const continuous_id)

theorem integrand_pointwise_diff
    (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) (a : ℝ) :
    |p.integrand (fun y => V y) (x, a) - p.integrand (fun y => W y) (x, a)|
      ≤ p.β_T * dist V W := by
  unfold integrand
  have heq : p.U_T_at (x, a) + p.β_T * V (Sanctions.clipS' (p.F_pair (x, a)))
              - (p.U_T_at (x, a) + p.β_T * W (Sanctions.clipS' (p.F_pair (x, a))))
            = p.β_T * (V (Sanctions.clipS' (p.F_pair (x, a)))
                       - W (Sanctions.clipS' (p.F_pair (x, a)))) := by ring
  rw [heq, abs_mul, abs_of_nonneg p.β_T_mem.1]
  have h_pt : dist (V (Sanctions.clipS' (p.F_pair (x, a))))
                   (W (Sanctions.clipS' (p.F_pair (x, a))))
                ≤ dist V W :=
    BoundedContinuousFunction.dist_coe_le_dist _
  rw [Real.dist_eq] at h_pt
  exact mul_le_mul_of_nonneg_left h_pt p.β_T_mem.1

theorem integrand_image_bddAbove [p.StaticSelectorContinuous]
    {V : ↥(Sanctions.S : Set ℝ) → ℝ} (hV : Continuous V) (x : ℝ) :
    BddAbove ((fun a => p.integrand V (x, a)) '' Sanctions.I) :=
  (isCompact_Icc.image (p.integrand_at_continuous hV x)).bddAbove

theorem bellmanBCF_pointwise_dist [p.StaticSelectorContinuous]
    (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)) :
    dist (p.bellmanBCF V x) (p.bellmanBCF W x) ≤ p.β_T * dist V W := by
  change |p.bellmanBCF V x - p.bellmanBCF W x| ≤ p.β_T * dist V W
  have heq_V : p.bellmanBCF V x =
      sSup ((fun a => p.integrand (fun y => V y) (x.val, a)) '' Sanctions.I) := rfl
  have heq_W : p.bellmanBCF W x =
      sSup ((fun a => p.integrand (fun y => W y) (x.val, a)) '' Sanctions.I) := rfl
  rw [heq_V, heq_W]
  apply Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd
    (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩
    (M := p.β_T * dist V W)
    (Bf := sSup ((fun a => p.integrand (fun y => V y) (x.val, a)) '' Sanctions.I))
    (Bg := sSup ((fun a => p.integrand (fun y => W y) (x.val, a)) '' Sanctions.I))
  · intro a _ha
    exact p.integrand_pointwise_diff V W x.val a
  · intro a ha
    exact le_csSup (p.integrand_image_bddAbove V.continuous x.val) ⟨a, ha, rfl⟩
  · intro a ha
    exact le_csSup (p.integrand_image_bddAbove W.continuous x.val) ⟨a, ha, rfl⟩

/-! ## Fixed-point existence -/

noncomputable def β_T_nnreal : NNReal := ⟨p.β_T, p.β_T_mem.1⟩

theorem β_T_nnreal_lt_one : p.β_T_nnreal < 1 := by
  change (p.β_T_nnreal : ℝ) < (1 : ℝ)
  exact p.β_T_mem.2

/-- **Existence and uniqueness of the abstract Target value function.**
The Bellman fixed point on `↥S →ᵇ ℝ`: the Target's value when the Sender plays
the static selector `σ`. General in `F`. It needs `[p.StaticSelectorContinuous]`
(round BJ5.1: formerly the `Params` field `σ_continuous`), because the operator
it fixes maps continuous functions to continuous functions only when `σ` is
jointly continuous. -/
noncomputable def V_T [p.StaticSelectorContinuous] : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  ContractingWith.fixedPoint p.bellmanBCF (by
    refine ⟨p.β_T_nnreal_lt_one, ?_⟩
    apply lipschitzWith_of_pointwise_dist_le
    intro V W x
    have h := p.bellmanBCF_pointwise_dist V W x
    convert h using 2)

theorem V_T_isFixedPoint [p.StaticSelectorContinuous] : p.bellmanBCF p.V_T = p.V_T := by
  unfold V_T
  exact ContractingWith.fixedPoint_isFixedPt _

/-- **Pointwise Bellman equation** for the abstract Target value function. -/
theorem V_T_bellman_eq [p.StaticSelectorContinuous] (x : ↥(Sanctions.S : Set ℝ)) :
    p.V_T x =
      sSup ((fun a => p.U_T x.val a (p.σ x.val a)
              + p.β_T * p.V_T
                  (Sanctions.clipS' (p.F x.val (p.σ x.val a)))) ''
              Sanctions.I) := by
  have h := p.V_T_isFixedPoint
  have hx : p.bellmanBCF p.V_T x = p.V_T x := by rw [h]
  rw [← hx, bellmanBCF_apply, bellmanOnS, bellmanOn_at]
  rfl

theorem V_T_bdd [p.StaticSelectorContinuous] : ∃ C, ∀ x, |p.V_T x| ≤ C := by
  refine ⟨‖p.V_T‖, fun x => ?_⟩
  exact BoundedContinuousFunction.norm_coe_le_norm p.V_T x

/-! ## Pointwise monotonicity in V (cone preservation in V argument) -/

/-- **bellmanBCF is monotone in V**: `V ≤ W pointwise ⇒ bellmanBCF V ≤
bellmanBCF W pointwise`. (Note: this is monotonicity in the V argument
of the Bellman operator, NOT monotonicity in x of the value function.) -/
theorem bellmanBCF_monotone_pointwise [p.StaticSelectorContinuous]
    (V W : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_le : ∀ x : ↥(Sanctions.S : Set ℝ), V x ≤ W x)
    (x : ↥(Sanctions.S : Set ℝ)) :
    p.bellmanBCF V x ≤ p.bellmanBCF W x := by
  show p.bellmanOnS (fun y => V y) x ≤ p.bellmanOnS (fun y => W y) x
  unfold bellmanOnS bellmanOn_at
  have hβ_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have h_int_le : ∀ a, p.integrand (fun y => V y) (x.val, a)
                       ≤ p.integrand (fun y => W y) (x.val, a) := by
    intro a
    unfold integrand
    have h_V_le : V (Sanctions.clipS' (p.F_pair (x.val, a)))
                   ≤ W (Sanctions.clipS' (p.F_pair (x.val, a))) :=
      h_le (Sanctions.clipS' (p.F_pair (x.val, a)))
    have h_mul : p.β_T * V (Sanctions.clipS' (p.F_pair (x.val, a)))
                  ≤ p.β_T * W (Sanctions.clipS' (p.F_pair (x.val, a))) :=
      mul_le_mul_of_nonneg_left h_V_le hβ_nn
    linarith
  apply csSup_le
  · exact ⟨p.integrand (fun y => V y) (x.val, 0), 0, by simp [Sanctions.I], rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    calc p.integrand (fun y => V y) (x.val, a)
        ≤ p.integrand (fun y => W y) (x.val, a) := h_int_le a
      _ ≤ sSup ((fun a => p.integrand (fun y => W y) (x.val, a)) '' Sanctions.I) :=
          le_csSup (p.integrand_image_bddAbove W.continuous x.val) ⟨a, ha, rfl⟩

/-- **SLP 4.14 (Bellman supersolution upper bound) — abstract.**
If `vHat : ↥S →ᵇ ℝ` satisfies `bellmanBCF vHat ≤ vHat` pointwise on
`↥S` (i.e. `vHat` is a supersolution), then `V_T ≤ vHat` pointwise. -/
theorem V_T_le_of_supersolution [p.StaticSelectorContinuous]
    (vHat : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_super : ∀ x : ↥(Sanctions.S : Set ℝ), p.bellmanBCF vHat x ≤ vHat x)
    (x : ↥(Sanctions.S : Set ℝ)) :
    p.V_T x ≤ vHat x := by
  have h_iter : ∀ n : ℕ, ∀ y : ↥(Sanctions.S : Set ℝ),
      (p.bellmanBCF^[n] vHat) y ≤ vHat y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply']
      calc p.bellmanBCF (p.bellmanBCF^[k] vHat) y
          ≤ p.bellmanBCF vHat y :=
            p.bellmanBCF_monotone_pointwise _ _ ih y
        _ ≤ vHat y := h_super y
  have hcontr : ContractingWith p.β_T_nnreal p.bellmanBCF := by
    refine ⟨p.β_T_nnreal_lt_one, ?_⟩
    apply lipschitzWith_of_pointwise_dist_le
    intro V W x
    convert p.bellmanBCF_pointwise_dist V W x using 2
  have h_tend :
      Filter.Tendsto (fun n => p.bellmanBCF^[n] vHat) Filter.atTop
        (𝓝 p.V_T) := by
    have : p.V_T = hcontr.fixedPoint := by
      unfold V_T; congr
    rw [this]
    exact hcontr.tendsto_iterate_fixedPoint vHat
  have h_eval_cont : Continuous (fun V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ => V x) :=
    ContinuousEvalConst.continuous_eval_const x
  have h_closed : IsClosed
      {V : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ | V x ≤ vHat x} :=
    isClosed_le h_eval_cont continuous_const
  exact h_closed.mem_of_tendsto h_tend
    (Filter.Eventually.of_forall (fun n => h_iter n x))

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
