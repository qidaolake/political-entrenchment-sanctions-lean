/-
Sanctions/Theory/Equilibrium/JointMPE.lean

**Abstract forward-looking Sender argmax + joint Bellman.**

Parametric over `Sanctions.AbstractGame.Params`. Constructs:

* `σ_dyn` — the Sender's forward-looking argmax of
  `U_S(x, a, s) + β_S · V_S(F(x, s))` over `s ∈ [0,1]`, via
  `IsCompact.exists_isMaxOn` + `Classical.choose`.
* `joint_T_integrand` — Target Bellman integrand with σ replaced by σ_dyn.
* `T_T_joint` — Target Bellman value with forward-looking Sender.

Together with the row-Lipschitz Banach contraction templates below,
this is the abstract joint MPE existence theorem under explicit
sufficient conditions.

**Rule-1 compliance.** σ_dyn is the *true* argmax of the dynamic
Sender objective (vs σ which is the myopic argmax). For β_S > 0,
forward-looking joint MPE results should use σ_dyn, not σ.

**Rule-3 compliance.** No new external hypothesis. Existence of
σ_dyn uses `IsCompact.exists_isMaxOn` which only needs continuity of
the Sender objective in `s`, which follows from `U_S_continuous`
and V_S being a BCF. (The static selector's continuity, the instance
`[p.StaticSelectorContinuous]` since round BJ5.1, is not needed for σ_dyn.)

**Rule-5 compliance.** Parametric over `AbstractGame.Params`.

**Continuity note.** σ_dyn is `Classical.choose`-defined. Its joint
`(x, a)`-continuity is machine-checked under a local uniqueness
hypothesis in `Theory/Equilibrium/BergeContinuity.lean` via the full Berge
maximum theorem (`σ_dyn_continuous_of_unique`); the resulting
`dynamicSenderResponse` is a genuine `JointMPE.SenderResponse`
instance under a parametric uniqueness hypothesis (canonical
sufficient condition: strict concavity of the complete dynamic Sender
objective in `s`; stage concavity of `U_S` alone is insufficient). The remaining
open content is the **quantitative Lipschitz-in-V_S** discharge for
nontrivial joint row-Lipschitz (the conditional version is in
`Theory/Equilibrium/JointLipschitz.lean`).

**Provenance of existence (2026-06-13, option B).** The row-Lipschitz /
Schur-margin route here and in `PerovExistence.lean` is a *sufficient*
condition for the joint operator to contract; it is the wrong instrument
for the bistable-flip regime, because the deterministic transition
`F(x,s) = (1-δ)x + δs` is an **atomic (Dirac) kernel**. For a dynamic
*game* (a fixed point of a best-response map), naive value/best-response
iteration on a deterministic kernel **cycles** rather than converging —
the known atomic-kernel degeneracy (Doraszelski–Satterthwaite 2010 §3;
confirmed numerically for this model: damping fails, a small atomless
shock restores convergence in ~60 iters while preserving the two basins).
Existence of the stationary feedback Markov-perfect (Stackelberg)
equilibrium is therefore established **not** by this contraction route but
by the **purified model** `x' = (1-δ)x + δs + ε` (ε atomless): He–Sun 2017
Thm 1 / Cor 1 (decomposable coarser transition kernel) gives existence,
and the deterministic transition is the ε→0 limit (D–S 2010 §7). See
`docs/archive/EXISTENCE-VIA-PURIFICATION-NOTE.md`. The headline theorems below remain
honestly named **conditional on** an equilibrium (Rule 15); existence is
literature-grounded, not machine-checked (Brouwer/Schauder/He–Sun are not
in mathlib). This adds no axiom and no `Params` field.
-/

import Sanctions.Theory.Bellman.BellmanT
import Sanctions.Theory.Bellman.BellmanS
import Sanctions.Foundations.TarskiMPE
import Sanctions.Foundations.PerovContraction
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Contracting

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Forward-looking Sender argmax (no derivatives, via compact-image max) -/

theorem sender_integrand_continuous_in_s
    {V_S : ↥(Sanctions.S : Set ℝ) → ℝ} (hV_S : Continuous V_S) (x a : ℝ) :
    Continuous (fun s : ℝ =>
      p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s))) := by
  have h_triple : Continuous (fun s : ℝ => (x, a, s)) := by
    refine .prodMk continuous_const (.prodMk continuous_const continuous_id)
  have hU : Continuous (fun s : ℝ => p.U_S x a s) :=
    p.U_S_continuous.comp h_triple
  have hclip : Continuous (Sanctions.clipS' : ℝ → ↥(Sanctions.S : Set ℝ)) :=
    Sanctions.clipS'_continuous
  have hF : Continuous (fun s : ℝ => p.F x s) :=
    p.F_continuous.comp (continuous_const.prodMk continuous_id)
  exact hU.add (continuous_const.mul (hV_S.comp (hclip.comp hF)))

theorem sender_arg_max_exists
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    ∃ s ∈ Sanctions.I, IsMaxOn (fun s' => p.U_S x a s'
      + p.β_S * V_S (Sanctions.clipS' (p.F x s'))) Sanctions.I s := by
  apply IsCompact.exists_isMaxOn isCompact_Icc ⟨0, by simp [Sanctions.I]⟩
  exact (p.sender_integrand_continuous_in_s V_S.continuous x a).continuousOn

/-- Forward-looking Sender argmax (the *dynamic* Sender response). -/
noncomputable def σ_dyn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  Classical.choose (p.sender_arg_max_exists V_S x a)

theorem σ_dyn_mem
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    p.σ_dyn V_S x a ∈ Sanctions.I :=
  (Classical.choose_spec (p.sender_arg_max_exists V_S x a)).1

theorem σ_dyn_isMaxOn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    IsMaxOn (fun s' => p.U_S x a s'
      + p.β_S * V_S (Sanctions.clipS' (p.F x s'))) Sanctions.I
      (p.σ_dyn V_S x a) :=
  (Classical.choose_spec (p.sender_arg_max_exists V_S x a)).2

/-! ## Joint Target Bellman with forward-looking Sender -/

noncomputable def joint_T_integrand
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  let s := p.σ_dyn V_S x a
  p.U_T x a s + p.β_T * V_T (Sanctions.clipS' (p.F x s))

noncomputable def T_T_joint
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : ℝ :=
  sSup ((fun a => p.joint_T_integrand V_T V_S x a) '' Sanctions.I)

/-! ## Forward-looking Target Bellman fixed point at a continuous Sender selector

The forward-looking analog of `BellmanT.V_T`, abstracted over the Sender
response. What separates them is the SELECTOR, not the transition:
`BellmanT.V_T` substitutes the *myopic* stage selector `σ`, whereas here
the Sender plays an arbitrary
continuous response selector `ρ : ℝ → ℝ → ℝ` (instantiated downstream at
the forward-looking dynamic argmax `σ_dyn_top`, whose joint continuity is
Berge's maximum theorem under uniqueness — `σ_dyn_continuous_of_unique`,
`BergeContinuity.lean`). The Target value `targetDynValue ρ hρc` is the
Banach fixed point of the Target Bellman operator — Rule-15 *constructed*
from primitives via `ContractingWith.fixedPoint`, valid for any monotone
`F`, no atomless noise. The β_T-contraction transports verbatim from
`BellmanT.bellmanBCF_pointwise_dist` because `ρ` does not depend on the
`V_T` argument, so the integrand difference is exactly `β_T·(V_T − W_T)`
at one point.

`hρc : Continuous (fun xa => ρ xa.1 xa.2)` is a use-site theorem-parameter,
NOT a new `Params` field (discharged from primitives via the Berge route
under argmax uniqueness). -/

/-- Target Bellman integrand at an arbitrary Sender response selector `ρ`. -/
noncomputable def targetDynIntegrand
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  p.U_T x a (ρ x a) + p.β_T * V_T (Sanctions.clipS' (p.F x (ρ x a)))

theorem targetDynIntegrand_continuous
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2)) :
    Continuous (fun xa : ℝ × ℝ => p.targetDynIntegrand ρ V_T xa.1 xa.2) := by
  unfold targetDynIntegrand
  have hU : Continuous
      (fun xa : ℝ × ℝ => p.U_T xa.1 xa.2 (ρ xa.1 xa.2)) := by
    have h_triple : Continuous
        (fun xa : ℝ × ℝ => (xa.1, xa.2, ρ xa.1 xa.2)) :=
      continuous_fst.prodMk (continuous_snd.prodMk hρc)
    exact p.U_T_continuous.comp h_triple
  have hclip : Continuous (Sanctions.clipS' : ℝ → ↥(Sanctions.S : Set ℝ)) :=
    Sanctions.clipS'_continuous
  have hF : Continuous
      (fun xa : ℝ × ℝ => p.F xa.1 (ρ xa.1 xa.2)) :=
    p.F_continuous.comp (continuous_fst.prodMk hρc)
  exact hU.add (continuous_const.mul (V_T.continuous.comp (hclip.comp hF)))

theorem targetDynIntegrand_continuous_in_a
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2)) (x : ℝ) :
    Continuous (fun a : ℝ => p.targetDynIntegrand ρ V_T x a) :=
  (p.targetDynIntegrand_continuous ρ V_T hρc).comp
    (continuous_const.prodMk continuous_id)

theorem targetDynIntegrand_image_bddAbove
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2)) (x : ℝ) :
    BddAbove ((fun a => p.targetDynIntegrand ρ V_T x a) '' Sanctions.I) :=
  (isCompact_Icc.image (p.targetDynIntegrand_continuous_in_a ρ V_T hρc x)).bddAbove

noncomputable def targetDynBellmanOn
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : ℝ :=
  sSup ((fun a => p.targetDynIntegrand ρ V_T x a) '' Sanctions.I)

theorem targetDynBellmanOn_continuous
    (ρ : ℝ → ℝ → ℝ) (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2)) :
    Continuous (fun x : ↥(Sanctions.S : Set ℝ) => p.targetDynBellmanOn ρ V_T x.val) := by
  unfold targetDynBellmanOn
  have hf : Continuous ↿(fun (x : ℝ) (a : ℝ) => p.targetDynIntegrand ρ V_T x a) :=
    p.targetDynIntegrand_continuous ρ V_T hρc
  exact (isCompact_Icc.continuous_sSup hf).comp continuous_subtype_val

/-- Forward-looking Target Bellman operator on `↥S →ᵇ ℝ` at selector `ρ`. -/
noncomputable def targetDynBCF
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => p.targetDynBellmanOn ρ V_T x.val, p.targetDynBellmanOn_continuous ρ V_T hρc⟩

@[simp] theorem targetDynBCF_apply
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)) :
    p.targetDynBCF ρ hρc V_T x = p.targetDynBellmanOn ρ V_T x.val := rfl

/-- Pointwise contraction estimate: identical to
`BellmanT.integrand_pointwise_diff`, because `ρ x a` does not depend on
the `V_T` argument. -/
theorem targetDynIntegrand_pointwise_diff
    (ρ : ℝ → ℝ → ℝ) (V_T W_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    |p.targetDynIntegrand ρ V_T x a - p.targetDynIntegrand ρ W_T x a|
      ≤ p.β_T * dist V_T W_T := by
  unfold targetDynIntegrand
  set s := ρ x a with hs
  have heq : (p.U_T x a s + p.β_T * V_T (Sanctions.clipS' (p.F x s)))
              - (p.U_T x a s + p.β_T * W_T (Sanctions.clipS' (p.F x s)))
            = p.β_T * (V_T (Sanctions.clipS' (p.F x s))
                       - W_T (Sanctions.clipS' (p.F x s))) := by ring
  rw [heq, abs_mul, abs_of_nonneg p.β_T_mem.1]
  have h_pt : dist (V_T (Sanctions.clipS' (p.F x s)))
                   (W_T (Sanctions.clipS' (p.F x s))) ≤ dist V_T W_T :=
    BoundedContinuousFunction.dist_coe_le_dist _
  rw [Real.dist_eq] at h_pt
  exact mul_le_mul_of_nonneg_left h_pt p.β_T_mem.1

theorem targetDynBCF_pointwise_dist
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (V_T W_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ↥(Sanctions.S : Set ℝ)) :
    dist (p.targetDynBCF ρ hρc V_T x) (p.targetDynBCF ρ hρc W_T x)
      ≤ p.β_T * dist V_T W_T := by
  change |p.targetDynBCF ρ hρc V_T x - p.targetDynBCF ρ hρc W_T x|
          ≤ p.β_T * dist V_T W_T
  have heq_V : p.targetDynBCF ρ hρc V_T x =
      sSup ((fun a => p.targetDynIntegrand ρ V_T x.val a) '' Sanctions.I) := rfl
  have heq_W : p.targetDynBCF ρ hρc W_T x =
      sSup ((fun a => p.targetDynIntegrand ρ W_T x.val a) '' Sanctions.I) := rfl
  rw [heq_V, heq_W]
  apply Sanctions.abs_sSup_image_sub_sSup_image_le_of_bdd
    (K := Sanctions.I) ⟨0, by simp [Sanctions.I]⟩
    (M := p.β_T * dist V_T W_T)
    (Bf := sSup ((fun a => p.targetDynIntegrand ρ V_T x.val a) '' Sanctions.I))
    (Bg := sSup ((fun a => p.targetDynIntegrand ρ W_T x.val a) '' Sanctions.I))
  · intro a _ha
    exact p.targetDynIntegrand_pointwise_diff ρ V_T W_T x.val a
  · intro a ha
    exact le_csSup (p.targetDynIntegrand_image_bddAbove ρ V_T hρc x.val) ⟨a, ha, rfl⟩
  · intro a ha
    exact le_csSup (p.targetDynIntegrand_image_bddAbove ρ W_T hρc x.val) ⟨a, ha, rfl⟩

/-- **Forward-looking single-agent Target value at a continuous Sender
selector, general transition `F`.** The Banach fixed point of the Target
Bellman operator on `↥S →ᵇ ℝ`. Rule-15 *constructed* from primitives via
`ContractingWith.fixedPoint`; valid for any monotone `F`. -/
noncomputable def targetDynValue
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2)) :
    ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  ContractingWith.fixedPoint (p.targetDynBCF ρ hρc) (by
    refine ⟨p.β_T_nnreal_lt_one, ?_⟩
    apply lipschitzWith_of_pointwise_dist_le
    intro V W x
    have h := p.targetDynBCF_pointwise_dist ρ hρc V W x
    convert h using 2)

theorem targetDynValue_isFixedPoint
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2)) :
    p.targetDynBCF ρ hρc (p.targetDynValue ρ hρc) = p.targetDynValue ρ hρc := by
  unfold targetDynValue
  exact ContractingWith.fixedPoint_isFixedPt _

/-- **Pointwise Bellman equation** for the forward-looking Target value:
`targetDynValue ρ x = sup_a [ U_T(x,a,ρ x a) + β_T · targetDynValue(F(x,ρ x a)) ]`. -/
theorem targetDynValue_bellman_eq
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (x : ↥(Sanctions.S : Set ℝ)) :
    p.targetDynValue ρ hρc x =
      sSup ((fun a => p.U_T x.val a (ρ x.val a)
              + p.β_T * p.targetDynValue ρ hρc
                  (Sanctions.clipS' (p.F x.val (ρ x.val a)))) ''
              Sanctions.I) := by
  have h := p.targetDynValue_isFixedPoint ρ hρc
  have hx : p.targetDynBCF ρ hρc (p.targetDynValue ρ hρc) x
              = p.targetDynValue ρ hρc x := by rw [h]
  rw [← hx, targetDynBCF_apply, targetDynBellmanOn]
  rfl

/-! ## The Target Bellman operator reads the selector only on feasible pairs

`targetDynBCF ρ` evaluates `ρ x a` only at a feasible state `x ∈ S` and a
feasible action `a ∈ I`. Two selectors that agree there therefore give the same
operator and the same Banach value, whatever they do off the state space. This
is what lets a selector that is continuous only on the physical states (and
extended continuously off them) stand in for a globally continuous one
(round BH-2, item BH2.10). General in `F`. -/

/-- **Congruence of the Target Bellman operator on feasible pairs.** General in
`F`. If two continuous selectors agree at every feasible state and action, the
two forward-looking Target Bellman operators are equal. No new hypothesis: this
records that the operator never looks at the selector off `S × I`. -/
theorem targetDynBCF_congr_on
    {ρ₁ ρ₂ : ℝ → ℝ → ℝ} (hρ₁ : Continuous (fun xa : ℝ × ℝ => ρ₁ xa.1 xa.2))
    (hρ₂ : Continuous (fun xa : ℝ × ℝ => ρ₂ xa.1 xa.2))
    (h : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I, ρ₁ x a = ρ₂ x a) :
    p.targetDynBCF ρ₁ hρ₁ = p.targetDynBCF ρ₂ hρ₂ := by
  funext V_T
  ext x
  simp only [targetDynBCF_apply, targetDynBellmanOn]
  congr 1
  apply Set.image_congr
  intro a ha
  simp only [targetDynIntegrand, h x.val x.property a ha]

/-- **Congruence of the forward-looking Target value on feasible pairs.**
General in `F`. Two continuous selectors that agree at every feasible state and
action have the same Banach Target value: by `targetDynBCF_congr_on` the second
value is a fixed point of the first operator, and a contraction has only one. -/
theorem targetDynValue_congr_on
    {ρ₁ ρ₂ : ℝ → ℝ → ℝ} (hρ₁ : Continuous (fun xa : ℝ × ℝ => ρ₁ xa.1 xa.2))
    (hρ₂ : Continuous (fun xa : ℝ × ℝ => ρ₂ xa.1 xa.2))
    (h : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I, ρ₁ x a = ρ₂ x a) :
    p.targetDynValue ρ₁ hρ₁ = p.targetDynValue ρ₂ hρ₂ := by
  have hcontr : ContractingWith p.β_T_nnreal (p.targetDynBCF ρ₁ hρ₁) := by
    refine ⟨p.β_T_nnreal_lt_one, ?_⟩
    apply lipschitzWith_of_pointwise_dist_le
    intro V W x
    have h := p.targetDynBCF_pointwise_dist ρ₁ hρ₁ V W x
    convert h using 2
  have h₁ : p.targetDynValue ρ₁ hρ₁ = hcontr.fixedPoint := by
    unfold targetDynValue; congr
  have hfix : Function.IsFixedPt (p.targetDynBCF ρ₁ hρ₁) (p.targetDynValue ρ₂ hρ₂) := by
    change p.targetDynBCF ρ₁ hρ₁ (p.targetDynValue ρ₂ hρ₂) = p.targetDynValue ρ₂ hρ₂
    rw [p.targetDynBCF_congr_on hρ₁ hρ₂ h]
    exact p.targetDynValue_isFixedPoint ρ₂ hρ₂
  rw [h₁]
  exact (hcontr.fixedPoint_unique hfix).symm

/-! ## State-monotonicity of the forward-looking Target value

SLP Theorem 4.7 (monotonicity preservation) applied to the
forward-looking Target Bellman operator `targetDynBCF ρ`. The Target
value `targetDynValue ρ` is non-decreasing in the political state `x`
once the per-stage *and* the continuation-state inputs are non-decreasing
in `x` at the Sender selector `ρ`. This is the `targetDynValue` analogue
of `BellmanS.V_S_monotone_of_integrand_monotone`; the structural
hypotheses are exactly the Target counterparts of `h_U_S_mono`. -/

/-- **`targetDynBCF ρ` preserves state-monotonicity.** If, for every
feasible action `a ∈ I`, the Target stage payoff at the Sender selector
`x ↦ U_T x a (ρ x a)` is non-decreasing in `x` on `S` (`h_U_T_mono`) and
the clipped continuation state `x ↦ clipS'(F x (ρ x a))` is non-decreasing
in `x` on `S` (`h_cont_mono`), then `targetDynBCF ρ` maps a
state-non-decreasing `V_T` to a state-non-decreasing image. The
continuation term inherits monotonicity from `V_T` precomposed with the
non-decreasing continuation state; `β_T ≥ 0` preserves the inequality. -/
theorem targetDynBCF_preserves_monotone
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (h_U_T_mono : ∀ a ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_T x a (ρ x a) ≤ p.U_T y a (ρ y a))
    (h_cont_mono : ∀ a ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → (Sanctions.clipS' (p.F x (ρ x a)) : ℝ)
                ≤ (Sanctions.clipS' (p.F y (ρ y a)) : ℝ))
    (V_T : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_V_mono : Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) => V_T x)) :
    Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) => p.targetDynBCF ρ hρc V_T x) := by
  intro x y h_xy
  simp only [targetDynBCF_apply, targetDynBellmanOn]
  have hβ_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have h_int_le : ∀ a ∈ Sanctions.I,
      p.targetDynIntegrand ρ V_T x.val a ≤ p.targetDynIntegrand ρ V_T y.val a := by
    intro a ha
    unfold targetDynIntegrand
    have h_U : p.U_T x.val a (ρ x.val a) ≤ p.U_T y.val a (ρ y.val a) :=
      h_U_T_mono a ha x.val x.property y.val y.property h_xy
    have hclip_le : (Sanctions.clipS' (p.F x.val (ρ x.val a)) : ℝ)
                      ≤ (Sanctions.clipS' (p.F y.val (ρ y.val a)) : ℝ) :=
      h_cont_mono a ha x.val x.property y.val y.property h_xy
    have h_V_le : V_T (Sanctions.clipS' (p.F x.val (ρ x.val a)))
                    ≤ V_T (Sanctions.clipS' (p.F y.val (ρ y.val a))) :=
      h_V_mono hclip_le
    have h_β_V_le : p.β_T * V_T (Sanctions.clipS' (p.F x.val (ρ x.val a)))
                     ≤ p.β_T * V_T (Sanctions.clipS' (p.F y.val (ρ y.val a))) :=
      mul_le_mul_of_nonneg_left h_V_le hβ_nn
    linarith
  apply csSup_le
  · exact (Set.image_nonempty.mpr ⟨0, by simp [Sanctions.I]⟩)
  · rintro _ ⟨a, ha, rfl⟩
    calc p.targetDynIntegrand ρ V_T x.val a
        ≤ p.targetDynIntegrand ρ V_T y.val a := h_int_le a ha
      _ ≤ sSup ((fun a => p.targetDynIntegrand ρ V_T y.val a) '' Sanctions.I) :=
          le_csSup (p.targetDynIntegrand_image_bddAbove ρ V_T hρc y.val) ⟨a, ha, rfl⟩

/-- **State-monotonicity of `targetDynValue ρ`.** Under the same Target
stage- and continuation-state monotonicity hypotheses, the Banach Target
value `targetDynValue ρ` is non-decreasing in the political state. SLP
Theorem 4.7 via iterate-from-`0` along the closed monotone cone — the
Target analogue of `BellmanS.V_S_monotone_of_integrand_monotone`. -/
theorem targetDynValue_monotone_of_integrand_monotone
    (ρ : ℝ → ℝ → ℝ) (hρc : Continuous (fun xa : ℝ × ℝ => ρ xa.1 xa.2))
    (h_U_T_mono : ∀ a ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_T x a (ρ x a) ≤ p.U_T y a (ρ y a))
    (h_cont_mono : ∀ a ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → (Sanctions.clipS' (p.F x (ρ x a)) : ℝ)
                ≤ (Sanctions.clipS' (p.F y (ρ y a)) : ℝ)) :
    Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) => p.targetDynValue ρ hρc x) := by
  have hcontr : ContractingWith p.β_T_nnreal (p.targetDynBCF ρ hρc) := by
    refine ⟨p.β_T_nnreal_lt_one, ?_⟩
    apply lipschitzWith_of_pointwise_dist_le
    intro V W x
    have h := p.targetDynBCF_pointwise_dist ρ hρc V W x
    convert h using 2
  have h_eq : p.targetDynValue ρ hρc = hcontr.fixedPoint := by
    unfold targetDynValue; congr
  have h_tend :
      Filter.Tendsto
        (fun n => (p.targetDynBCF ρ hρc)^[n] (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ))
        Filter.atTop (𝓝 (p.targetDynValue ρ hρc)) := by
    rw [h_eq]
    exact hcontr.tendsto_iterate_fixedPoint 0
  have h_zero_mono : Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) => (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) x) := by
    intro x y _; simp
  have h_iter_mono : ∀ n : ℕ, Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) =>
        ((p.targetDynBCF ρ hρc)^[n] (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) x) := by
    intro n
    induction n with
    | zero => simpa using h_zero_mono
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact p.targetDynBCF_preserves_monotone ρ hρc h_U_T_mono h_cont_mono _ ih
  have h_iter_basin : ∀ n : ℕ, Sanctions.StokeyLucas.MonotoneOnBasin Set.univ
      (fun x : ↥(Sanctions.S : Set ℝ) =>
        ((p.targetDynBCF ρ hρc)^[n] (0 : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)) x) := by
    intro n x y _ _ h_le
    exact h_iter_mono n h_le
  have h_closed := @Sanctions.StokeyLucas.isClosed_monotoneOnBasin
    (Sanctions.S : Set ℝ) Set.univ
  have h_fp_basin : Sanctions.StokeyLucas.MonotoneOnBasin Set.univ
      (fun x : ↥(Sanctions.S : Set ℝ) => p.targetDynValue ρ hρc x) :=
    h_closed.mem_of_tendsto h_tend (Filter.Eventually.of_forall h_iter_basin)
  intro x y h_le
  exact h_fp_basin (Set.mem_univ _) (Set.mem_univ _) h_le

/-! ## Sender max value -/

noncomputable def sender_max_value
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  sSup ((fun s' => p.U_S x a s'
    + p.β_S * V_S (Sanctions.clipS' (p.F x s'))) '' Sanctions.I)

end Params
end AbstractGame

/-! ## Joint MPE existence (Banach template — already parametric) -/

namespace AbstractGame
namespace JointMPE

/-- **Joint MPE consistency via Banach.** Parametric template:
contracting joint operator yields a fixed point. -/
theorem joint_MPE_consistency
    {γ : NNReal}
    (T_joint : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) →
              (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ))
    (hT : ContractingWith γ T_joint) :
    ∃ p : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ),
      T_joint p = p :=
  Sanctions.MPE.joint_MPE_via_Banach T_joint hT

/-! ## Joint contraction assembly from per-direction Lipschitz bounds

(Extracted from `Theory/Equilibrium/JointMPE.lean` during the
2026-05-23 AbstractGame refactor — these theorems are purely
parametric over a metric space `E` or BCF on `↥S`.) -/

theorem joint_contraction_from_row_bounds
    {E : Type*} [MetricSpace E] [CompleteSpace E] [Nonempty E]
    {T₁ T₂ : E × E → E}
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ}
    (ha₁₁_nn : 0 ≤ a₁₁) (ha₁₂_nn : 0 ≤ a₁₂)
    (ha₂₁_nn : 0 ≤ a₂₁) (ha₂₂_nn : 0 ≤ a₂₂)
    (hT₁ : ∀ V W V' W' : E,
      dist (T₁ (V, W)) (T₁ (V', W')) ≤ a₁₁ * dist V V' + a₁₂ * dist W W')
    (hT₂ : ∀ V W V' W' : E,
      dist (T₂ (V, W)) (T₂ (V', W')) ≤ a₂₁ * dist V V' + a₂₂ * dist W W')
    (hγ : max (a₁₁ + a₁₂) (a₂₁ + a₂₂) < 1) :
    ∃ p : E × E, (T₁ p, T₂ p) = p := by
  set γ : NNReal :=
    ⟨max (a₁₁ + a₁₂) (a₂₁ + a₂₂),
      le_max_of_le_left (by linarith [add_nonneg ha₁₁_nn ha₁₂_nn])⟩
  let T : E × E → E × E := fun p => (T₁ p, T₂ p)
  have hγ_lt : γ < 1 := by
    change (max (a₁₁ + a₁₂) (a₂₁ + a₂₂) : ℝ) < (1 : ℝ)
    exact hγ
  have h_pair_dist_le : ∀ (p q : E × E),
      dist p.1 q.1 ≤ dist p q ∧ dist p.2 q.2 ≤ dist p q := by
    intro p q
    rw [Prod.dist_eq]
    exact ⟨le_max_left _ _, le_max_right _ _⟩
  have _hγ_nn : 0 ≤ (γ : ℝ) := γ.coe_nonneg
  have hT₁_lip : LipschitzWith γ T₁ := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have h := hT₁ p.1 p.2 q.1 q.2
    have ⟨h1, h2⟩ := h_pair_dist_le p q
    have hcombo : a₁₁ * dist p.1 q.1 + a₁₂ * dist p.2 q.2
                    ≤ (a₁₁ + a₁₂) * dist p q := by
      calc a₁₁ * dist p.1 q.1 + a₁₂ * dist p.2 q.2
          ≤ a₁₁ * dist p q + a₁₂ * dist p q :=
              add_le_add (mul_le_mul_of_nonneg_left h1 ha₁₁_nn)
                (mul_le_mul_of_nonneg_left h2 ha₁₂_nn)
        _ = (a₁₁ + a₁₂) * dist p q := by ring
    calc dist (T₁ p) (T₁ q) ≤ a₁₁ * dist p.1 q.1 + a₁₂ * dist p.2 q.2 := h
      _ ≤ (a₁₁ + a₁₂) * dist p q := hcombo
      _ ≤ (γ : ℝ) * dist p q :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
  have hT₂_lip : LipschitzWith γ T₂ := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have h := hT₂ p.1 p.2 q.1 q.2
    have ⟨h1, h2⟩ := h_pair_dist_le p q
    have hcombo : a₂₁ * dist p.1 q.1 + a₂₂ * dist p.2 q.2
                    ≤ (a₂₁ + a₂₂) * dist p q := by
      calc a₂₁ * dist p.1 q.1 + a₂₂ * dist p.2 q.2
          ≤ a₂₁ * dist p q + a₂₂ * dist p q :=
              add_le_add (mul_le_mul_of_nonneg_left h1 ha₂₁_nn)
                (mul_le_mul_of_nonneg_left h2 ha₂₂_nn)
        _ = (a₂₁ + a₂₂) * dist p q := by ring
    calc dist (T₂ p) (T₂ q) ≤ a₂₁ * dist p.1 q.1 + a₂₂ * dist p.2 q.2 := h
      _ ≤ (a₂₁ + a₂₂) * dist p q := hcombo
      _ ≤ (γ : ℝ) * dist p q :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
  have hT_lip : LipschitzWith γ T := by
    intro p q
    rw [Prod.edist_eq]
    exact max_le (hT₁_lip p q) (hT₂_lip p q)
  have hT_contr : ContractingWith γ T := ⟨hγ_lt, hT_lip⟩
  exact ⟨ContractingWith.fixedPoint T hT_contr,
         ContractingWith.fixedPoint_isFixedPt hT_contr⟩

theorem joint_MPE_existence_from_row_bounds
    {T₁ T₂ : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) →
            (↥(Sanctions.S : Set ℝ) →ᵇ ℝ)}
    {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ}
    (ha₁₁_nn : 0 ≤ a₁₁) (ha₁₂_nn : 0 ≤ a₁₂)
    (ha₂₁_nn : 0 ≤ a₂₁) (ha₂₂_nn : 0 ≤ a₂₂)
    (hT₁ : ∀ V W V' W', dist (T₁ (V, W)) (T₁ (V', W'))
                          ≤ a₁₁ * dist V V' + a₁₂ * dist W W')
    (hT₂ : ∀ V W V' W', dist (T₂ (V, W)) (T₂ (V', W'))
                          ≤ a₂₁ * dist V V' + a₂₂ * dist W W')
    (hγ : max (a₁₁ + a₁₂) (a₂₁ + a₂₂) < 1) :
    ∃ p : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ),
      (T₁ p, T₂ p) = p :=
  joint_contraction_from_row_bounds
    ha₁₁_nn ha₁₂_nn ha₂₁_nn ha₂₂_nn hT₁ hT₂ hγ

theorem joint_MPE_under_explicit_bounds
    {T_T T_S : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) →
              (↥(Sanctions.S : Set ℝ) →ᵇ ℝ)}
    {β_S β_T L_TS L_ST : ℝ}
    (hβ_S_nn : 0 ≤ β_S) (hβ_T_nn : 0 ≤ β_T)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ V W V' W', dist (T_T (V, W)) (T_T (V', W'))
                            ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ V W V' W', dist (T_S (V, W)) (T_S (V', W'))
                            ≤ L_ST * dist V V' + β_S * dist W W')
    (hsuff_T : β_T + L_TS < 1)
    (hsuff_S : β_S + L_ST < 1) :
    ∃ p : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ),
      (T_T p, T_S p) = p :=
  joint_MPE_existence_from_row_bounds
    hβ_T_nn hL_TS_nn hL_ST_nn hβ_S_nn hT_T hT_S
    (max_lt hsuff_T (by linarith))

/-! ## Weighted row-sum criterion (loosening of `joint_MPE_under_explicit_bounds`)

The max-metric row-sum criterion `max(β_T + L_TS, β_S + L_ST) < 1`
admits the row-Lipschitz matrix `M = [β_T L_TS; L_ST β_S]` whose
2-norm `max(row-sum)` is bounded by 1. This is *sufficient* for joint
contraction but not necessary: the truly necessary condition is the
**spectral radius** `ρ(M) < 1`, which by Perron-Frobenius is equivalent
to the existence of positive weights `(c_T, c_S)` such that the
**weighted** row sums satisfy

  `c_T β_T + c_S L_TS < c_T`   AND   `c_T L_ST + c_S β_S < c_S`.

The theorem below admits this weaker criterion. The proof rescales the
Sender component by `r := c_S / c_T` and applies the existing
max-metric theorem to the rescaled operators.

**Example.** With `(β_T, L_TS, L_ST, β_S) = (0.9, 0.2, 0.05, 0.05)`,
the max-metric row sum row-T is `1.1 ≥ 1`, so
`joint_MPE_under_explicit_bounds` does not apply. With weights
`(c_T, c_S) = (1, 0.1)`, the weighted criterion gives
`1·0.9 + 0.1·0.2 = 0.92 < 1` and `1·0.05 + 0.1·0.05 = 0.055 < 0.1`,
so `joint_MPE_under_weighted_bounds` applies. -/
set_option linter.style.longLine false in
theorem joint_MPE_under_weighted_bounds
    {T_T T_S : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) →
              (↥(Sanctions.S : Set ℝ) →ᵇ ℝ)}
    {β_S β_T L_TS L_ST c_T c_S : ℝ}
    (hc_T_pos : 0 < c_T) (hc_S_pos : 0 < c_S)
    (hβ_S_nn : 0 ≤ β_S) (hβ_T_nn : 0 ≤ β_T)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ V W V' W', dist (T_T (V, W)) (T_T (V', W'))
                            ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ V W V' W', dist (T_S (V, W)) (T_S (V', W'))
                            ≤ L_ST * dist V V' + β_S * dist W W')
    (h_weighted_T : c_T * β_T + c_S * L_TS < c_T)
    (h_weighted_S : c_T * L_ST + c_S * β_S < c_S) :
    ∃ p : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ),
      (T_T p, T_S p) = p := by
  -- Rescale Sender component by r = c_S / c_T > 0.
  set r : ℝ := c_S / c_T with hr_def
  have hr_pos : 0 < r := div_pos hc_S_pos hc_T_pos
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr_inv_pos : 0 < 1 / r := one_div_pos.mpr hr_pos
  -- Define rescaled operators.
  let Tt_T : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) →
            (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :=
    fun p => T_T (p.1, r • p.2)
  let Tt_S : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) →
            (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :=
    fun p => (1 / r) • T_S (p.1, r • p.2)
  -- Row-Lipschitz for Tt_T in max metric:
  -- β_T · dist V V' + (L_TS · r) · dist W W'.
  have hTt_T : ∀ V W V' W', dist (Tt_T (V, W)) (Tt_T (V', W'))
                              ≤ β_T * dist V V' + (L_TS * r) * dist W W' := by
    intro V W V' W'
    have h := hT_T V (r • W) V' (r • W')
    have h_smul : dist (r • W) (r • W') = r * dist W W' := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr_pos]
    rw [h_smul] at h
    have : L_TS * (r * dist W W') = L_TS * r * dist W W' := by ring
    linarith
  -- Row-Lipschitz for Tt_S in max metric:
  -- (L_ST / r) · dist V V' + β_S · dist W W'.
  have hTt_S : ∀ V W V' W', dist (Tt_S (V, W)) (Tt_S (V', W'))
                              ≤ (L_ST / r) * dist V V' + β_S * dist W W' := by
    intro V W V' W'
    have h := hT_S V (r • W) V' (r • W')
    have h_smul_W : dist (r • W) (r • W') = r * dist W W' := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr_pos]
    rw [h_smul_W] at h
    -- dist (Tt_S (V,W)) (Tt_S (V',W')) = (1/r) * dist (T_S (V, r•W)) (T_S (V', r•W'))
    have h_smul_out : dist (Tt_S (V, W)) (Tt_S (V', W'))
                        = (1 / r) * dist (T_S (V, r • W)) (T_S (V', r • W')) := by
      change dist ((1/r) • T_S (V, r • W)) ((1/r) • T_S (V', r • W'))
              = (1 / r) * _
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr_inv_pos]
    rw [h_smul_out]
    have h_inv_r_nn : 0 ≤ 1 / r := le_of_lt hr_inv_pos
    have h_mul : (1 / r) * dist (T_S (V, r • W)) (T_S (V', r • W'))
                  ≤ (1 / r) * (L_ST * dist V V' + β_S * (r * dist W W')) :=
      mul_le_mul_of_nonneg_left h h_inv_r_nn
    have h_simp : (1 / r) * (L_ST * dist V V' + β_S * (r * dist W W'))
                    = (L_ST / r) * dist V V' + β_S * dist W W' := by
      field_simp
    linarith
  -- Row sums < 1: β_T + L_TS · r < 1 and L_ST/r + β_S < 1.
  have h_row_T : β_T + L_TS * r < 1 := by
    -- From c_T · β_T + c_S · L_TS < c_T: divide by c_T (positive).
    have h := h_weighted_T
    have hc_T_ne : c_T ≠ 0 := ne_of_gt hc_T_pos
    have h1 : β_T + (c_S / c_T) * L_TS < 1 := by
      have hdiv : (c_T * β_T + c_S * L_TS) / c_T < c_T / c_T :=
        div_lt_div_of_pos_right h hc_T_pos
      rw [div_self hc_T_ne] at hdiv
      have heq : (c_T * β_T + c_S * L_TS) / c_T = β_T + (c_S / c_T) * L_TS := by
        field_simp
      linarith [heq ▸ hdiv]
    change β_T + L_TS * r < 1
    have : L_TS * r = (c_S / c_T) * L_TS := by rw [hr_def]; ring
    linarith
  have h_row_S : L_ST / r + β_S < 1 := by
    -- From c_T · L_ST + c_S · β_S < c_S: divide by c_S.
    have h := h_weighted_S
    have hc_S_ne : c_S ≠ 0 := ne_of_gt hc_S_pos
    have h1 : (c_T / c_S) * L_ST + β_S < 1 := by
      have hdiv : (c_T * L_ST + c_S * β_S) / c_S < c_S / c_S :=
        div_lt_div_of_pos_right h hc_S_pos
      rw [div_self hc_S_ne] at hdiv
      have heq : (c_T * L_ST + c_S * β_S) / c_S = (c_T / c_S) * L_ST + β_S := by
        field_simp
      linarith [heq ▸ hdiv]
    change L_ST / r + β_S < 1
    have : L_ST / r = (c_T / c_S) * L_ST := by
      rw [hr_def]
      field_simp
    linarith
  -- Apply existing max-metric theorem to (Tt_T, Tt_S).
  have hL_TS_r_nn : 0 ≤ L_TS * r := mul_nonneg hL_TS_nn (le_of_lt hr_pos)
  have hL_ST_r_nn : 0 ≤ L_ST / r := div_nonneg hL_ST_nn (le_of_lt hr_pos)
  obtain ⟨q, hq⟩ :=
    joint_MPE_existence_from_row_bounds
      (T₁ := Tt_T) (T₂ := Tt_S)
      hβ_T_nn hL_TS_r_nn hL_ST_r_nn hβ_S_nn hTt_T hTt_S
      (max_lt h_row_T h_row_S)
  -- Transport: (V, W) := (q.1, r • q.2) is a fixed point of (T_T, T_S).
  refine ⟨(q.1, r • q.2), ?_⟩
  obtain ⟨hq_T, hq_S⟩ := Prod.mk.inj hq
  -- Tt_T(q) = q.1 means T_T(q.1, r • q.2) = q.1, i.e., T_T at (V, W) gives V.
  -- Tt_S(q) = q.2 means (1/r) • T_S(q.1, r • q.2) = q.2, i.e., T_S at (V, W) = r • q.2 = W.
  refine Prod.mk.injEq .. |>.mpr ⟨hq_T, ?_⟩
  have h2 : (1 / r) • T_S (q.1, r • q.2) = q.2 := hq_S
  have h_eq : T_S (q.1, r • q.2) = r • q.2 := by
    have := congr_arg (r • ·) h2
    simp only at this
    rw [smul_smul, mul_one_div, div_self hr_ne, one_smul] at this
    exact this
  exact h_eq

/-! ## Round-14 Priority 4: Schur-complement form for the row-contraction margin

The certificate's two scalar row-sum margins
`hsuff_T : β_T + L_TS < 1` and `hsuff_S : β_S + L_ST < 1` together
imply the joint-Bellman contraction. But the genuinely sharp
necessary-and-sufficient criterion for the 2×2 row-Lipschitz matrix
`M = [[β_T, L_TS]; [L_ST, β_S]]` to have spectral radius `< 1` is
the **Schur-complement** inequality
`L_TS · L_ST < (1 - β_T) · (1 - β_S)` (together with `β_T, β_S < 1`).
This is strictly weaker than the max-row-sum form and admits
asymmetric high-discount regimes the unweighted criterion excludes
(e.g. `(β_T, L_TS, β_S, L_ST) = (0.9, 0.2, 0.05, 0.05)`: max-row-sum
`1.1 ≥ 1` fails, but Schur gives `0.01 < 0.095` ✓).

The lemma below provides the closed-form Perron-vector
construction. Plus a thin wrapper
`joint_MPE_existence_from_Schur` that routes through
`joint_MPE_under_weighted_bounds` so users can supply the Schur
inequality directly without manually computing weights.

## Rule compliance
* Rule 1: structural — no strategies involved.
* Rule 3: cat-2 weakening (strictly weaker scalar inequality than
  the existing two `hsuff_T`, `hsuff_S` margins; no new fields or
  hypotheses).
* Rule 5: fully parametric over `(β_T, β_S, L_TS, L_ST)`.
* Rule 8: paraphrase above.
* Rule 9: non-vacuity witness — explicit closed-form weights
  `c_T = (1 - β_S) + L_TS` and `c_S = (1 - β_T) + L_ST` are exhibited.

## Closed-form weights
With `c_T := (1 - β_S) + L_TS`, `c_S := (1 - β_T) + L_ST`,
* `c_T · β_T + c_S · L_TS - c_T = L_TS · L_ST - (1 - β_T)(1 - β_S) < 0` by Schur,
* `c_T · L_ST + c_S · β_S - c_S = L_TS · L_ST - (1 - β_T)(1 - β_S) < 0` by Schur. -/

set_option linter.style.longLine false in
/-- **Round-14 Priority 4: Perron-vector closed-form weights from Schur margin.**
From `β_S < 1`, nonneg cross-Lipschitz `L_TS, L_ST`, and the
Schur-complement inequality `L_TS · L_ST < (1 - β_T) · (1 - β_S)`,
exhibit explicit positive weights `(c_T, c_S)` such that the
weighted row sums are strictly less than the diagonal:
`c_T · β_T + c_S · L_TS < c_T` and `c_T · L_ST + c_S · β_S < c_S`.
These are exactly the hypotheses consumed by
`joint_MPE_under_weighted_bounds`.

Explicit construction: `c_T := (1 - β_S) + L_TS` and
`c_S := (1 - β_T) + L_ST`. Both are positive (from `β_S < 1` and
`β_T < 1`), and both weighted row-sum inequalities reduce exactly
to the Schur condition.

2026-07-24 dedup: one-line wrapper of the Foundations scalar lemma
`Foundations.Perov.perronWeights_of_schur_scalars` (the single point
of truth for the 2×2 Perron-weight algebra; the pure-arithmetic proof
formerly duplicated here now lives there — Rule 19).

2026-10-06 (round BG1.1): the hypothesis `β_T < 1` was dropped. The
nonnegative cross constants, `β_S < 1` and the Schur margin already force it
(`Foundations.Perov.lt_one_of_schur_margin`), so the Target's own-discount
bound is a consequence here, not an input. F-free: pure 2×2 arithmetic. -/
theorem rowSumWeights_of_spectralRadius_lt_one
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_S_lt : β_S < 1)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S)) :
    ∃ c_T c_S : ℝ, 0 < c_T ∧ 0 < c_S ∧
      c_T * β_T + c_S * L_TS < c_T ∧
      c_T * L_ST + c_S * β_S < c_S :=
  Sanctions.Foundations.Perov.perronWeights_of_schur_scalars
    hL_TS_nn hL_ST_nn hβ_S_lt hSchur

/-- **Round-14 Priority 4: joint MPE existence from Schur margin.**
A thin wrapper around `joint_MPE_under_weighted_bounds`: given the
Schur-complement inequality `L_TS · L_ST < (1 - β_T)(1 - β_S)`
(strictly weaker than the unweighted `β_T + L_TS < 1` and
`β_S + L_ST < 1` pair), produce the joint Bellman fixed point.

Combines `rowSumWeights_of_spectralRadius_lt_one` (which exhibits
explicit positive weights from Schur) with the existing
`joint_MPE_under_weighted_bounds` route. The user supplies one
Schur inequality instead of two unweighted row-sum margins.

2026-10-06 (round BG1.1): the hypothesis `β_T < 1` was dropped together with
the same binder of `rowSumWeights_of_spectralRadius_lt_one`; it follows from
the signs, `β_S < 1` and the Schur margin. General in `F`: the two operators
are arbitrary maps on the value space. -/
theorem joint_MPE_existence_from_Schur
    {T_T T_S : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) →
              (↥(Sanctions.S : Set ℝ) →ᵇ ℝ)}
    {β_S β_T L_TS L_ST : ℝ}
    (hβ_S_nn : 0 ≤ β_S) (hβ_T_nn : 0 ≤ β_T)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hβ_S_lt : β_S < 1)
    (hT_T : ∀ V W V' W', dist (T_T (V, W)) (T_T (V', W'))
                            ≤ β_T * dist V V' + L_TS * dist W W')
    (hT_S : ∀ V W V' W', dist (T_S (V, W)) (T_S (V', W'))
                            ≤ L_ST * dist V V' + β_S * dist W W')
    (hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S)) :
    ∃ p : (↥(Sanctions.S : Set ℝ) →ᵇ ℝ) × (↥(Sanctions.S : Set ℝ) →ᵇ ℝ),
      (T_T p, T_S p) = p := by
  obtain ⟨c_T, c_S, hc_T_pos, hc_S_pos, h_weighted_T, h_weighted_S⟩ :=
    rowSumWeights_of_spectralRadius_lt_one
      hβ_S_lt hL_TS_nn hL_ST_nn hSchur
  exact joint_MPE_under_weighted_bounds
    hc_T_pos hc_S_pos hβ_S_nn hβ_T_nn hL_TS_nn hL_ST_nn
    hT_T hT_S h_weighted_T h_weighted_S

end JointMPE
end AbstractGame

end -- noncomputable section

end Sanctions
