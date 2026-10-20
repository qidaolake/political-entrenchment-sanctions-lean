/-
Sanctions/Theory/Equilibrium/JointExistenceFromPrimitives.lean

**Operator-level existence of `FeedbackStackelbergEquilibrium`.**

Existing equilibrium-existence in the project is structural in the
sense that `FeedbackStackelbergEquilibrium` is taken as a hypothesis
of downstream theorems. This file produces an actual instance from:

1. **Sender argmax uniqueness for every BCF** (`h_unique_all`). Under
   this primitive, the Berge continuity theorem
   `σ_dyn_continuous_of_unique` (`BergeContinuity`) gives joint
   `(x, a)`-continuity of the dynamic Sender selector for every
   `V_S`, hence joint continuity of the Target integrand.

2. **A continuous Target-policy selector** packaged as a
   `DynamicTargetSelector` — a function `α : Val × Val → ℝ → ℝ` with
   `(V_T, V_S)`-dependent continuity, feasibility, and Bellman
   optimality. The selector is parametric; concrete dischargers (e.g.
   via Berge for a unique leader argmax, or via the existing top
   selector under a different bridge) live elsewhere.

3. **Explicit row-Lipschitz contraction bounds** for the joint
   Target/Sender operator pair — the same bounds that
   `joint_MPE_under_explicit_bounds` already consumes.

The fixed-point pair `(V_T, V_S)` returned by the joint MPE existence
theorem is then packaged with the selector and its discharges to
produce a `FeedbackStackelbergEquilibrium`. A corollary
`exists_feedbackStackelbergTop_from_selector_row_bounds` lifts to the
top-selector equilibrium via the `toTop_of_unique` bridge.

No new fields are added to `AbstractGame.Params`. The existence
postulate is reduced to: "there is a continuous Target selector and
the joint operator pair contracts" — the irreducible operator-level
core of an equilibrium-existence proof.
-/

import Sanctions.Theory.Equilibrium.SelectionRobust
import Sanctions.Theory.Equilibrium.JointLipschitz
import Sanctions.Theory.Equilibrium.BergeContinuity

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 0. Notation -/

/-- BCF value-function type over the state space. -/
abbrev Val : Type :=
  ↥(Sanctions.S : Set ℝ) →ᵇ ℝ

/-! ## 1. Joint continuity of the Target integrand under uniqueness -/

/-- **Joint continuity of `joint_T_integrand` under Sender argmax
uniqueness.** This is the technical input needed for the Target joint
Bellman operator to land in `↥S →ᵇ ℝ`. -/
theorem joint_T_integrand_continuous_jointly_of_unique
    (V_T V_S : Val)
    (h_unique : p.DynamicArgmaxUniqueGlobal V_S) :
    Continuous
      (fun xa : ℝ × ℝ => p.joint_T_integrand V_T V_S xa.1 xa.2) := by
  unfold joint_T_integrand
  -- σ_dyn is jointly continuous under uniqueness.
  have hσ : Continuous (fun xa : ℝ × ℝ => p.σ_dyn V_S xa.1 xa.2) :=
    p.σ_dyn_continuous_of_unique V_S
      (fun x a s₁ s₂ hs₁ hs₂ h₁ h₂ => h_unique x a s₁ s₂ hs₁ hs₂ h₁ h₂)
  -- Triple (x, a, σ_dyn x a) is continuous.
  have h_triple :
      Continuous
        (fun xa : ℝ × ℝ => (xa.1, xa.2, p.σ_dyn V_S xa.1 xa.2)) :=
    continuous_fst.prodMk (continuous_snd.prodMk hσ)
  -- Stage utility part: continuous.
  have hU :
      Continuous
        (fun xa : ℝ × ℝ =>
          p.U_T xa.1 xa.2 (p.σ_dyn V_S xa.1 xa.2)) :=
    p.U_T_continuous.comp h_triple
  -- Argument of V_T after clipS': continuous in (x, σ_dyn x a) → ℝ.
  have h_F :
      Continuous
        (fun xa : ℝ × ℝ =>
          p.F xa.1 (p.σ_dyn V_S xa.1 xa.2)) :=
    p.F_continuous.comp (continuous_fst.prodMk hσ)
  -- Continuity of V_T ∘ clipS' ∘ F.
  have hV :
      Continuous
        (fun xa : ℝ × ℝ =>
          V_T (Sanctions.clipS' (p.F xa.1
            (p.σ_dyn V_S xa.1 xa.2)))) :=
    V_T.continuous.comp (Sanctions.clipS'_continuous.comp h_F)
  exact hU.add (continuous_const.mul hV)

/-! ## 2. Joint Target Bellman operator, BCF-valued -/

/-- **Joint Target Bellman operator (BCF-valued)** under Sender argmax
uniqueness for the supplied `V_S`. This is the pointwise sSup of the
joint Target integrand on the action set, restricted to `↥S`. -/
noncomputable def jointTarget_BCF
    (V_T V_S : Val)
    (h_unique : p.DynamicArgmaxUniqueGlobal V_S) : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x : ↥(Sanctions.S : Set ℝ) =>
        sSup ((fun a => p.joint_T_integrand V_T V_S x.val a)
                '' Sanctions.I),
     by
       have hI : IsCompact (Sanctions.I : Set ℝ) := isCompact_Icc
       have hcont :
           Continuous
             (fun xa : ℝ × ℝ => p.joint_T_integrand V_T V_S xa.1 xa.2) :=
         p.joint_T_integrand_continuous_jointly_of_unique V_T V_S h_unique
       have hxcont :
           Continuous (fun x : ℝ =>
             sSup ((fun a => p.joint_T_integrand V_T V_S x a)
                     '' Sanctions.I)) :=
         hI.continuous_sSup hcont
       exact hxcont.comp continuous_subtype_val⟩

/-- The defining pointwise equation for `jointTarget_BCF`. -/
theorem jointTarget_BCF_apply
    (V_T V_S : Val)
    (h_unique : p.DynamicArgmaxUniqueGlobal V_S)
    (x : ↥(Sanctions.S : Set ℝ)) :
    p.jointTarget_BCF V_T V_S h_unique x =
      sSup ((fun a => p.joint_T_integrand V_T V_S x.val a) ''
              Sanctions.I) := rfl

/-! ## 2b. State-local (Design A) joint continuity + Target BCF

State-local companions of §1–§2: they need Sender argmax uniqueness only
at physical states `x ∈ S = [0,1]`, and work on the compact subtype
`↥S × ℝ` (where continuity is genuine, not `ContinuousOn`). The single
`ContinuousOn → Continuous` step is at `σ_dyn`, via `comp_continuous`; every
higher layer reuses the global `Continuous.comp` / `IsCompact.continuous_sSup`
machinery unchanged, because `↥S` is compact and the sSup domain is the
subtype.

**Compliance-local since round BJ4.3 (2026-10-08).** The uniqueness input is
`DynamicArgmaxUniqueOnI`: uniqueness also only at physical compliance levels
`a ∈ I`. The Target integrand is then continuous on `↥S × I` only, so the
continuity statement precomposes the compliance argument with the projection
`Set.projIcc 0 1` of `ℝ` onto `[0,1]` (`σ_dyn_continuousOn_SI_of_unique_on`
supplies the `ContinuousOn → Continuous` step). The projection fixes every
point of `I`, so the image of `I`, and hence the supremum that defines
`jointTarget_BCF_on_S`, is unchanged: `jointTarget_BCF_on_S_apply` still holds
by `rfl`. -/

/-- **Subtype-joint continuity of the projected `joint_T_integrand`
(compliance-local, round BJ4.3).** General in `F`. As a function on
`↥S × ℝ`, the Target integrand with its compliance argument projected onto
`[0,1]` is continuous, under uniqueness of the Sender argmax at physical
states and physical compliance levels (`DynamicArgmaxUniqueOnI`).

Before round BJ4.3 this took `DynamicArgmaxUnique` (uniqueness at every real
compliance level) and concluded continuity of the unprojected integrand on
`↥S × ℝ`. The all-real-`a` uniqueness is dropped; the conclusion is read
through the projection, which is the identity on the Target's choice set `I`.
The `a ∈ I` slice is `joint_T_integrand_continuousOn_I_of_unique_on`. -/
theorem joint_T_integrand_subtype_continuous_of_unique_on
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S) :
    Continuous (fun (xa : ↥(Sanctions.S : Set ℝ) × ℝ) =>
      p.joint_T_integrand V_T V_S xa.1.val
        (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)) := by
  unfold joint_T_integrand
  -- The state and the projected compliance level, as a point of `S ×ˢ I`.
  have hmap : Continuous (fun (xa : ↥(Sanctions.S : Set ℝ) × ℝ) =>
      ((xa.1.val, (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)) : ℝ × ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  have hmaps : ∀ xa : ↥(Sanctions.S : Set ℝ) × ℝ,
      ((xa.1.val, (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)) : ℝ × ℝ) ∈
        Sanctions.S ×ˢ Sanctions.I :=
    fun xa => ⟨xa.1.property, (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2).property⟩
  -- σ_dyn continuous along that map: the only ContinuousOn→Continuous step.
  have hσ : Continuous (fun (xa : ↥(Sanctions.S : Set ℝ) × ℝ) =>
      p.σ_dyn V_S xa.1.val (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)) :=
    (p.σ_dyn_continuousOn_SI_of_unique_on V_S h_unique_on).comp_continuous
      hmap hmaps
  have h_triple : Continuous (fun (xa : ↥(Sanctions.S : Set ℝ) × ℝ) =>
      (xa.1.val, (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ),
        p.σ_dyn V_S xa.1.val (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)).prodMk hσ)
  have hU : Continuous (fun (xa : ↥(Sanctions.S : Set ℝ) × ℝ) =>
      p.U_T xa.1.val (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)
        (p.σ_dyn V_S xa.1.val (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ))) :=
    p.U_T_continuous.comp h_triple
  have h_F : Continuous (fun (xa : ↥(Sanctions.S : Set ℝ) × ℝ) =>
      p.F xa.1.val
        (p.σ_dyn V_S xa.1.val (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ))) :=
    p.F_continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk hσ)
  have hV : Continuous (fun (xa : ↥(Sanctions.S : Set ℝ) × ℝ) =>
      V_T (Sanctions.clipS' (p.F xa.1.val
        (p.σ_dyn V_S xa.1.val (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ))))) :=
    V_T.continuous.comp (Sanctions.clipS'_continuous.comp h_F)
  exact hU.add (continuous_const.mul hV)

/-- **The Target integrand is continuous in compliance on `I` (round BJ4.3,
2026-10-08).** General in `F`. At a physical state `x ∈ S`, the joint Target
integrand is continuous in the compliance level on the choice set `I`, under
compliance-local Sender uniqueness. This is the slice of
`joint_T_integrand_subtype_continuous_of_unique_on` at `x`; on `I` the
projection is the identity. It is what the existence of a Target maximiser and
the boundedness of the integrand's image of `I` need. -/
theorem joint_T_integrand_continuousOn_I_of_unique_on
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    ContinuousOn (fun a => p.joint_T_integrand V_T V_S x a) Sanctions.I := by
  have hcont : Continuous (fun a : ℝ =>
      p.joint_T_integrand V_T V_S x (Set.projIcc (0 : ℝ) 1 zero_le_one a : ℝ)) :=
    (p.joint_T_integrand_subtype_continuous_of_unique_on V_T V_S h_unique_on).comp
      ((continuous_const (y := (⟨x, hx⟩ : ↥(Sanctions.S : Set ℝ)))).prodMk
        continuous_id)
  refine hcont.continuousOn.congr ?_
  intro a ha
  simp only [Set.projIcc_of_mem zero_le_one ha]

/-- **Joint Target Bellman operator (state-local).** Same BCF as
`jointTarget_BCF`, but built from uniqueness only at physical states
`x ∈ S`. The BCF continuity comes from `IsCompact.continuous_sSup` on
the subtype `↥S`.

Since round BJ4.3 (2026-10-08) the uniqueness input is the compliance-local
`DynamicArgmaxUniqueOnI` (formerly `DynamicArgmaxUnique`, uniqueness at every
real compliance level). The value is unchanged: the supremum is still taken of
the unprojected integrand over `I`, and continuity is transported from the
projected integrand, which has the same image of `I`. General in `F`. -/
noncomputable def jointTarget_BCF_on_S
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S) : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x : ↥(Sanctions.S : Set ℝ) =>
        sSup ((fun a => p.joint_T_integrand V_T V_S x.val a)
                '' Sanctions.I),
     by
       have hI : IsCompact (Sanctions.I : Set ℝ) := isCompact_Icc
       have hproj := hI.continuous_sSup
         (f := fun (x : ↥(Sanctions.S : Set ℝ)) (a : ℝ) =>
           p.joint_T_integrand V_T V_S x.val
             (Set.projIcc (0 : ℝ) 1 zero_le_one a : ℝ))
         (p.joint_T_integrand_subtype_continuous_of_unique_on V_T V_S h_unique_on)
       refine hproj.congr (fun x => congrArg sSup (Set.image_congr fun a ha => ?_))
       simp only [Set.projIcc_of_mem zero_le_one ha]⟩

/-- The defining pointwise equation for `jointTarget_BCF_on_S`. -/
theorem jointTarget_BCF_on_S_apply
    (V_T V_S : Val)
    (h_unique_on : p.DynamicArgmaxUniqueOnI V_S)
    (x : ↥(Sanctions.S : Set ℝ)) :
    p.jointTarget_BCF_on_S V_T V_S h_unique_on x =
      sSup ((fun a => p.joint_T_integrand V_T V_S x.val a) ''
              Sanctions.I) := rfl

/-! ## 3. Dynamic Target selector packaging -/

/-- **Dynamic Target selector.** A continuous, feasible, Bellman-
optimal Target-policy assignment depending on the current value pair
`(V_T, V_S)`. The continuity field is what enables `bellmanS_BCF`
construction at every iterate; the feasibility field is what
`FeedbackStackelbergEquilibrium.α_mem` consumes; the optimality field
is what `α_opt` consumes.

This is the irreducible structural primitive an equilibrium-existence
proof requires above and beyond the joint contraction bounds — the
"leader sub-game has a continuous best-response" hypothesis. -/
structure DynamicTargetSelector where
  /-- Selector function: from a value pair to a Target policy. -/
  α : Val × Val → ℝ → ℝ
  /-- Continuity of the selector at each value pair. -/
  α_continuous : ∀ z : Val × Val, Continuous (α z)
  /-- Feasibility of the selector. -/
  α_mem : ∀ z : Val × Val, ∀ x : ℝ, α z x ∈ Sanctions.I
  /-- Bellman optimality of the selector against the joint Target
  integrand (using the ordinary `σ_dyn` Sender selector). -/
  α_opt : ∀ z : Val × Val, ∀ x : ℝ,
    IsMaxOn
      (fun a => p.joint_T_integrand z.1 z.2 x a)
      Sanctions.I
      (α z x)

/-! ## 4. Joint operators on the BCF² space -/

/-- **Joint Target operator** on `Val × Val`, parameterized by global
Sender argmax uniqueness. -/
noncomputable def jointTargetOp
    (h_unique_all : ∀ V_S : Val, p.DynamicArgmaxUniqueGlobal V_S)
    (z : Val × Val) : Val :=
  p.jointTarget_BCF z.1 z.2 (h_unique_all z.2)

/-- **Joint Sender operator** on `Val × Val`, parameterized by the
Target selector. -/
noncomputable def jointSenderOp
    (D : p.DynamicTargetSelector)
    (z : Val × Val) : Val :=
  p.bellmanS_BCF (D.α z) (D.α_continuous z) z.2

/-! ## 5. Operator-level existence theorem -/

/-- **Existence of `FeedbackStackelbergEquilibrium` from the joint
operator-level inputs.** Under:

* global Sender argmax uniqueness `h_unique_all`,
* a `DynamicTargetSelector` `D` (continuous, feasible,
  Bellman-optimal Target policy at every value pair),
* explicit row-Lipschitz contraction bounds on the joint Target and
  Sender operators with `β_T + L_TS < 1` and `β_S + L_ST < 1`,

there exists a feedback Stackelberg equilibrium. This is the
operator-level core of equilibrium existence: it leaves the
*derivation* of the row-Lipschitz bounds from primitives (which would
go through `JointLipschitz`-style theorems with primitive payoff
Lipschitz constants) as a separate, downstream item. -/
theorem exists_feedbackStackelberg_from_selector_row_bounds
    (D : p.DynamicTargetSelector)
    (h_unique_all : ∀ V_S : Val, p.DynamicArgmaxUniqueGlobal V_S)
    {βS βT LTS LST : ℝ}
    (hβS_nn : 0 ≤ βS)
    (hβT_nn : 0 ≤ βT)
    (hLTS_nn : 0 ≤ LTS)
    (hLST_nn : 0 ≤ LST)
    (hT_row :
      ∀ V W V' W' : Val,
        dist
          (p.jointTargetOp h_unique_all (V, W))
          (p.jointTargetOp h_unique_all (V', W'))
          ≤ βT * dist V V' + LTS * dist W W')
    (hS_row :
      ∀ V W V' W' : Val,
        dist
          (p.jointSenderOp D (V, W))
          (p.jointSenderOp D (V', W'))
          ≤ LST * dist V V' + βS * dist W W')
    (hT_sum : βT + LTS < 1)
    (hS_sum : βS + LST < 1) :
    Nonempty p.FeedbackStackelbergEquilibrium := by
  -- Invoke the joint MPE existence theorem on the operator pair.
  obtain ⟨z, hz⟩ :=
    Sanctions.AbstractGame.JointMPE.joint_MPE_under_explicit_bounds
      (T_T := p.jointTargetOp h_unique_all)
      (T_S := p.jointSenderOp D)
      hβS_nn hβT_nn hLTS_nn hLST_nn
      hT_row hS_row hT_sum hS_sum
  -- hz : (jointTargetOp h_unique_all z, jointSenderOp D z) = z
  -- so z.1 = jointTargetOp h_unique_all z and z.2 = jointSenderOp D z.
  have hz_T : p.jointTargetOp h_unique_all z = z.1 := by
    have h := congrArg Prod.fst hz
    simpa using h
  have hz_S : p.jointSenderOp D z = z.2 := by
    have h := congrArg Prod.snd hz
    simpa using h
  -- Package as a FeedbackStackelbergEquilibrium.
  refine ⟨{
    V_T := z.1
    V_S := z.2
    α := D.α z
    hα := D.α_continuous z
    α_mem := D.α_mem z
    V_S_fix := ?_
    V_T_fix := ?_
    α_opt := D.α_opt z
  }⟩
  · -- V_S = bellmanS_BCF (D.α z) (D.α_continuous z) z.2
    -- This is jointSenderOp D z = z.2.
    have : p.jointSenderOp D z = p.bellmanS_BCF (D.α z) (D.α_continuous z) z.2 := rfl
    rw [← this]; exact hz_S.symm
  · -- ∀ x : ↥S, V_T x = sSup (joint_T_integrand V_T V_S x.val · '' I)
    intro x
    -- V_T = z.1 = jointTargetOp h_unique_all z = jointTarget_BCF z.1 z.2 (h_unique_all z.2)
    -- At x, this equals sSup ((fun a => joint_T_integrand z.1 z.2 x.val a) '' I).
    have h_op : p.jointTargetOp h_unique_all z = p.jointTarget_BCF z.1 z.2 (h_unique_all z.2) := rfl
    have h_apply :
        (p.jointTarget_BCF z.1 z.2 (h_unique_all z.2)) x =
          sSup ((fun a => p.joint_T_integrand z.1 z.2 x.val a) ''
                  Sanctions.I) :=
      p.jointTarget_BCF_apply z.1 z.2 (h_unique_all z.2) x
    calc z.1 x
        = (p.jointTargetOp h_unique_all z) x := by rw [hz_T]
      _ = (p.jointTarget_BCF z.1 z.2 (h_unique_all z.2)) x := by rw [h_op]
      _ = sSup ((fun a => p.joint_T_integrand z.1 z.2 x.val a) ''
                  Sanctions.I) := h_apply

/-- **Existence of `FeedbackStackelbergEquilibriumTop` from the joint
operator-level inputs.** Composition of
`exists_feedbackStackelberg_from_selector_row_bounds` with the
`toTop_of_unique` bridge: the same operator-level inputs produce both
the ordinary and the top-selector equilibrium under global Sender
argmax uniqueness. -/
theorem exists_feedbackStackelbergTop_from_selector_row_bounds
    (D : p.DynamicTargetSelector)
    (h_unique_all : ∀ V_S : Val, p.DynamicArgmaxUniqueGlobal V_S)
    {βS βT LTS LST : ℝ}
    (hβS_nn : 0 ≤ βS)
    (hβT_nn : 0 ≤ βT)
    (hLTS_nn : 0 ≤ LTS)
    (hLST_nn : 0 ≤ LST)
    (hT_row :
      ∀ V W V' W' : Val,
        dist
          (p.jointTargetOp h_unique_all (V, W))
          (p.jointTargetOp h_unique_all (V', W'))
          ≤ βT * dist V V' + LTS * dist W W')
    (hS_row :
      ∀ V W V' W' : Val,
        dist
          (p.jointSenderOp D (V, W))
          (p.jointSenderOp D (V', W'))
          ≤ LST * dist V V' + βS * dist W W')
    (hT_sum : βT + LTS < 1)
    (hS_sum : βS + LST < 1) :
    Nonempty p.FeedbackStackelbergEquilibriumTop := by
  obtain ⟨E⟩ :=
    p.exists_feedbackStackelberg_from_selector_row_bounds
      D h_unique_all hβS_nn hβT_nn hLTS_nn hLST_nn
      hT_row hS_row hT_sum hS_sum
  exact ⟨FeedbackStackelbergEquilibrium.toTop_of_unique E
    (p.dynamicArgmaxUnique_of_global (h_unique_all E.V_S))⟩

end Params
end AbstractGame

end

end Sanctions
