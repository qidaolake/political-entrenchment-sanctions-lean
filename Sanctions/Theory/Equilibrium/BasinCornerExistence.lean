/-
Sanctions/Theory/Equilibrium/BasinCornerExistence.lean

**Basin-corner construction of a feedback-Stackelberg equilibrium for a
general transition `F`.**

This module closes the *value-existence* half of the general-`F`
existence question (the open crux after Phase 3). It is the basin-local
route: on the high political basin the Target plays the saturated corner
policy `α ≡ 0`, which severs the strategic-substitute channel that makes
the joint value operator non-isotone (`T_S` antitone in `V_T`). With the
leader pinned, the game decouples into a single-agent Target MDP whose
value is an unconditional Banach fixed point — `targetDynValue` in
`JointMPE.lean`, *constructed* from primitives for **any monotone `F`**
(Rule 15), no atomless noise.

What is delivered:

* `V_T_dyn` — the forward-looking, general-`F` single-agent Target value
  function at the canonical greatest Sender selector `σ_dyn_top`
  (`= targetDynValue (σ_dyn_top V_S)`), with its Bellman equation in the
  `joint_T_top_integrand` shape the equilibrium structure consumes.
* `σ_dyn_top_continuous_of_unique` — joint `(x,a)`-continuity of the
  greatest dynamic Sender selector under uniqueness of the dynamic
  argmax (Berge's maximum theorem + `σ_dyn = σ_dyn_top` under
  uniqueness). Discharges the use-site continuity hypothesis from
  primitives.
* `feedbackStackelbergTop_of_constant_corner_optimal` and its `α ≡ 0`
  specialization `feedbackStackelbergTop_of_corner_optimal` — the
  **honestly-named conditional** equilibrium: given that the constant
  corner policy attains the Target's dynamic argmax (`h_corner`), there
  is a genuine `FeedbackStackelbergEquilibriumTop` at that corner. Per
  Rule 15 the equilibrium is named *conditional on* corner-optimality;
  the only *constructed* object is the single-agent value fixed point.
* `V_T_dyn_on` and `feedbackStackelbergTop_corner_of_substituted_stage_le`
  (round BH-2, item BH2.10) — the same construction when the greatest Sender
  selector is continuous only on the feasible states `↥S × ℝ`, and the corner
  equilibrium under weak conditions: a weak substituted-stage decrease, a
  comparison of the Sender's response with its full-defiance value only, and
  that state-local continuity. The strict theorem
  `feedbackStackelbergTop_corner_of_substituted_stage_strictDecr` is now its
  corollary. General in `F`.

**Rule-1 compliance.** `V_S`, `V_T_dyn` are Banach Bellman fixed points;
`σ_dyn_top` is the forward-looking Sender argmax (greatest selector,
Milgrom-Roberts 1990); the corner policy is *certified optimal* via
`h_corner` (discharged from the `Tipping.optimizer_at_zero_*` engine at a
witness), never asserted constant.

**Rule-3 compliance.** No new `Params` field. `hσc` (continuity of
`σ_dyn_top V_S`) and `h_corner` (corner-optimality) are use-site
theorem-parameters — the former discharged via Berge under uniqueness,
the latter via the strict-concavity / FD-wedge engine at a witness. This
matches the existing `BergeContinuity.lean` Rule-3 posture.

**Rule-15 compliance.** The single-agent value `V_T_dyn` terminates in a
`def` applying the in-repo `ContractingWith.fixedPoint` to an operator
built from `Params` primitives. The equilibrium is *conditional on
existence* in its name (`_of_corner_optimal`) and docstring; the joint
unconditional general-`F` existence remains literature-grounded
(He-Sun purification; see `JointMPE.lean` docstring).
-/

import Sanctions.Theory.Basin.JointPreferenceBasin
import Sanctions.Theory.Equilibrium.BergeContinuity
import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Theory.Basin.Tipping

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Continuity of the greatest dynamic Sender selector under uniqueness -/

/-- **Joint continuity of `σ_dyn_top V_S`** under uniqueness of the
dynamic argmax. Combines `σ_dyn_eq_σ_dyn_top_of_unique` (the greatest
selector coincides with the `Classical.choose` selector when the argmax
is a singleton) with `σ_dyn_continuous_of_unique` (Berge's maximum
theorem for the latter). This discharges the `hσc` hypothesis of
`V_T_dyn` from primitives at any `V_S` with a unique dynamic argmax
(canonical sufficient condition: strict concavity of `U_S` in `s`). -/
theorem σ_dyn_top_continuous_of_unique
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_unique : ∀ x a s₁ s₂, s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₁ →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₂ → s₁ = s₂) :
    Continuous (fun xa : ℝ × ℝ => p.σ_dyn_top V_S xa.1 xa.2) := by
  have h_eq : (fun xa : ℝ × ℝ => p.σ_dyn_top V_S xa.1 xa.2)
            = (fun xa : ℝ × ℝ => p.σ_dyn V_S xa.1 xa.2) := by
    funext xa
    exact (p.σ_dyn_eq_σ_dyn_top_of_unique V_S xa.1 xa.2 (h_unique xa.1 xa.2)).symm
  rw [h_eq]
  exact p.σ_dyn_continuous_of_unique V_S h_unique

/-- **State-local joint continuity of `σ_dyn_top V_S`.**  This is the
physical-state companion of `σ_dyn_top_continuous_of_unique`: uniqueness is
required only for `x ∈ S`, and the conclusion is genuine continuity on the
subtype `↥S × ℝ`.  It combines the state-local Berge theorem for
`Classical.choose`'s `σ_dyn` with selector equality under uniqueness.

This is the appropriate interface for clipped interior-argmax economies:
off-state clip kinks can destroy global uniqueness even though the Bellman
operator only evaluates physical states. -/
theorem σ_dyn_top_continuous_subtype_of_unique_on
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_unique : ∀ x ∈ Sanctions.S, ∀ a s₁ s₂,
        s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₁ →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₂ → s₁ = s₂) :
    Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      p.σ_dyn_top V_S xa.1.val xa.2) := by
  have h_eq : (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
        p.σ_dyn_top V_S xa.1.val xa.2)
      = (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
        p.σ_dyn V_S xa.1.val xa.2) := by
    funext xa
    exact (p.σ_dyn_eq_σ_dyn_top_of_unique V_S xa.1.val xa.2
      (h_unique xa.1.val xa.1.property xa.2)).symm
  rw [h_eq]
  have hmap : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      ((xa.1.val, xa.2) : ℝ × ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hmaps : ∀ xa : ↥(Sanctions.S : Set ℝ) × ℝ,
      ((xa.1.val, xa.2) : ℝ × ℝ) ∈
        Sanctions.S ×ˢ (Set.univ : Set ℝ) :=
    fun xa => ⟨xa.1.property, Set.mem_univ _⟩
  exact (p.σ_dyn_continuousOn_S_of_unique_on V_S h_unique).comp_continuous
    hmap hmaps

/-- **Compliance-local joint continuity of `σ_dyn_top V_S` (round BJ4.3,
2026-10-08).** General in `F`. Compliance-local sibling of
`σ_dyn_top_continuous_subtype_of_unique_on`: uniqueness of the dynamic Sender
argmax is required only at physical states `x ∈ S` *and physical compliance
levels `a ∈ I`* (the form `DynamicArgmaxUniqueOnI` of `SelectionRobust`), and
the conclusion is continuity on `↥S × ℝ` of the greatest selector with its
compliance argument projected onto `[0,1]` by `Set.projIcc`. On `↥S × I` the
projection is the identity, so this is continuity of `σ_dyn_top V_S` on the
physical states and compliance levels. The all-`a` form above keeps its
`DynamicArgmaxUnique` hypothesis: its conclusion reads the selector at every
real compliance level, which compliance-local uniqueness does not control. -/
theorem σ_dyn_top_continuous_subtype_SI_of_unique_on
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_unique : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I, ∀ s₁ s₂,
        s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₁ →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₂ → s₁ = s₂) :
    Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      p.σ_dyn_top V_S xa.1.val (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)) := by
  have h_eq : (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
        p.σ_dyn_top V_S xa.1.val (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ))
      = (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
        p.σ_dyn V_S xa.1.val (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)) := by
    funext xa
    exact (p.σ_dyn_eq_σ_dyn_top_of_unique V_S xa.1.val _
      (h_unique xa.1.val xa.1.property _
        (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2).property)).symm
  rw [h_eq]
  have hmap : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      ((xa.1.val, (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)) : ℝ × ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  have hmaps : ∀ xa : ↥(Sanctions.S : Set ℝ) × ℝ,
      ((xa.1.val, (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2 : ℝ)) : ℝ × ℝ) ∈
        Sanctions.S ×ˢ Sanctions.I :=
    fun xa => ⟨xa.1.property, (Set.projIcc (0 : ℝ) 1 zero_le_one xa.2).property⟩
  exact (p.σ_dyn_continuousOn_SI_of_unique_on V_S h_unique).comp_continuous
    hmap hmaps

/-- **Continuous whole-line extension of a physical-state Sender selector.**
The state is first clipped into `S`, then the genuine dynamic greatest argmax is
evaluated there. This extension is used only to satisfy generic Target-Bellman
interfaces that are stated on `ℝ`; on every physical state it is exactly the
original equilibrium-derived selector. -/
noncomputable def σ_dyn_top_clamped
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  p.σ_dyn_top V_S (Sanctions.clipS' x).val a

/-- The clipped extension is jointly continuous whenever the original dynamic
greatest selector is jointly continuous on the physical state subtype. -/
theorem σ_dyn_top_clamped_continuous
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσc : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      p.σ_dyn_top V_S xa.1.val xa.2)) :
    Continuous (fun xa : ℝ × ℝ => p.σ_dyn_top_clamped V_S xa.1 xa.2) := by
  have hmap : Continuous (fun xa : ℝ × ℝ =>
      ((Sanctions.clipS' xa.1, xa.2) : ↥(Sanctions.S : Set ℝ) × ℝ)) :=
    (Sanctions.clipS'_continuous.comp continuous_fst).prodMk continuous_snd
  simpa only [σ_dyn_top_clamped, Function.comp_apply] using hσc.comp hmap

/-- On the physical state interval, the clipped extension is definitionally the
same dynamic greatest argmax as the model's original Sender selector. -/
theorem σ_dyn_top_clamped_eq_of_mem
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x a : ℝ} (hx : x ∈ Sanctions.S) :
    p.σ_dyn_top_clamped V_S x a = p.σ_dyn_top V_S x a := by
  unfold σ_dyn_top_clamped
  rw [Sanctions.clipS'_val_eq_of_mem hx]

/-! ## Forward-looking single-agent Target value at the greatest selector -/

/-- **Forward-looking single-agent Target value at the canonical greatest
Sender selector, general transition `F`.** The Banach fixed point of the
Target Bellman operator with the Sender playing `σ_dyn_top V_S`. This is
the value function the top feedback-Stackelberg equilibrium consumes.
Rule-15 *constructed* (via `targetDynValue` / `ContractingWith.fixedPoint`),
valid for any monotone `F`. -/
noncomputable def V_T_dyn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσc : Continuous (fun xa : ℝ × ℝ => p.σ_dyn_top V_S xa.1 xa.2)) :
    ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  p.targetDynValue (p.σ_dyn_top V_S) hσc

/-- **Bellman equation for `V_T_dyn`** in the `joint_T_top_integrand`
shape required by `FeedbackStackelbergEquilibriumTop.V_T_fix_top`. -/
theorem V_T_dyn_bellman_eq
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσc : Continuous (fun xa : ℝ × ℝ => p.σ_dyn_top V_S xa.1 xa.2))
    (x : ↥(Sanctions.S : Set ℝ)) :
    p.V_T_dyn V_S hσc x =
      sSup ((fun a => p.joint_T_top_integrand (p.V_T_dyn V_S hσc) V_S x.val a)
              '' Sanctions.I) := by
  simp only [joint_T_top_integrand, V_T_dyn]
  exact p.targetDynValue_bellman_eq (p.σ_dyn_top V_S) hσc x

/-! ## The same Target value from continuity on the feasible states only -/

/-- **Forward-looking Target value from state-local selector continuity.**
General in `F`. `V_T_dyn` needs the greatest Sender selector `σ_dyn_top V_S`
to be jointly continuous on all of `ℝ × ℝ`. This constructor needs it only on
the feasible states `↥S × ℝ`: it feeds the Target Bellman constructor
`targetDynValue` the clipped extension `σ_dyn_top_clamped`, which equals
`σ_dyn_top V_S` at every feasible state (round BH-2, item BH2.10). Dropped:
continuity of the selector off the state space, which the Target Bellman
operator never reads (`targetDynBCF_congr_on`). -/
noncomputable def V_T_dyn_on
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσc : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      p.σ_dyn_top V_S xa.1.val xa.2)) :
    ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  p.targetDynValue (p.σ_dyn_top_clamped V_S) (p.σ_dyn_top_clamped_continuous V_S hσc)

/-- **Bellman equation for `V_T_dyn_on`** in the `joint_T_top_integrand` shape
required by `FeedbackStackelbergEquilibriumTop.V_T_fix_top`. General in `F`.
The clipped selector and the original greatest selector agree at every
feasible state, so this is the original Target Bellman equation against
`σ_dyn_top V_S`. -/
theorem V_T_dyn_on_bellman_eq
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσc : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      p.σ_dyn_top V_S xa.1.val xa.2))
    (x : ↥(Sanctions.S : Set ℝ)) :
    p.V_T_dyn_on V_S hσc x =
      sSup ((fun a => p.joint_T_top_integrand (p.V_T_dyn_on V_S hσc) V_S x.val a)
              '' Sanctions.I) := by
  have h := p.targetDynValue_bellman_eq (p.σ_dyn_top_clamped V_S)
    (p.σ_dyn_top_clamped_continuous V_S hσc) x
  simpa only [V_T_dyn_on, joint_T_top_integrand,
    p.σ_dyn_top_clamped_eq_of_mem V_S x.property] using h

/-- **`V_T_dyn_on` is `V_T_dyn` whenever the latter exists.** General in `F`.
If the greatest selector is also continuous on all of `ℝ × ℝ`, the state-local
Target value equals the original one, because the two selectors agree on
`S × I` (`targetDynValue_congr_on`). Any statement about `V_T_dyn` therefore
transfers to `V_T_dyn_on`. -/
theorem V_T_dyn_on_eq_V_T_dyn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσc_on : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      p.σ_dyn_top V_S xa.1.val xa.2))
    (hσc : Continuous (fun xa : ℝ × ℝ => p.σ_dyn_top V_S xa.1 xa.2)) :
    p.V_T_dyn_on V_S hσc_on = p.V_T_dyn V_S hσc := by
  unfold V_T_dyn_on V_T_dyn
  exact p.targetDynValue_congr_on _ _
    (fun _ hx _ _ => p.σ_dyn_top_clamped_eq_of_mem V_S hx)

/-! ## Conditional feedback-Stackelberg equilibrium at a constant corner -/

/-- **Conditional equilibrium at a constant corner policy.** Given a
constant Target policy `α ≡ c` with `c ∈ I`, the Sender value `V_S` taken
as the Sender Bellman fixed point against `α ≡ c`, continuity of the
greatest Sender selector at that `V_S` (`hσc`), and the certificate
`h_corner` that `c` attains the Target's dynamic argmax at every feasible
state, there is a genuine `FeedbackStackelbergEquilibriumTop` whose leader
policy is `α ≡ c`.

The only *constructed* object is the single-agent value fixed point
`V_T_dyn`; `h_corner` (the leader's corner-optimality, which the
deterministic-kernel cycling actually threatens) is *consumed
conditionally* and named accordingly (Rule 15). -/
theorem feedbackStackelbergTop_of_constant_corner_optimal
    (c : ℝ) (hc : c ∈ Sanctions.I)
    (hσc : Continuous (fun xa : ℝ × ℝ =>
      p.σ_dyn_top (p.V_S (fun _ => c) continuous_const) xa.1 xa.2))
    (h_corner : ∀ x ∈ Sanctions.S,
      IsMaxOn (fun a => p.joint_T_top_integrand
        (p.V_T_dyn (p.V_S (fun _ => c) continuous_const) hσc)
        (p.V_S (fun _ => c) continuous_const) x a) Sanctions.I c) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop, E.α = (fun _ => c) :=
  ⟨{ V_T := p.V_T_dyn (p.V_S (fun _ => c) continuous_const) hσc
     V_S := p.V_S (fun _ => c) continuous_const
     α := fun _ => c
     hα := continuous_const
     α_mem := fun _ _ => hc
     V_S_fix := (p.V_S_isFixedPoint continuous_const).symm
     V_T_fix_top := fun x =>
       p.V_T_dyn_bellman_eq (p.V_S (fun _ => c) continuous_const) hσc x
     α_opt_top := h_corner }, rfl⟩

/-- **Conditional equilibrium at the saturated corner `α ≡ 0`.** The
`c = 0` specialization of `feedbackStackelbergTop_of_constant_corner_optimal`
— the canonical basin corner. -/
theorem feedbackStackelbergTop_of_corner_optimal
    (hσc : Continuous (fun xa : ℝ × ℝ =>
      p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) xa.1 xa.2))
    (h_corner : ∀ x ∈ Sanctions.S,
      IsMaxOn (fun a => p.joint_T_top_integrand
        (p.V_T_dyn (p.V_S (fun _ => 0) continuous_const) hσc)
        (p.V_S (fun _ => 0) continuous_const) x a) Sanctions.I 0) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop, E.α = (fun _ => 0) :=
  p.feedbackStackelbergTop_of_constant_corner_optimal 0
    (by simp [Sanctions.I]) hσc h_corner

/-- **Conditional equilibrium at a constant corner, state-local selector
continuity.** General in `F`. `feedbackStackelbergTop_of_constant_corner_optimal`
with the continuity of the greatest Sender selector asked only on the feasible
states `↥S × ℝ`, and the Target value built by `V_T_dyn_on`. Dropped:
continuity of the selector off the state space (round BH-2, item BH2.10). -/
theorem feedbackStackelbergTop_of_constant_corner_optimal_on
    (c : ℝ) (hc : c ∈ Sanctions.I)
    (hσc : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      p.σ_dyn_top (p.V_S (fun _ => c) continuous_const) xa.1.val xa.2))
    (h_corner : ∀ x ∈ Sanctions.S,
      IsMaxOn (fun a => p.joint_T_top_integrand
        (p.V_T_dyn_on (p.V_S (fun _ => c) continuous_const) hσc)
        (p.V_S (fun _ => c) continuous_const) x a) Sanctions.I c) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop, E.α = (fun _ => c) :=
  ⟨{ V_T := p.V_T_dyn_on (p.V_S (fun _ => c) continuous_const) hσc
     V_S := p.V_S (fun _ => c) continuous_const
     α := fun _ => c
     hα := continuous_const
     α_mem := fun _ _ => hc
     V_S_fix := (p.V_S_isFixedPoint continuous_const).symm
     V_T_fix_top := fun x =>
       p.V_T_dyn_on_bellman_eq (p.V_S (fun _ => c) continuous_const) hσc x
     α_opt_top := h_corner }, rfl⟩

/-! ## Parametric corner dischargers (witness-independent)

Two reusable lemmas that discharge the `hσc` and `h_corner` hypotheses
from primitive monotonicity / `a`-independence conditions, so any witness
satisfying them obtains a corner equilibrium in one line. -/

/-- **`σ_dyn_top (V_S ≡ 0-policy) ≡ 1`** whenever the corner Sender value
is monotone and the Sender stage payoff is maximized at the top sanction
`s = 1`. The dynamic Sender objective `U_S(x,a,s) + β_S·V_S(F(x,s))` then
attains its `[0,1]`-maximum at `s = 1` (both summands are maximized
there), so the greatest selector equals `1`. -/
theorem σ_dyn_top_V_S_zero_eq_one_of_monotone
    (hmono : Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x => p.V_S (fun _ => 0) continuous_const x))
    (hUS_max1 : ∀ x a s, s ∈ Sanctions.I → p.U_S x a s ≤ p.U_S x a 1)
    (x a : ℝ) :
    p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) x a = 1 := by
  set V := p.V_S (fun _ => 0) continuous_const with hV
  have h1_mem : (1 : ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_refl _⟩
  have h1_max : IsMaxOn
      (fun s' => p.U_S x a s' + p.β_S * V (Sanctions.clipS' (p.F x s')))
      Sanctions.I 1 := by
    intro s' hs'
    rw [Set.mem_setOf_eq]
    have hUS : p.U_S x a s' ≤ p.U_S x a 1 := hUS_max1 x a s' hs'
    have hF_le : p.F x s' ≤ p.F x 1 := p.F_mono_s x hs'.2
    have hclip : (Sanctions.clipS' (p.F x s') : ℝ)
                ≤ (Sanctions.clipS' (p.F x 1) : ℝ) := Sanctions.clipS'_mono hF_le
    have hV_le : V (Sanctions.clipS' (p.F x s')) ≤ V (Sanctions.clipS' (p.F x 1)) :=
      hmono hclip
    have hβV : p.β_S * V (Sanctions.clipS' (p.F x s'))
             ≤ p.β_S * V (Sanctions.clipS' (p.F x 1)) :=
      mul_le_mul_of_nonneg_left hV_le p.β_S_mem.1
    linarith
  have hge : 1 ≤ p.σ_dyn_top V x a := by
    unfold Params.σ_dyn_top
    exact le_csSup (p.dynamicArgmaxSet_bddAbove V x a) ⟨h1_mem, h1_max⟩
  have hle : p.σ_dyn_top V x a ≤ 1 := (p.σ_dyn_top_mem_I V x a).2
  linarith

/-- **Corner equilibrium from `σ_dyn_top ≡ 1` and `a`-independent Target
payoff.** If the greatest Sender selector is constant `1` at the corner
value (so it is continuous) and the Target stage payoff does not depend
on the Target action `a`, then the joint Target integrand is constant in
`a`, the corner `α ≡ 0` trivially attains its argmax, and a corner
`FeedbackStackelbergEquilibriumTop` exists. -/
theorem feedbackStackelbergTop_corner_exists_of_σtop_one
    (hσtop : ∀ x a, p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) x a = 1)
    (hU_T_aindep : ∀ x a s, p.U_T x a s = p.U_T x 0 s) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop, E.α = (fun _ => 0) := by
  have hσc : Continuous (fun xa : ℝ × ℝ =>
      p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) xa.1 xa.2) := by
    have h : (fun xa : ℝ × ℝ =>
          p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) xa.1 xa.2)
        = fun _ => (1 : ℝ) := by funext xa; exact hσtop xa.1 xa.2
    rw [h]; exact continuous_const
  refine p.feedbackStackelbergTop_of_corner_optimal hσc ?_
  intro x _ a _
  simp only [Set.mem_setOf_eq, Params.joint_T_top_integrand, hσtop, hU_T_aindep, le_refl]

/-! ## From-primitives corner equilibrium via the hardliner substituted-stage condition

The deepest of the parametric corner dischargers: instead of asking for
the corner to be the dynamic argmax outright (`h_corner`), or for the
Target payoff to be `a`-independent, this theorem *derives* corner
optimality from two economically-meaningful inputs evaluated *at the
endogenous Sender response* `σ* = σ_dyn_top V_S`:

* a **strict** stage-payoff decrease in the Target action (the hardliner
  sign condition: as the Target complies more, its σ-substituted stage
  payoff strictly falls), and
* a **weak** continuation decrease, itself *derived from primitives*: the
  Sender's response is antitone in the Target action (Step-1 sub-lemma,
  from `SenderActionDD` + dynamic-argmax uniqueness), `F` is monotone in
  the sanction, `clipS'` is monotone, and the Target value `V_T_dyn` is
  state-non-decreasing, so the discounted continuation value at the
  corner dominates its value at any positive compliance.

Their sum gives the `h_corner` certificate consumed by the corner
equilibrium constructor.

**Weak form (round BH-2, item BH2.10).** Each input is read once, and only
weakly. `feedbackStackelbergTop_corner_of_substituted_stage_le` therefore asks
for a **weak** stage decrease, for the comparison `σ* x a ≤ σ* x 0` with full
defiance in place of antitonicity in `a`, and for continuity of `σ*` on the
feasible states `↥S × ℝ` in place of `ℝ × ℝ` (its Target value is
`V_T_dyn_on`). A weak stage decrease plus the weak continuation decrease gives
the `IsMaxOn` certificate directly. The strict theorem is its corollary. -/

/-- **Basin-corner feedback-Stackelberg equilibrium under weak conditions.**
General in `F`: the transition enters only through `F_mono_s`.

Fix the Sender value at the saturated-corner Sender Bellman fixed point
`V_S := p.V_S (fun _ => 0) continuous_const`, and write `σ* := σ_dyn_top V_S`.
Suppose:

* `hσc` — `σ*` is jointly continuous on the feasible states `↥S × ℝ`
  (discharged, for instance, by `σ_dyn_top_continuous_subtype_of_unique_on`);
* `h_V_T_dyn_mono` — the Target value `V_T_dyn_on V_S hσc`, constructed
  against `σ*`, is non-decreasing in the state;
* `h_resp_le` — at every feasible state the Sender's response to a positive
  compliance `a ∈ (0,1]` is no larger than its response to full defiance,
  `σ* x a ≤ σ* x 0`;
* `h_subst_stage` — the substituted Target stage payoff does not rise when the
  Target complies, `U_T x a (σ* x a) ≤ U_T x 0 (σ* x 0)` for `a ∈ (0,1]`.

Then full defiance `α ≡ 0` attains the Target's dynamic argmax at every
feasible state, and a `FeedbackStackelbergEquilibriumTop` with leader policy
`α ≡ 0` exists.

Dropped relative to `feedbackStackelbergTop_corner_of_substituted_stage_strictDecr`:
continuity of `σ*` off the state space; antitonicity of `σ* x ·` on all pairs
of actions (only the comparison with `a = 0` is read); and strictness of the
stage decrease (the conclusion is an `IsMaxOn`, a weak statement).
Economically: full defiance is optimal as soon as complying never raises the
Target's stage payoff once the Sender's reply is substituted, and complying
never draws a harsher Sender reply than defiance does. -/
theorem feedbackStackelbergTop_corner_of_substituted_stage_le
    (hσc : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) xa.1.val xa.2))
    (h_V_T_dyn_mono : Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) =>
        p.V_T_dyn_on (p.V_S (fun _ => 0) continuous_const) hσc x))
    (h_resp_le : ∀ x ∈ Sanctions.S, ∀ a ∈ Set.Ioc (0 : ℝ) 1,
      p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) x a
        ≤ p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) x 0)
    (h_subst_stage : ∀ x ∈ Sanctions.S, ∀ a ∈ Set.Ioc (0 : ℝ) 1,
      p.U_T x a (p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) x a)
        ≤ p.U_T x 0 (p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) x 0)) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop, E.α = (fun _ => 0) := by
  set V_S := p.V_S (fun _ => 0) continuous_const with hV_S
  set V_T := p.V_T_dyn_on V_S hσc with hV_T
  refine p.feedbackStackelbergTop_of_constant_corner_optimal_on 0
    ⟨le_rfl, zero_le_one⟩ hσc ?_
  intro x hx a ha
  rw [Set.mem_setOf_eq]
  rcases eq_or_lt_of_le ha.1 with h0 | hpos
  · subst h0
    exact le_rfl
  · have ha' : a ∈ Set.Ioc (0 : ℝ) 1 := ⟨hpos, ha.2⟩
    -- STAGE: weak decrease.
    have h_stage : p.U_T x a (p.σ_dyn_top V_S x a) ≤ p.U_T x 0 (p.σ_dyn_top V_S x 0) :=
      h_subst_stage x hx a ha'
    -- CONTINUATION: weak decrease, through `F_mono_s`, `clipS'_mono` and `V_T` monotone.
    have h_F_le : p.F x (p.σ_dyn_top V_S x a) ≤ p.F x (p.σ_dyn_top V_S x 0) :=
      p.F_mono_s x (h_resp_le x hx a ha')
    have h_clip_le : (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x a)) : ℝ)
        ≤ (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x 0)) : ℝ) :=
      Sanctions.clipS'_mono h_F_le
    have h_V_le : V_T (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x a)))
        ≤ V_T (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x 0))) :=
      h_V_T_dyn_mono h_clip_le
    have h_βV_le : p.β_T * V_T (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x a)))
        ≤ p.β_T * V_T (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x 0))) :=
      mul_le_mul_of_nonneg_left h_V_le p.β_T_mem.1
    simp only [Params.joint_T_top_integrand]
    linarith

/-- **From-primitives basin-corner feedback-Stackelberg equilibrium under
the hardliner substituted-stage condition.**

Fix the Sender value at the saturated-corner Sender Bellman fixed point
`V_S := p.V_S (fun _ => 0) continuous_const`, and write `σ* := σ_dyn_top V_S`
for the greatest dynamic Sender selector. Suppose:

* `hσc` — joint `(x,a)`-continuity of `σ*` (discharged from primitives via
  the Berge route under dynamic-argmax uniqueness, `σ_dyn_top_continuous_of_unique`);
* `h_V_T_dyn_mono` — the constructed Banach Target value `V_T_dyn V_S hσc`
  is non-decreasing in the political state (discharged from primitives via
  `JointMPE.targetDynValue_monotone_of_integrand_monotone`);
* `h_antitone` — at every feasible state, `σ* x ·` is `AntitoneOn`
  `Sanctions.I` (the Step-1 sub-lemma
  `σ_dyn_top_antitoneOn_a_of_SenderActionDD`, from `SenderActionDD`
  decreasing differences + dynamic-argmax uniqueness);
* `h_subst_stage` — the **hardliner substituted-stage strict-decrease**:
  for every feasible state and every positive compliance `a ∈ (0,1]`, the
  σ-substituted Target stage payoff strictly falls,
  `U_T x a (σ* x a) < U_T x 0 (σ* x 0)`.

Then the corner policy `α ≡ 0` attains the Target's dynamic argmax at
every feasible state, and a genuine `FeedbackStackelbergEquilibriumTop`
exists with leader policy `α ≡ 0` and Target value the constructed Banach
fixed point `V_T_dyn V_S hσc`.

The only object asserted (not constructed) is the hardliner strict-stage
condition `h_subst_stage`; everything else is derived from the existing
primitives and the two from-primitives sub-lemmas.

General in `F`. Since round BH-2 (item BH2.10) this is a corollary of the weak
form `feedbackStackelbergTop_corner_of_substituted_stage_le`: continuity on
`ℝ × ℝ` restricts to `↥S × ℝ` (and then `V_T_dyn_on = V_T_dyn`,
`V_T_dyn_on_eq_V_T_dyn`), antitonicity gives the comparison with `a = 0`, and
the strict stage decrease gives the weak one. The statement is unchanged. -/
theorem feedbackStackelbergTop_corner_of_substituted_stage_strictDecr
    (hσc : Continuous (fun xa : ℝ × ℝ =>
      p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) xa.1 xa.2))
    (h_V_T_dyn_mono : Sanctions.StokeyLucas.MonotoneOnSubtype
      (fun x : ↥(Sanctions.S : Set ℝ) =>
        p.V_T_dyn (p.V_S (fun _ => 0) continuous_const) hσc x))
    (h_antitone : ∀ x ∈ Sanctions.S,
      AntitoneOn (fun a => p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) x a)
        Sanctions.I)
    (h_subst_stage : ∀ x ∈ Sanctions.S, ∀ a ∈ Set.Ioc (0 : ℝ) 1,
      p.U_T x a (p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) x a)
        < p.U_T x 0 (p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) x 0)) :
    ∃ E : p.FeedbackStackelbergEquilibriumTop, E.α = (fun _ => 0) := by
  have hσc_on : Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      p.σ_dyn_top (p.V_S (fun _ => 0) continuous_const) xa.1.val xa.2) :=
    hσc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  refine p.feedbackStackelbergTop_corner_of_substituted_stage_le hσc_on ?_
    (fun x hx a ha => h_antitone x hx ⟨le_rfl, zero_le_one⟩ ⟨ha.1.le, ha.2⟩ ha.1.le)
    (fun x hx a ha => (h_subst_stage x hx a ha).le)
  rw [p.V_T_dyn_on_eq_V_T_dyn _ hσc_on hσc]
  exact h_V_T_dyn_mono

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
