/-
Copyright (c) 2026 Xiaofeng Gong. All rights reserved.
-/
import Sanctions.Examples.FeedbackComparativeStatics

/-!
# Perpetual sanctions on an interval of Sender patience

`Examples/PerpetualSanctionExistence` shows that perpetual sanctions occur at
*some* primitives.  An existence claim of that shape answers "why those
magnitudes?" --- the numbers are bound inside the existential --- but it does not
answer a second and different objection: an isolated witness could be
**knife-edge**, with the behaviour disappearing under any perturbation.

This file answers that objection.  The conclusion holds not at a point but on a
**non-degenerate interval** of Sender discount factors.

`perpetual_sanctions_on_beta_interval` --- for **every** `β ∈ [6/13, 4/7)` there
is an equilibrium of `eeCertParamsB β` along which, from every initial state of
the high basin and at every date, the realised sanction stays above a positive
floor and never falls, and the political state never leaves the basin.  The
transition is a deterministic affine law (rate existentially bound, so no
magnitude appears), hence the game has perfect information.

`beta_window_nondegenerate` records that the window really is a continuum rather
than a disguised point.

## The conclusion is sharper than a floor

`eeCertB_sanctions_eq_one`: along the whole path the realised sanction is not
merely bounded below but **exactly maximal**, at every date, for every patience
in the window.  The positive floor and the monotonicity in the headline are
immediate consequences.

Economically this is the corner-lock-in regime: the Sender's forward-looking
motive is strong enough, throughout the window, that the greatest dynamic
response sits at the ceiling regardless of the state, and the Target's
best response is full defiance.  Both governments optimise at every date --- the
Target's action carries the equilibrium's Bellman-optimality field and the
Sender's sanction is the greatest maximiser of its forward-looking objective.

## Scope

This is robustness in **one** direction: the Sender's discount factor.  The
remaining primitives are held at the `eeCert` values, so this is not a
neighbourhood in the full parameter space and does not claim to be.  What it
rules out is the specific worry that the perpetual-sanction conclusion survives
only at an isolated point of the patience parameter.

Note also that the escalation here is *weak* --- sanctions sit at the ceiling
from the outset rather than climbing to it.  The strictly increasing path of
`Examples/P3SubBasinMonotonicity` remains available only at the shocked economy.
-/

namespace Sanctions
namespace Examples

open Set AbstractGame

noncomputable section

/-! Parameter-interval robustness: the perpetual-sanction conclusion is not a
knife-edge property of one calibration. It holds at EVERY Sender patience in a
non-degenerate interval. -/

/-- The realised sanction of the `eeCertB` equilibrium is maximal at every
feasible state, for every Sender patience in the window. -/
theorem eeCertB_realized_rule_eq_one (β : ℝ) (hβ : β ∈ Set.Ico (6/13 : ℝ) (4/7))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (eeCertParamsB β hβ).dynamicTopRealizedRule
      (eeCertBEquilibrium β hβ).V_S (eeCertBEquilibrium β hβ).α x = 1 := by
  show (eeCertParamsB β hβ).σ_dyn_top (eeVSstarB β) x _ = 1
  exact eeCertB_σ_dyn_top_eq_one β hβ (eeVSstarB_mem hβ) hx
    ((eeCertBEquilibrium β hβ).α_mem x hx)

/-- The closed-loop step from a feasible state stays feasible and never falls. -/
theorem eeCertB_step_mem (β : ℝ) (hβ : β ∈ Set.Ico (6/13 : ℝ) (4/7))
    {x : ℝ} (hx : x ∈ Set.Icc (1/2 : ℝ) 1) :
    (eeCertParamsB β hβ).dynamicTopLockInStepF
      (eeCertBEquilibrium β hβ).V_S (eeCertBEquilibrium β hβ).α x
      ∈ Set.Icc (1/2 : ℝ) 1 := by
  have hx01 : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  show (eeCertParamsB β hβ).F x _ ∈ _
  rw [eeCertB_realized_rule_eq_one β hβ hx01]
  show AbstractGame.affineF (1/2 : ℝ) x 1 ∈ _
  simp only [AbstractGame.affineF]
  constructor <;> [linarith [hx.1]; linarith [hx.2]]

/-- The whole path stays in the basin. -/
theorem eeCertB_path_mem (β : ℝ) (hβ : β ∈ Set.Ico (6/13 : ℝ) (4/7))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (1/2 : ℝ) 1) :
    ∀ n, (eeCertParamsB β hβ).dynamicTopLockInPathF
      (eeCertBEquilibrium β hβ).V_S (eeCertBEquilibrium β hβ).α x₀ n
      ∈ Set.Icc (1/2 : ℝ) 1 := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ k ih =>
      rw [AbstractGame.Params.dynamicTopLockInPathF_succ]
      exact eeCertB_step_mem β hβ ih

/-- **Maximal sanctions at every date, for every patience in the window.** -/
theorem eeCertB_sanctions_eq_one (β : ℝ) (hβ : β ∈ Set.Ico (6/13 : ℝ) (4/7))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (1/2 : ℝ) 1) :
    ∀ n, (eeCertParamsB β hβ).dynamicTopLockInSanctionsF
      (eeCertBEquilibrium β hβ).V_S (eeCertBEquilibrium β hβ).α x₀ n = 1 := by
  intro n
  have hmem := eeCertB_path_mem β hβ hx₀ n
  exact eeCertB_realized_rule_eq_one β hβ ⟨by linarith [hmem.1], hmem.2⟩

/-- **Parameter-interval perpetual sanctions.**

For **every** Sender discount factor in the non-degenerate interval
`[6/13, 4/7)` there is a perfect-information infinite-horizon equilibrium along
which, from every initial state of the high basin and at every date, the
realised sanction is *maximal* --- hence bounded below by a positive floor and
non-decreasing --- and the political state never leaves the basin.

This is the answer to the knife-edge objection: the conclusion is not a property
of one tuned point but of a continuum of economies. -/
theorem perpetual_sanctions_on_beta_interval
    (β : ℝ) (hβ : β ∈ Set.Ico (6/13 : ℝ) (4/7)) :
    ∃ (E : (eeCertParamsB β hβ).FeedbackStackelbergEquilibriumTop) (sbar : ℝ),
      (∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ (eeCertParamsB β hβ).F = AbstractGame.affineF δ)
      ∧ 0 < sbar
      ∧ ∀ x₀ ∈ Set.Icc (1/2 : ℝ) 1,
          (∀ n, (eeCertParamsB β hβ).dynamicTopLockInPathF E.V_S E.α x₀ n
                  ∈ Set.Icc (1/2 : ℝ) 1)
          ∧ (∀ n, sbar ≤ (eeCertParamsB β hβ).dynamicTopLockInSanctionsF
                            E.V_S E.α x₀ n)
          ∧ Monotone ((eeCertParamsB β hβ).dynamicTopLockInSanctionsF
                            E.V_S E.α x₀) := by
  refine ⟨eeCertBEquilibrium β hβ, 1, ⟨1/2, by norm_num, by norm_num, rfl⟩,
    by norm_num, fun x₀ hx₀ => ⟨eeCertB_path_mem β hβ hx₀, ?_, ?_⟩⟩
  · intro n; rw [eeCertB_sanctions_eq_one β hβ hx₀ n]
  · intro m n _
    rw [eeCertB_sanctions_eq_one β hβ hx₀ m, eeCertB_sanctions_eq_one β hβ hx₀ n]

/-- The interval is non-degenerate: it contains at least two distinct patience
values, so this is a genuine continuum and not a disguised point. -/
theorem beta_window_nondegenerate :
    (6/13 : ℝ) < 4/7 ∧ (6/13 : ℝ) ∈ Set.Ico (6/13 : ℝ) (4/7)
      ∧ (1/2 : ℝ) ∈ Set.Ico (6/13 : ℝ) (4/7) := by
  refine ⟨by norm_num, ⟨le_refl _, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

#print axioms eeCertB_realized_rule_eq_one
#print axioms eeCertB_sanctions_eq_one
#print axioms perpetual_sanctions_on_beta_interval
#print axioms beta_window_nondegenerate

end

end Examples
end Sanctions
