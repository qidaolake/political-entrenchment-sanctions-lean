/-
Sanctions/Theory/LockIn/MyopicComparator.lean

**Myopic (β = 0) comparator architecture for the abstract game.**

The previous `DynamicLockIn.dynamicLockInSanctions_ge_lockInSanctions`
compared the dynamic sanction sequence (driven by `σ_dyn V_S`) against
the *stage* sanction sequence under the same `α` and the same params.
External audits noted that, strictly read, the canonical "myopic
equilibrium" is the equilibrium of the β = 0 game — not the stage rule
of the original (β > 0) game under the dynamic α.

This module makes the framing explicit by introducing a `Params → Params`
transformation `Params.myopify` that zeros out both discount factors,
and provides the equivalence theorems showing that the existing
`lockInPath` / `lockInSanctions` *are* the legitimate β = 0 equilibrium
path: at the myopified params, the Sender's stage payoff argmax is
unchanged (the σ field is preserved), and the dynamic Sender objective
collapses to the stage objective because the continuation term
`β_S · V_S(F)` vanishes; similarly the Target's Bellman integrand
collapses to its stage payoff term, so the Target-Bellman-optimal policy
at the myopic params is the stage U_T argmax.

The headline dominance theorem
`dynamicLockInSanctions_ge_myopify_lockInSanctions` then re-states the
existing path-level comparison in the *equilibrium-vs-equilibrium*
form requested by the audit: the dynamic equilibrium of `p` weakly
dominates the myopic equilibrium of `p.myopify`.

**Rule 22.** The two reduction theorems are general in `F`: since BG2.5
(2026-10-06) they are stated over the model's own successor `p.myopify.F`
(before, the affine successor `(1 − δ)·x + δ·s` was written out by hand). The
path comparators are affine-restricted, because `lockInPath` and
`dynamicLockInPath` evolve the state by the affine law at `δ`. BG2.5 also
derived the dynamic level floor `h_level_dyn` of the headline from its other
hypotheses, and deleted the verbatim-duplicate `_with_equilibrium_evidence`
variant.

## Rule compliance

**Rule 1.** Every sanction path here is equilibrium-derived: the myopic
equilibrium uses the structural Sender argmax `p.σ` (carried by
`σ_isMaxOn_U_S`); the dynamic equilibrium uses the forward-looking
`p.σ_dyn V_S`. Both rules are stage or Bellman optimal at the relevant
parameter regime, not hand-chosen.

**Rule 3.** `Params.myopify` is a *transformation* on the existing
`Params` structure — no new fields, no new structural Props, no new
parameter hypotheses. The `Params.β_T_mem`/`Params.β_S_mem` admit the
endpoint `0` by definition (both are in `Set.Ico 0 1`), so the myopic
construction yields a valid `Params`. The reduction theorems
`myopify_σ_isMaxOn_dynamic` and `myopify_target_bellman_reduces_to_stage`
re-use existing structural data (no new hypotheses).

**Rule 5.** All theorems parametric over `(p, V_S, α)`. No
instantiation-specific content. The strict (not just weak)
dynamic-vs-myopic gap at concrete parameter points is DISCHARGED in
the `Sanctions/Examples/` layer: first by `eeCertCertificate`
(`Examples/EECertWitness.lean`, 2026-07-01, strict gap ≥ 1/5 on the
basin interior), and subsequently by three further complete
certificate witnesses (`qbCertCertificateMS`, non-affine transition;
`lbLow_generalF_three_goals`, low-basin mirror, both 2026-07-03; and
the B2 non-monotone-continuation witness, 2026-07-04). Non-vacuity is
no longer an open inhabitation item.
-/

import Sanctions.Theory.LockIn.DynamicLockIn

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

/-! ## The myopic (β = 0) Params transformation -/

/-- **Myopic version of `p`.** Zero out both discount factors, keep
all other fields. The result is a valid `Params` because `β_T = 0` and
`β_S = 0` lie in `Set.Ico 0 1`. -/
def myopify (p : Params) : Params where
  δ := p.δ
  δ_mem := p.δ_mem
  β_T := 0
  β_T_mem := ⟨le_refl 0, by norm_num⟩
  β_S := 0
  β_S_mem := ⟨le_refl 0, by norm_num⟩
  U_T := p.U_T
  U_S := p.U_S
  σ := p.σ
  σ_mem := p.σ_mem
  σ_isMaxOn_U_S := p.σ_isMaxOn_U_S
  U_T_continuous := p.U_T_continuous
  U_S_continuous := p.U_S_continuous
  F := p.F
  F_continuous := p.F_continuous
  F_mono_x := p.F_mono_x
  F_mono_s := p.F_mono_s
  F_diag := p.F_diag

@[simp] theorem myopify_δ (p : Params) : p.myopify.δ = p.δ := rfl
@[simp] theorem myopify_β_T (p : Params) : p.myopify.β_T = 0 := rfl
@[simp] theorem myopify_β_S (p : Params) : p.myopify.β_S = 0 := rfl
@[simp] theorem myopify_U_T (p : Params) : p.myopify.U_T = p.U_T := rfl
@[simp] theorem myopify_U_S (p : Params) : p.myopify.U_S = p.U_S := rfl
@[simp] theorem myopify_σ (p : Params) : p.myopify.σ = p.σ := rfl

/-- **Myopification keeps the static selector continuous.** `myopify` leaves `σ`
unchanged, so if the static Sender response of `p` is jointly continuous in the
state and the compliance level, so is that of `p.myopify`. General in `F`. Until
round BJ5.1 (2026-10-07) this was the copied field `σ_continuous := p.σ_continuous`
of `myopify`; it is now the instance that the static-selector results read at the
myopic economy. -/
instance myopify_staticSelectorContinuous (p : Params) [p.StaticSelectorContinuous] :
    p.myopify.StaticSelectorContinuous :=
  ⟨p.σ_continuous⟩

/-! ## Equivalence theorems for the path-level data

These are `rfl`-trivial because `myopify` only changes the `β_T`/`β_S`
fields, while `realizedRule`, `lockInStep`, `lockInPath`, and
`lockInSanctions` depend only on `δ` and `σ` (which `myopify` preserves). -/

@[simp] theorem myopify_realizedRule (p : Params) (α : ℝ → ℝ) :
    p.myopify.realizedRule α = p.realizedRule α := rfl

@[simp] theorem myopify_lockInStep (p : Params) (α : ℝ → ℝ) :
    p.myopify.lockInStep α = p.lockInStep α := rfl

@[simp] theorem myopify_lockInPath (p : Params) (α : ℝ → ℝ) (x₀ : ℝ) :
    p.myopify.lockInPath α x₀ = p.lockInPath α x₀ := rfl

@[simp] theorem myopify_lockInSanctions (p : Params) (α : ℝ → ℝ) (x₀ : ℝ) :
    p.myopify.lockInSanctions α x₀ = p.lockInSanctions α x₀ := rfl

/-! ## At myopify, σ is a dynamic Sender argmax

With `β_S = 0`, the dynamic Sender objective
`U_S(x, a, s) + β_S · V_S(F(x, s))` reduces to `U_S(x, a, s)`, whose
argmax on `[0, 1]` is `σ x a` by the structural `σ_isMaxOn_U_S`. -/

/-- At the myopic params, `σ x a` is an argmax of the dynamic Sender
objective for *any* continuation value `V_S`. (The `Classical.choose`-
selected `σ_dyn V_S` is also a maximizer; it may differ from `σ x a`
only when the argmax is non-unique.)

General in `F`: the objective is the Sender objective of `dynamicArgmaxSet`
at `p.myopify`, with the model's own successor `p.myopify.F x s'`. Restated in
BG2.5 (2026-10-06); it used to write the affine successor
`(1 − δ)·x + δ·s'` by hand, which is the model's successor only in affine
economies. The proof never reads the successor: `β_S = 0` removes the
continuation term whatever the transition. -/
theorem myopify_σ_isMaxOn_dynamic (p : Params)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    IsMaxOn (fun s' => p.myopify.U_S x a s'
      + p.myopify.β_S * V_S (Sanctions.clipS' (p.myopify.F x s')))
      Sanctions.I (p.σ x a) := by
  intro s hs
  change p.myopify.U_S x a s
         + p.myopify.β_S * V_S (Sanctions.clipS' (p.myopify.F x s))
       ≤ p.myopify.U_S x a (p.σ x a)
         + p.myopify.β_S * V_S (Sanctions.clipS' (p.myopify.F x (p.σ x a)))
  simp only [myopify_β_S, zero_mul, add_zero, myopify_U_S]
  exact p.σ_isMaxOn_U_S x a hs

/-! ## At myopify, the Target Bellman integrand reduces to stage U_T

With `β_T = 0`, the dynamic Target Bellman integrand
`U_T(x, a, σ_dyn(x, a)) + β_T · V_T(F)` reduces to its stage payoff
term `U_T(x, a, σ_dyn(x, a))`. So the Target's Bellman-optimal policy
at myopic params is the *stage* U_T argmax (against the chosen Sender
response). -/

/-- At the myopic params, the Target Bellman integrand reduces to the
stage U_T payoff against the Sender response. The Target's
Bellman-optimal policy at myopify is the stage U_T argmax.

General in `F`: the integrand is `p.myopify.joint_T_integrand V_T V_S x a`
written out, with the model's own successor `p.myopify.F`. Restated in BG2.5
(2026-10-06) from a form that wrote the affine successor by hand; as before,
`β_T = 0` removes the continuation term whatever the transition. -/
theorem myopify_target_bellman_reduces_to_stage (p : Params)
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ)
    (h_stage_max : IsMaxOn (fun a => p.U_T x a (p.myopify.σ_dyn V_S x a))
                            Sanctions.I (α x)) :
    IsMaxOn (fun a => p.myopify.U_T x a (p.myopify.σ_dyn V_S x a)
                      + p.myopify.β_T * V_T (Sanctions.clipS'
                          (p.myopify.F x (p.myopify.σ_dyn V_S x a))))
            Sanctions.I (α x) := by
  intro a ha
  change p.myopify.U_T x a (p.myopify.σ_dyn V_S x a)
         + p.myopify.β_T * V_T (Sanctions.clipS'
             (p.myopify.F x (p.myopify.σ_dyn V_S x a)))
       ≤ p.myopify.U_T x (α x) (p.myopify.σ_dyn V_S x (α x))
         + p.myopify.β_T * V_T (Sanctions.clipS'
             (p.myopify.F x (p.myopify.σ_dyn V_S x (α x))))
  simp only [myopify_β_T, zero_mul, add_zero]
  exact h_stage_max ha

/-! ## Dominance of dynamic over myopic equilibrium

The headline architectural theorem: under the standard comparison
hypotheses, the dynamic equilibrium sanctions of `p` weakly dominate
the *equilibrium* sanctions of `p.myopify` (which by
`myopify_lockInSanctions` is the same path as
`p.lockInSanctions α x₀`).

The theorem below is the **same-α path-level dominance**: it requires
the kinematic comparison hypotheses but does not, by itself, certify
that `α` is Target-Bellman-optimal at `p` or `p.myopify`. For the
genuine equilibrium-vs-equilibrium reading, callers should additionally
hold the Bellman-optimality of `α` on both sides — at `p` against
`σ_dyn V_S`, and at `p.myopify` against the stage response `p.σ`, which
is also a dynamic Sender argmax there (`myopify_σ_isMaxOn_dynamic`) while
the Target integrand collapses to stage `U_T`
(`myopify_target_bellman_reduces_to_stage`). The proof never reads that
evidence, so it is not a hypothesis here. A variant that merely added it
to the signature, `..._with_equilibrium_evidence`, had the same conclusion
verbatim and was deleted in BG2.5 (2026-10-06). -/

/-- **Dynamic equilibrium ≥ myopic equilibrium.** The dynamic sanction
sequence (driven by the forward-looking `σ_dyn V_S` at the original
discount factors) weakly dominates the myopic equilibrium sanction
sequence (the lock-in sanction path of `p.myopify`, the β = 0 game).
The myopic-equilibrium path is, by the equivalence theorems above,
identically equal to `p.lockInSanctions α x₀` — the path-level
proposition is therefore identical to
`dynamicLockInSanctions_ge_lockInSanctions`, but with the explicit
myopic-equilibrium framing.

Affine-restricted (Rule 22): both lock-in paths move by the affine law at
`δ`. Since BG2.5 (2026-10-06) the dynamic level floor
`max x sbar ≤ σ_dyn(x, α x)` on the basin is no longer a hypothesis: it follows
from the myopic floor and the rule comparison `h_dyn_ge_myo`, because the
forward-looking rule sanctions at least as much as a myopic rule that already
clears the floor. -/
theorem dynamicLockInSanctions_ge_myopify_lockInSanctions
    (p : Params) (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar : ℝ}
    (h_level_myo : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.myopify.realizedRule α x)
    (h_dyn_ge_myo : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      p.myopify.realizedRule α x ≤ p.dynamicRealizedRule V_S α x)
    (h_dyn_mono : MonotoneOn (p.dynamicRealizedRule V_S α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.myopify.lockInSanctions α x₀ n
            ≤ p.dynamicLockInSanctions V_S α x₀ n := by
  intro n
  rw [myopify_lockInSanctions]
  -- Now the goal is the existing dynamic-vs-stage-σ comparison; discharge
  -- via `dynamicLockInSanctions_ge_lockInSanctions`.
  have h_level_myo' :
      ∀ x ∈ Set.Icc xbar (1 : ℝ), max x sbar ≤ p.realizedRule α x := by
    intro x hx; exact h_level_myo x hx
  have h_dyn_ge_myo' :
      ∀ x ∈ Set.Icc xbar (1 : ℝ),
        p.realizedRule α x ≤ p.dynamicRealizedRule V_S α x := by
    intro x hx; exact h_dyn_ge_myo x hx
  -- The dynamic floor is derived, not assumed (BG2.5).
  have h_level_dyn :
      ∀ x ∈ Set.Icc xbar (1 : ℝ), max x sbar ≤ p.dynamicRealizedRule V_S α x :=
    fun x hx => le_trans (h_level_myo' x hx) (h_dyn_ge_myo' x hx)
  exact p.dynamicLockInSanctions_ge_lockInSanctions V_S α
    h_level_dyn h_level_myo' h_dyn_ge_myo' h_dyn_mono hx₀ n

/-! ## Post-shock dynamic ≥ myopic-equilibrium composition

Lifts the dominance theorem to the post-shock regime: after a temporary
exogenous shock pushes the state into the basin, the dynamic equilibrium
sanction sequence weakly dominates the myopic-equilibrium sanction
sequence forever. -/

/-- **Post-shock dynamic equilibrium ≥ post-shock myopic equilibrium.**
Composes the shock-entry arithmetic (`shockPath_eventually_in_basin`)
with the dynamic-vs-myopic-equilibrium dominance. Affine-restricted
(Rule 22): the shock path and both lock-in paths use the affine law. Since
BG2.5 (2026-10-06) the dynamic level floor is derived inside the headline, so
it is no longer a hypothesis here either. -/
theorem dynamic_temporary_shock_post_shock_dominates_myopify
    (p : Params) (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    {xbar sbar : ℝ}
    (hxbar_lt : xbar < 1)
    (h_level_myo : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      max x sbar ≤ p.myopify.realizedRule α x)
    (h_dyn_ge_myo : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                      p.myopify.realizedRule α x ≤ p.dynamicRealizedRule V_S α x)
    (h_dyn_mono : MonotoneOn (p.dynamicRealizedRule V_S α) (Set.Icc xbar 1))
    {x₀ : ℝ} (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ, ∀ n,
      p.myopify.lockInSanctions α (p.shockPath x₀ N) n
        ≤ p.dynamicLockInSanctions V_S α (p.shockPath x₀ N) n := by
  obtain ⟨N, hN⟩ := p.shockPath_eventually_in_basin hx₀_nn hx₀_le hxbar_lt
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  exact ⟨N, p.dynamicLockInSanctions_ge_myopify_lockInSanctions V_S α
    h_level_myo h_dyn_ge_myo h_dyn_mono h_N_in⟩

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
