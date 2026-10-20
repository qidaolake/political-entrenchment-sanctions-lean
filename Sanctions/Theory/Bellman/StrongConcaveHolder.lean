/-
Sanctions/Theory/Bellman/StrongConcaveHolder.lean

**Substantive Hölder-1/2 bound for `σ_dyn` from strong concavity of
the dynamic Sender objective (audit-33 substantive-closure work).**

The standing audit-33 Gap 2/3 substantive obstruction:
- The carrier-restricted Lipschitz primitive `SigmaDynLipschitzOn` is
  taken as a category-(3) Prop in `LipschitzPrimitives.lean`.
- Strong concavity of the complete objective alone yields a **Hölder-1/2**
  bound in the sup-norm distance of the values, and that exponent is what
  the deviation-at-maximiser argument gives. A Lipschitz bound needs more
  than the sup-norm distance: control of the objective's perturbation in the
  action direction. A differentiable value space is one route to that
  control; it is not the only one (the chord economy's enriched subclass,
  `Examples/ChordEconomy`, bounds its response's shift by a semiconvexity
  argument, `Foundations/SemiconvexArgmaxShift`), and no such route is
  attempted here.

This file delivers the **Hölder-1/2 bound** substantively from
mathlib's `StrongConcaveOn`. The bound:

```
c · (σ_dyn V_S x a - σ_dyn V_S' x a)²  ≤  4 · β_S · dist V_S V_S'
```

equivalently

```
|σ_dyn V_S x a - σ_dyn V_S' x a|  ≤  2 · √(β_S/c) · √(dist V_S V_S').
```

This is what strong concavity of the objective gives without further
structure on how the objective moves in the action direction.

## Argument

For each `(x, a)`, let `f_V(s) := U_S(x, a, s) + β_S · V_S(F(x, s))`.
Under `SenderObjectiveStronglyConcaveOn D c`, `f_V` is `c`-strongly
concave in `s ∈ I` for every `V_S ∈ D.carrier`.

The standard deviation-at-maximizer lemma: if `s_max` maximizes `f`
on `I` and `s' ∈ I`, applying strong concavity at the midpoint
`(s_max + s')/2` gives `f s' ≤ f s_max - (c/4)(s_max - s')²`.

Let `σ = σ_dyn V_S x a`, `σ' = σ_dyn V_S' x a`. Applying deviation to
each:

```
f_V (σ')  ≤  f_V (σ)  - (c/4)(σ - σ')²
f_V'(σ )  ≤  f_V'(σ') - (c/4)(σ - σ')²
```

Adding and rearranging:

```
(c/2)(σ - σ')²  ≤  [f_V(σ) - f_V(σ')] + [f_V'(σ') - f_V'(σ)]
                =  β_S · [(V_S - V_S')(F(x,σ)) - (V_S - V_S')(F(x,σ'))]
                ≤  2 β_S · dist V_S V_S'
```

Hence `c · (σ - σ')² ≤ 4 β_S · dist V_S V_S'`. □

## Rule compliance

**Rule 1.** `σ_dyn` is the equilibrium-derived forward-looking Sender
argmax; `σ` and `σ'` are realized as `Classical.choose`-defined
argmaxes from `sender_arg_max_exists`.

**Rule 3.** Two new local theorem-parameter primitives
(category-(3) in the assumption-surface register):
- `SenderObjectiveStronglyConcaveOn D c` — strong concavity of the
  dynamic Sender objective on `D.carrier`. Mathlib's
  `StrongConcaveOn Sanctions.I c f` underlies the definition.
- The Hölder bound itself is **substantively derived** (not a
  primitive). The strong-concavity hypothesis is the only new
  primitive at this layer.

**Rule 5.** Fully parametric.

**Rule 6.** Mathlib `StrongConcaveOn` consulted; deviation-at-
maximizer lemma derived from the definition (not in mathlib
directly).
-/

import Sanctions.Theory.Bellman.InvariantValueClass
import Sanctions.Theory.Bellman.LipschitzPrimitives
import Sanctions.Foundations.StrongConcaveArgmax
import Mathlib.Analysis.Convex.Strong

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Strong-concavity primitive for the dynamic Sender objective -/

/-- **Strong-concavity primitive for the dynamic Sender objective.**
For every `V_S` in the value-class carrier and every state-action
pair `(x, a)`, the dynamic Sender objective
`f(s) = U_S(x, a, s) + β_S · V_S(F(x, s))` is `c`-strongly concave in
`s ∈ Sanctions.I` (mathlib's `StrongConcaveOn`).

Sufficient conditions: `U_S(x, a, ·)` is `c`-strongly concave in `s` and
the composition `s ↦ V_S(F(x, s))` is concave — for instance `V_S` concave
on `↥S` with `F(x, ·)` affine. Concavity of `V_S` alone is not enough under
a nonlinear sanction section: at `quadDiagFSwap`
(`Examples/PlacableSenderRallyBindingMember`, whose sanction sections are
convex dips), `V(y) = 30·y`, `U_S = −s²` and `β_S = 1/2`, the objective's
second derivative in `s` is `+1` (round J, doc 77 K6). -/
def SenderObjectiveStronglyConcaveOn (D : p.ValueClass) (c : ℝ) : Prop :=
  ∀ V_S : Val, V_S ∈ D.carrier → ∀ x a : ℝ,
    StrongConcaveOn Sanctions.I c
      (fun s => p.U_S x a s
        + p.β_S * V_S (Sanctions.clipS' (p.F x s)))

/-! ## Deviation lemma

`StrongConcaveOn.deviation_at_maximizer` — `f s' ≤ f s_max - (c/4)(s_max - s')²`
for a `c`-strongly concave `f` maximised at `s_max` — now lives in
`Foundations/StrongConcaveArgmax.lean` (doc 71, T4; Rule 19: it is generic
mathematics over mathlib's `StrongConcaveOn`). -/

/-! ## σ_dyn Hölder-1/2 bound (substantive) -/

/-- **Substantive Hölder-1/2 bound for `σ_dyn` from strong concavity.**
Under `SenderObjectiveStronglyConcaveOn D c`, the squared σ_dyn
difference is bounded by `(4·β_S/c) · dist V_S V_S'`:

```
c · (σ_dyn V_S x a - σ_dyn V_S' x a)²  ≤  4 · β_S · dist V_S V_S'.
```

This is the standard Hölder-1/2 rate from strong concavity alone;
genuine Lipschitz requires additional smoothness of `V_S` (C¹ in `s`),
which is incompatible with the BCF sup-norm topology. -/
theorem sigma_dyn_sq_le_of_strongConcave
    (D : p.ValueClass) {c : ℝ}
    (h_sc : p.SenderObjectiveStronglyConcaveOn D c)
    (V_S V_S' : D.Carrier) (x a : ℝ) :
    c * (p.σ_dyn V_S.val x a - p.σ_dyn V_S'.val x a) ^ 2
      ≤ 4 * p.β_S * dist V_S V_S' := by
  -- Notations.
  set σ : ℝ := p.σ_dyn V_S.val x a with hσ_def
  set σ' : ℝ := p.σ_dyn V_S'.val x a with hσ'_def
  set f_V : ℝ → ℝ := fun s => p.U_S x a s
    + p.β_S * V_S.val (Sanctions.clipS' (p.F x s))
    with hf_V_def
  set f_V' : ℝ → ℝ := fun s => p.U_S x a s
    + p.β_S * V_S'.val (Sanctions.clipS' (p.F x s))
    with hf_V'_def
  -- Memberships.
  have hσ_mem : σ ∈ Sanctions.I := p.σ_dyn_mem V_S.val x a
  have hσ'_mem : σ' ∈ Sanctions.I := p.σ_dyn_mem V_S'.val x a
  -- Strong concavity facts.
  have h_sc_V : StrongConcaveOn Sanctions.I c f_V :=
    h_sc V_S.val V_S.property x a
  have h_sc_V' : StrongConcaveOn Sanctions.I c f_V' :=
    h_sc V_S'.val V_S'.property x a
  -- σ maximizes f_V on I; σ' maximizes f_V' on I.
  have hσ_max : ∀ y ∈ Sanctions.I, f_V y ≤ f_V σ := by
    intro y hy
    have h := p.σ_dyn_isMaxOn V_S.val x a hy
    -- h : f_V y ≤ f_V σ via the σ_dyn argmax property
    exact h
  have hσ'_max : ∀ y ∈ Sanctions.I, f_V' y ≤ f_V' σ' := by
    intro y hy
    exact p.σ_dyn_isMaxOn V_S'.val x a hy
  -- I is convex.
  have hI_convex : Convex ℝ (Sanctions.I : Set ℝ) := convex_Icc 0 1
  -- Deviation: f_V σ' ≤ f_V σ - (c/4)(σ - σ')².
  have h_dev_V : f_V σ' ≤ f_V σ - (c / 4) * (σ - σ') ^ 2 :=
    StrongConcaveOn.deviation_at_maximizer hI_convex h_sc_V
      hσ_mem hσ'_mem hσ_max
  -- Deviation: f_V' σ ≤ f_V' σ' - (c/4)(σ' - σ)².
  have h_dev_V' : f_V' σ ≤ f_V' σ' - (c / 4) * (σ' - σ) ^ 2 :=
    StrongConcaveOn.deviation_at_maximizer hI_convex h_sc_V'
      hσ'_mem hσ_mem hσ'_max
  -- (σ - σ')² = (σ' - σ)².
  have h_sq_swap : (σ' - σ) ^ 2 = (σ - σ') ^ 2 := by ring
  rw [h_sq_swap] at h_dev_V'
  -- Add the two deviation bounds:
  --   f_V σ' + f_V' σ ≤ f_V σ + f_V' σ' - (c/2)(σ - σ')².
  have h_added : f_V σ' + f_V' σ
      ≤ f_V σ + f_V' σ' - (c / 2) * (σ - σ') ^ 2 := by
    have h_combine := add_le_add h_dev_V h_dev_V'
    linarith
  -- Rearrange: (c/2)(σ - σ')² ≤ [f_V σ - f_V σ'] + [f_V' σ' - f_V' σ].
  have h_rearr : (c / 2) * (σ - σ') ^ 2
      ≤ (f_V σ - f_V σ') + (f_V' σ' - f_V' σ) := by linarith
  -- f_V σ - f_V' σ = β_S · [V_S.val(F(x,σ)) - V_S'.val(F(x,σ))]
  -- f_V σ' - f_V' σ' = β_S · [V_S.val(F(x,σ')) - V_S'.val(F(x,σ'))]
  -- We need: [f_V σ - f_V σ'] + [f_V' σ' - f_V' σ]
  --        = [f_V σ - f_V' σ] - [f_V σ' - f_V' σ']
  --        = β_S · [(V_S - V_S')(F(x,σ))] - β_S · [(V_S - V_S')(F(x,σ'))]
  -- Bounded by sup-norm: ≤ β_S · 2 · dist V_S V_S'.
  have h_diff_form :
      (f_V σ - f_V σ') + (f_V' σ' - f_V' σ)
        = p.β_S * (V_S.val (Sanctions.clipS' (p.F x σ))
                    - V_S'.val (Sanctions.clipS' (p.F x σ)))
          - p.β_S * (V_S.val (Sanctions.clipS' (p.F x σ'))
                      - V_S'.val (Sanctions.clipS' (p.F x σ'))) := by
    simp only [hf_V_def, hf_V'_def]
    ring
  -- Pointwise BCF bound on each evaluation.
  have h_dist_subtype : dist V_S V_S' = dist V_S.val V_S'.val := by
    rw [Subtype.dist_eq]
  have h_BCF_σ :
      |V_S.val (Sanctions.clipS' (p.F x σ))
        - V_S'.val (Sanctions.clipS' (p.F x σ))|
        ≤ dist V_S V_S' := by
    have h_pt := BoundedContinuousFunction.dist_coe_le_dist
      (f := V_S.val) (g := V_S'.val)
      (Sanctions.clipS' (p.F x σ))
    rw [Real.dist_eq] at h_pt
    rw [h_dist_subtype]
    exact h_pt
  have h_BCF_σ' :
      |V_S.val (Sanctions.clipS' (p.F x σ'))
        - V_S'.val (Sanctions.clipS' (p.F x σ'))|
        ≤ dist V_S V_S' := by
    have h_pt := BoundedContinuousFunction.dist_coe_le_dist
      (f := V_S.val) (g := V_S'.val)
      (Sanctions.clipS' (p.F x σ'))
    rw [Real.dist_eq] at h_pt
    rw [h_dist_subtype]
    exact h_pt
  -- Combined absolute bound on the difference of differences.
  have hβS_nn : 0 ≤ p.β_S := p.β_S_mem.1
  have h_combined_abs :
      |(f_V σ - f_V σ') + (f_V' σ' - f_V' σ)|
        ≤ 2 * p.β_S * dist V_S V_S' := by
    rw [h_diff_form]
    calc |p.β_S * (V_S.val (Sanctions.clipS' (p.F x σ))
                    - V_S'.val (Sanctions.clipS' (p.F x σ)))
          - p.β_S * (V_S.val (Sanctions.clipS' (p.F x σ'))
                      - V_S'.val (Sanctions.clipS' (p.F x σ')))|
        ≤ |p.β_S * (V_S.val (Sanctions.clipS' (p.F x σ))
                    - V_S'.val (Sanctions.clipS' (p.F x σ)))|
          + |p.β_S * (V_S.val (Sanctions.clipS' (p.F x σ'))
                      - V_S'.val (Sanctions.clipS' (p.F x σ')))| :=
            abs_sub _ _
      _ = p.β_S * |V_S.val (Sanctions.clipS' (p.F x σ))
                    - V_S'.val (Sanctions.clipS' (p.F x σ))|
          + p.β_S * |V_S.val (Sanctions.clipS' (p.F x σ'))
                      - V_S'.val (Sanctions.clipS' (p.F x σ'))| := by
            rw [abs_mul, abs_of_nonneg hβS_nn, abs_mul, abs_of_nonneg hβS_nn]
      _ ≤ p.β_S * dist V_S V_S' + p.β_S * dist V_S V_S' := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left h_BCF_σ hβS_nn)
              (mul_le_mul_of_nonneg_left h_BCF_σ' hβS_nn)
      _ = 2 * p.β_S * dist V_S V_S' := by ring
  -- The non-absolute bound is at most the absolute bound:
  have h_le_abs :
      (f_V σ - f_V σ') + (f_V' σ' - f_V' σ)
        ≤ |(f_V σ - f_V σ') + (f_V' σ' - f_V' σ)| := le_abs_self _
  -- Combine: (c/2)(σ - σ')² ≤ 2 β_S dist V_S V_S'.
  have h_chain : (c / 2) * (σ - σ') ^ 2 ≤ 2 * p.β_S * dist V_S V_S' :=
    le_trans h_rearr (le_trans h_le_abs h_combined_abs)
  -- Multiply both sides by 2: c (σ - σ')² ≤ 4 β_S dist V_S V_S'.
  linarith

/-! ## Leader argmax `α_on` Hölder-1/2 in V_T (at fixed V_S) -/

/-- **Strong-concavity primitive for the leader joint-Bellman
integrand** `a ↦ joint_T_integrand V_T V_S x a` on `Sanctions.I` for
every `(V_T, V_S)` in the carrier × carrier and every state `x`. -/
def LeaderObjectiveStronglyConcaveOn (D : p.ValueClass) (c : ℝ) : Prop :=
  ∀ V_T : Val, V_T ∈ D.carrier → ∀ V_S : Val, V_S ∈ D.carrier → ∀ x : ℝ,
    StrongConcaveOn Sanctions.I c
      (fun a => p.joint_T_integrand V_T V_S x a)

/-- **Substantive Hölder-1/2 bound for the leader argmax in V_T (at
fixed V_S).** Mirror of `sigma_dyn_sq_le_of_strongConcave` for the
leader side. Key simplification (relative to V_S variation): when
V_T varies and V_S stays fixed, σ_dyn V_S x a is unchanged, so the
U_T part of `joint_T_integrand` cancels; only the V_T term differs.

```
c · (α(V_T) - α(V_T'))²  ≤  4 · β_T · dist V_T V_T'
```

V_S-variation gives only Hölder-1/4 (Hölder-1/2 of σ_dyn composed
with Hölder-1/2 deviation), not delivered here. -/
theorem targetArgmax_sq_le_of_leaderStrongConcave
    (D : p.ValueClass) {c : ℝ}
    (h_sc : p.LeaderObjectiveStronglyConcaveOn D c)
    (V_T V_T' V_S : D.Carrier) {x : ℝ} (hxS : x ∈ Sanctions.S) :
    c * (D.α_on V_T V_S x
          - D.α_on V_T' V_S x) ^ 2
      ≤ 4 * p.β_T * dist V_T V_T' := by
  -- Notations.
  set α : ℝ := D.α_on V_T V_S x with hα_def
  set α' : ℝ := D.α_on V_T' V_S x with hα'_def
  set g_VT : ℝ → ℝ := fun a => p.joint_T_integrand V_T.val V_S.val x a
    with hg_VT_def
  set g_VT' : ℝ → ℝ := fun a => p.joint_T_integrand V_T'.val V_S.val x a
    with hg_VT'_def
  -- Memberships.
  have hα_mem : α ∈ Sanctions.I :=
    D.α_on_mem V_T V_S x
  have hα'_mem : α' ∈ Sanctions.I :=
    D.α_on_mem V_T' V_S x
  -- Strong concavity facts (carrier-restricted).
  have h_sc_VT : StrongConcaveOn Sanctions.I c g_VT :=
    h_sc V_T.val V_T.property V_S.val V_S.property x
  have h_sc_VT' : StrongConcaveOn Sanctions.I c g_VT' :=
    h_sc V_T'.val V_T'.property V_S.val V_S.property x
  -- α is max of g_VT on I; α' is max of g_VT' on I.
  have hα_max : ∀ y ∈ Sanctions.I, g_VT y ≤ g_VT α := by
    intro y hy
    exact D.α_on_isMaxOn V_T V_S hxS hy
  have hα'_max : ∀ y ∈ Sanctions.I, g_VT' y ≤ g_VT' α' := by
    intro y hy
    exact D.α_on_isMaxOn V_T' V_S hxS hy
  -- I is convex.
  have hI_convex : Convex ℝ (Sanctions.I : Set ℝ) := convex_Icc 0 1
  -- Deviation lemmas.
  have h_dev_VT : g_VT α' ≤ g_VT α - (c / 4) * (α - α') ^ 2 :=
    StrongConcaveOn.deviation_at_maximizer hI_convex h_sc_VT
      hα_mem hα'_mem hα_max
  have h_dev_VT' : g_VT' α ≤ g_VT' α' - (c / 4) * (α' - α) ^ 2 :=
    StrongConcaveOn.deviation_at_maximizer hI_convex h_sc_VT'
      hα'_mem hα_mem hα'_max
  have h_sq_swap : (α' - α) ^ 2 = (α - α') ^ 2 := by ring
  rw [h_sq_swap] at h_dev_VT'
  -- Add: (c/2)(α - α')² ≤ [g_VT α - g_VT α'] + [g_VT' α' - g_VT' α].
  have h_added : g_VT α' + g_VT' α
      ≤ g_VT α + g_VT' α' - (c / 2) * (α - α') ^ 2 := by
    have h_combine := add_le_add h_dev_VT h_dev_VT'
    linarith
  have h_rearr : (c / 2) * (α - α') ^ 2
      ≤ (g_VT α - g_VT α') + (g_VT' α' - g_VT' α) := by linarith
  -- At fixed V_S, the integrand difference is purely the V_T term:
  -- g_VT(a) - g_VT'(a) = β_T (V_T.val - V_T'.val)(F(x, σ_dyn V_S x a))
  -- (σ_dyn V_S x a doesn't depend on V_T, so U_T cancels).
  have h_diff_α :
      g_VT α - g_VT' α
        = p.β_T * (V_T.val (Sanctions.clipS' (p.F x
                              (p.σ_dyn V_S.val x α)))
                   - V_T'.val (Sanctions.clipS' (p.F x
                                 (p.σ_dyn V_S.val x α)))) := by
    simp only [hg_VT_def, hg_VT'_def]
    unfold joint_T_integrand
    ring
  have h_diff_α' :
      g_VT α' - g_VT' α'
        = p.β_T * (V_T.val (Sanctions.clipS' (p.F x
                              (p.σ_dyn V_S.val x α')))
                   - V_T'.val (Sanctions.clipS' (p.F x
                                 (p.σ_dyn V_S.val x α')))) := by
    simp only [hg_VT_def, hg_VT'_def]
    unfold joint_T_integrand
    ring
  -- RHS = h_diff_α - h_diff_α' = β_T [V_T-V_T'](F(x,σ_α)) - β_T [V_T-V_T'](F(x,σ_α')).
  have h_rhs_form :
      (g_VT α - g_VT α') + (g_VT' α' - g_VT' α)
        = (g_VT α - g_VT' α) - (g_VT α' - g_VT' α') := by ring
  rw [h_rhs_form] at h_rearr
  -- Now substitute the forms.
  rw [h_diff_α, h_diff_α'] at h_rearr
  -- BCF sup-norm bounds.
  have hβT_nn : 0 ≤ p.β_T := p.β_T_mem.1
  have h_dist_subtype : dist V_T V_T' = dist V_T.val V_T'.val := by
    rw [Subtype.dist_eq]
  have h_BCF_α :
      |V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α)))
        - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α)))|
        ≤ dist V_T V_T' := by
    have h_pt := BoundedContinuousFunction.dist_coe_le_dist
      (f := V_T.val) (g := V_T'.val)
      (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α)))
    rw [Real.dist_eq] at h_pt
    rw [h_dist_subtype]; exact h_pt
  have h_BCF_α' :
      |V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α')))
        - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α')))|
        ≤ dist V_T V_T' := by
    have h_pt := BoundedContinuousFunction.dist_coe_le_dist
      (f := V_T.val) (g := V_T'.val)
      (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α')))
    rw [Real.dist_eq] at h_pt
    rw [h_dist_subtype]; exact h_pt
  -- Combined absolute bound on the difference of differences.
  have h_combined_abs :
      |p.β_T * (V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α)))
                - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α))))
        - p.β_T * (V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α')))
                    - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α'))))|
        ≤ 2 * p.β_T * dist V_T V_T' := by
    calc |p.β_T * (V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α)))
                  - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α))))
          - p.β_T * (V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α')))
                      - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α'))))|
        ≤ |p.β_T * (V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α)))
                    - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α))))|
          + |p.β_T * (V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α')))
                      - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α'))))| :=
            abs_sub _ _
      _ = p.β_T * |V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α)))
                    - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α)))|
          + p.β_T * |V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α')))
                      - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α')))| := by
            rw [abs_mul, abs_of_nonneg hβT_nn,
                abs_mul, abs_of_nonneg hβT_nn]
      _ ≤ p.β_T * dist V_T V_T' + p.β_T * dist V_T V_T' :=
            add_le_add
              (mul_le_mul_of_nonneg_left h_BCF_α hβT_nn)
              (mul_le_mul_of_nonneg_left h_BCF_α' hβT_nn)
      _ = 2 * p.β_T * dist V_T V_T' := by ring
  -- The non-absolute bound is at most the absolute bound.
  have h_le_abs :
      p.β_T * (V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α)))
                - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α))))
        - p.β_T * (V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α')))
                    - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α'))))
        ≤ |p.β_T * (V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α)))
                    - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α))))
          - p.β_T * (V_T.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α')))
                      - V_T'.val (Sanctions.clipS' (p.F x (p.σ_dyn V_S.val x α'))))| :=
    le_abs_self _
  have h_chain : (c / 2) * (α - α') ^ 2 ≤ 2 * p.β_T * dist V_T V_T' :=
    le_trans h_rearr (le_trans h_le_abs h_combined_abs)
  linarith

/-! ## Hölder Props derived from the substantive bounds

The Hölder-1/2 bounds proved above are packaged as formal Props that
parallel the `SigmaDynLipschitzOn` / `AlphaOnLipschitzOn` Lipschitz
primitives. The Lipschitz Props would be category-(3) primitives
requiring future IFT discharge (impossible in BCF as documented);
these Hölder Props are **substantively derived** from strong
concavity — category-(2) in the assumption-surface register
(weakening of the strong-concavity primitive). -/

/-- **Hölder-1/2 Prop for `σ_dyn` in V_S on the carrier.** The
squared σ_dyn difference is bounded by `L_H · dist V_S V_S'` for
some constant `L_H ≥ 0`. -/
def SigmaDynHolderOn (D : p.ValueClass) (L_H : ℝ) : Prop :=
  ∀ V_S V_S' : D.Carrier, ∀ x a : ℝ,
    (p.σ_dyn V_S.val x a - p.σ_dyn V_S'.val x a) ^ 2
      ≤ L_H * dist V_S V_S'

/-- **Substantive derivation of `SigmaDynHolderOn` from strong
concavity.** Under `SenderObjectiveStronglyConcaveOn D c` with
`c > 0`, the Hölder-1/2 bound holds with `L_H = 4·β_S/c`. -/
theorem SigmaDynHolderOn.of_strongConcave
    (D : p.ValueClass) {c : ℝ} (hc_pos : 0 < c)
    (h_sc : p.SenderObjectiveStronglyConcaveOn D c) :
    p.SigmaDynHolderOn D (4 * p.β_S / c) := by
  intro V_S V_S' x a
  have h_main := p.sigma_dyn_sq_le_of_strongConcave D
    h_sc V_S V_S' x a
  -- h_main : c * (σ - σ')^2 ≤ 4 * β_S * dist V_S V_S'
  -- Want: (σ - σ')^2 ≤ (4 * β_S / c) * dist V_S V_S'
  -- Divide both sides by c (positive).
  have h_div : (p.σ_dyn V_S.val x a - p.σ_dyn V_S'.val x a) ^ 2
                ≤ (4 * p.β_S * dist V_S V_S') / c :=
    le_div_iff₀ hc_pos |>.mpr (by linarith)
  calc (p.σ_dyn V_S.val x a - p.σ_dyn V_S'.val x a) ^ 2
      ≤ (4 * p.β_S * dist V_S V_S') / c := h_div
    _ = 4 * p.β_S / c * dist V_S V_S' := by ring

/-- **Hölder-1/2 Prop for the leader argmax `α_on` in V_T (at fixed
V_S) on the carrier.** Squared α_on difference bounded by `L_H_VT ·
dist V_T V_T'` at fixed V_S. (V_S variation gives only Hölder-1/4,
not packaged here.) -/
def AlphaOnHolderOnInVT (D : p.ValueClass) (L_H_VT : ℝ) : Prop :=
  ∀ V_T V_T' V_S : D.Carrier, ∀ x ∈ Sanctions.S,
    (D.α_on V_T V_S x
        - D.α_on V_T' V_S x) ^ 2
      ≤ L_H_VT * dist V_T V_T'

/-- **Substantive derivation of `AlphaOnHolderOnInVT` from leader
strong concavity.** Under `LeaderObjectiveStronglyConcaveOn D c`
with `c > 0`, the Hölder-1/2 bound for α_on in V_T (at fixed V_S)
holds with `L_H_VT = 4·β_T/c`. -/
theorem AlphaOnHolderOnInVT.of_leaderStrongConcave
    (D : p.ValueClass) {c : ℝ} (hc_pos : 0 < c)
    (h_sc : p.LeaderObjectiveStronglyConcaveOn D c) :
    p.AlphaOnHolderOnInVT D (4 * p.β_T / c) := by
  intro V_T V_T' V_S x hxS
  have h_main := p.targetArgmax_sq_le_of_leaderStrongConcave D
    h_sc V_T V_T' V_S hxS
  have h_div : (D.α_on V_T V_S x
                  - D.α_on V_T' V_S x) ^ 2
                ≤ (4 * p.β_T * dist V_T V_T') / c :=
    le_div_iff₀ hc_pos |>.mpr (by linarith)
  calc (D.α_on V_T V_S x
          - D.α_on V_T' V_S x) ^ 2
      ≤ (4 * p.β_T * dist V_T V_T') / c := h_div
    _ = 4 * p.β_T / c * dist V_T V_T' := by ring

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
