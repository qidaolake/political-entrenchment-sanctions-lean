/-
Sanctions/Theory/Equilibrium/BergeContinuity.lean

**Berge's maximum theorem for the dynamic Sender argmax.**

The audit's open item "$\sigma_{\rm dyn}$-as-`SenderResponse`-interface
instance (joint $(x,a)$-continuity)" required Berge's maximum theorem:
under uniqueness of the dynamic Sender argmax, the
`Classical.choose`-defined $\sigma_{\rm dyn}\,V_S\,x\,a$ is jointly
continuous in $(x, a)$.

This module proves Berge's theorem for our specific setup
(continuous objective on a compact constant choice set
$\mathrm{I} = [0, 1]$, parameterized by $(x, a) \in \mathbb{R}^2$).

## Argument

The standard Berge argument adapted to our scalar case:
1. The dynamic Sender objective $f(x, a, s) = U_S(x, a, s) + \beta_S \cdot V_S(F(x, s))$
   is **jointly continuous** in $(x, a, s)$ (composition of continuous
   pieces: `U_S_continuous`, `clipS'_continuous`, $V_S$'s BCF continuity,
   and the transition's continuity `p.F_continuous` — general in $F$).
2. Any **subsequential limit** of $\sigma_{\rm dyn}\,V_S\,x_n\,a_n$
   (where $(x_n, a_n) \to (x_0, a_0)$) is a maximizer of $f(x_0, a_0, \cdot)$
   on $[0, 1]$: pass to the limit in the inequality
   $f(x_n, a_n, s_n) \geq f(x_n, a_n, s')$ for any $s' \in [0, 1]$.
3. **Under uniqueness**, the maximizer at $(x_0, a_0)$ is a singleton.
   By compactness of $[0, 1]$ + uniqueness, every cluster point of
   $\sigma_{\rm dyn}\,V_S\,(x_n, a_n)$ equals $\sigma_{\rm dyn}\,V_S\,(x_0, a_0)$.
4. Sequential continuity follows; since $\mathbb{R}^2$ is metrizable,
   continuity holds.

## Open content remaining

This closes the **continuity** half of Berge's theorem. A
**quantitative Lipschitz-in-$V_S$** bound for $\sigma_{\rm dyn}$, which the
general joint Bellman row-Lipschitz bound from primitives would need, is not
proved here. What is proved elsewhere: under strong concavity of the
*complete* objective, `Theory/Bellman/StrongConcaveHolder.lean` gives a
Hölder-1/2 estimate in the sup-norm distance of the values; on the placable
family, `Examples/PlacableSenderEquilibrium.lean` §7 bounds the response's
shift in the *state* with an explicit constant. A linear estimate in $V_S$
needs control of the objective's perturbation in the action direction beyond
its sup norm; an implicit-function argument alone does not supply it, and no
such route is attempted here (round J, doc 77 K6).

## Rule compliance

**Rule 1.** $\sigma_{\rm dyn}\,V_S$ is the equilibrium-derived
forward-looking Sender response (argmax of the dynamic Sender
objective). No hand-chosen rule.

**Rule 3.** Local theorem-parameter hypotheses only (`h_unique` for
the specific theorem instance). No new fields on `AbstractGame.Params`;
no new Postulates; no new global `Prop`. The uniqueness hypothesis
concerns the complete dynamic objective
$U_S(x,a,\cdot) + \beta_S V_S(F(x,\cdot))$; strict concavity of the stage
payoff alone does not deliver it, since the continuation can offset it (see
the header of `SigmaDynComparison.lean`). On the chord economy
(`Examples/ChordEconomy`, the placable class with both stage payoffs abstract)
it is derived from strict concavity of the complete objective
(`senderObj_strictConcaveOn` → `DAU_on_carrier`). It is the same hypothesis
pattern as in `SigmaDynComparison.lean`.

**Rule 5.** Fully parametric over `(p, V_S, h_unique)`.
-/

import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Theory.Bridges.SenderResponse
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Sequences

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Joint continuity of the dynamic Sender objective in `(x, a, s)` -/

/-- The dynamic Sender objective `f(x, a, s) = U_S(x, a, s) + β_S · V_S(F(x, s))`
is jointly continuous in `(x, a, s)`. -/
theorem sender_integrand_continuous_jointly
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) :
    Continuous (fun (xas : ℝ × ℝ × ℝ) => p.U_S xas.1 xas.2.1 xas.2.2
      + p.β_S * V_S (Sanctions.clipS' (p.F xas.1 xas.2.2))) := by
  have hU : Continuous (fun (xas : ℝ × ℝ × ℝ) => p.U_S xas.1 xas.2.1 xas.2.2) :=
    p.U_S_continuous
  have hclipS' : Continuous (Sanctions.clipS' : ℝ → ↥(Sanctions.S : Set ℝ)) :=
    Sanctions.clipS'_continuous
  have hF : Continuous (fun (xas : ℝ × ℝ × ℝ) =>
      p.F xas.1 xas.2.2) :=
    p.F_continuous.comp ((continuous_fst).prodMk (continuous_snd.comp continuous_snd))
  exact hU.add (continuous_const.mul (V_S.continuous.comp (hclipS'.comp hF)))

/-! ## Berge: limit of argmaxes is an argmax

The standard Berge-step: if `(x_n, a_n) → (x_0, a_0)` and
`s_n ∈ argmax_s f(x_n, a_n, s)` on `[0, 1]`, and `s_n → s*`, then
`s* ∈ argmax_s f(x_0, a_0, s)` on `[0, 1]`. -/

/-- **Berge limit step.** Let `(xa_n) → xa_0` in `ℝ × ℝ` and
`s_n → s*` in `[0, 1]`, with `s_n` a maximizer of the dynamic Sender
objective `f(xa_n.1, xa_n.2, ·)` on `[0, 1]`. Then `s*` is a maximizer
of `f(xa_0.1, xa_0.2, ·)` on `[0, 1]`. -/
theorem isMaxOn_sender_obj_of_limit
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    {xa_seq : ℕ → ℝ × ℝ} {xa₀ : ℝ × ℝ}
    (h_xa_tendsto : Tendsto xa_seq atTop (𝓝 xa₀))
    {s_seq : ℕ → ℝ} {sStar : ℝ}
    (h_s_tendsto : Tendsto s_seq atTop (𝓝 sStar))
    (h_s_max : ∀ n, IsMaxOn
      (fun s => p.U_S (xa_seq n).1 (xa_seq n).2 s
        + p.β_S * V_S (Sanctions.clipS' (p.F (xa_seq n).1 s)))
      Sanctions.I (s_seq n)) :
    IsMaxOn
      (fun s => p.U_S xa₀.1 xa₀.2 s
        + p.β_S * V_S (Sanctions.clipS' (p.F xa₀.1 s)))
      Sanctions.I sStar := by
  intro s' hs'
  -- Pointwise: for each n, f(xa_n, s_n) ≥ f(xa_n, s')
  have h_ptn : ∀ n,
      (fun (xas : ℝ × ℝ × ℝ) => p.U_S xas.1 xas.2.1 xas.2.2
        + p.β_S * V_S (Sanctions.clipS' (p.F xas.1 xas.2.2)))
        ((xa_seq n).1, (xa_seq n).2, s')
      ≤ (fun (xas : ℝ × ℝ × ℝ) => p.U_S xas.1 xas.2.1 xas.2.2
        + p.β_S * V_S (Sanctions.clipS' (p.F xas.1 xas.2.2)))
        ((xa_seq n).1, (xa_seq n).2, s_seq n) := fun n => h_s_max n hs'
  -- LHS tendsto: f(xa_n, s') → f(xa₀, s') by joint continuity + constant s
  have h_xas_lhs : Tendsto (fun n : ℕ => ((xa_seq n).1, (xa_seq n).2, s')) atTop
                            (𝓝 (xa₀.1, xa₀.2, s')) := by
    refine .prodMk_nhds ?_ ?_
    · exact (continuous_fst.tendsto _).comp h_xa_tendsto
    · refine .prodMk_nhds ?_ tendsto_const_nhds
      exact (continuous_snd.tendsto _).comp h_xa_tendsto
  have h_lhs := ((p.sender_integrand_continuous_jointly V_S).tendsto _).comp h_xas_lhs
  -- RHS tendsto: f(xa_n, s_n) → f(xa₀, s*) by joint continuity
  have h_xas_rhs : Tendsto (fun n : ℕ => ((xa_seq n).1, (xa_seq n).2, s_seq n)) atTop
                            (𝓝 (xa₀.1, xa₀.2, sStar)) := by
    refine .prodMk_nhds ?_ ?_
    · exact (continuous_fst.tendsto _).comp h_xa_tendsto
    · exact .prodMk_nhds ((continuous_snd.tendsto _).comp h_xa_tendsto) h_s_tendsto
  have h_rhs := ((p.sender_integrand_continuous_jointly V_S).tendsto _).comp h_xas_rhs
  -- Conclude via le_of_tendsto_of_tendsto
  exact le_of_tendsto_of_tendsto' h_lhs h_rhs h_ptn

/-! ## Berge continuity of `σ_dyn V_S` under uniqueness -/

/-- **Berge's maximum theorem for `σ_dyn`.** Under uniqueness of the
dynamic argmax for the given `V_S`, the `Classical.choose`-defined
`σ_dyn V_S` is jointly continuous in `(x, a)`. -/
theorem σ_dyn_continuous_of_unique
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_unique : ∀ x a s₁ s₂, s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₁ →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₂ → s₁ = s₂) :
    Continuous (fun (xa : ℝ × ℝ) => p.σ_dyn V_S xa.1 xa.2) := by
  -- Sequential continuity (since ℝ² is first-countable / metrizable)
  rw [Metric.continuous_iff]
  intro xa₀ ε hε
  -- Negate and extract violating sequence
  by_contra h_neg
  push Not at h_neg
  -- For each n, pick xa_n with dist xa_n xa₀ < 1/(n+1) but distance ≥ ε
  -- ⟦For each δ > 0, there's xa with dist xa xa₀ < δ but |σ_dyn xa - σ_dyn xa₀| ≥ ε⟧
  -- Apply at δ = 1/(n+1)
  choose xa_seq h_close h_far using fun n : ℕ => h_neg (1 / (n + 1))
    (by positivity)
  -- xa_seq : ℕ → ℝ × ℝ
  -- h_close : ∀ n, dist (xa_seq n) xa₀ < 1/(n+1)
  -- h_far : ∀ n, dist (p.σ_dyn V_S (xa_seq n).1 (xa_seq n).2)
  --                   (p.σ_dyn V_S xa₀.1 xa₀.2) ≥ ε
  -- Tendsto xa_seq → xa₀
  have h_xa_tendsto : Tendsto xa_seq atTop (𝓝 xa₀) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    -- Want N such that ∀ n ≥ N, dist (xa_seq n) xa₀ < δ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    calc dist (xa_seq n) xa₀
        < 1 / (n + 1) := h_close n
      _ ≤ 1 / (N + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hn 1
      _ < δ := hN
  -- Let s_seq = σ_dyn V_S xa_seq
  set s_seq : ℕ → ℝ := fun n => p.σ_dyn V_S (xa_seq n).1 (xa_seq n).2 with hs_def
  -- s_seq is in [0, 1] (compact)
  have hs_mem : ∀ n, s_seq n ∈ Sanctions.I := fun n => p.σ_dyn_mem V_S _ _
  -- By compactness of [0, 1], extract convergent subsequence
  have h_compact_I : IsCompact (Sanctions.I : Set ℝ) := isCompact_Icc
  -- Use IsCompact.tendsto_subseq to get φ : ℕ → ℕ strict mono and sStar with s_seq ∘ φ → sStar
  obtain ⟨sStar, hsStar_mem, φ, hφ_mono, h_sub_tendsto⟩ :=
    h_compact_I.tendsto_subseq hs_mem
  -- The subsequence xa_seq ∘ φ also tends to xa₀
  have h_xa_sub_tendsto : Tendsto (xa_seq ∘ φ) atTop (𝓝 xa₀) :=
    h_xa_tendsto.comp hφ_mono.tendsto_atTop
  -- Each s_seq (φ n) is a max
  have h_s_max_sub : ∀ n, IsMaxOn
      (fun s => p.U_S (xa_seq (φ n)).1 (xa_seq (φ n)).2 s
        + p.β_S * V_S (Sanctions.clipS' (p.F (xa_seq (φ n)).1 s)))
      Sanctions.I (s_seq (φ n)) := fun n => p.σ_dyn_isMaxOn V_S _ _
  -- Berge: sStar is a max of f(xa₀, ·)
  have h_sStar_max := p.isMaxOn_sender_obj_of_limit V_S
    h_xa_sub_tendsto h_sub_tendsto h_s_max_sub
  -- σ_dyn V_S xa₀.1 xa₀.2 is also a max
  have h_σ_dyn_max := p.σ_dyn_isMaxOn V_S xa₀.1 xa₀.2
  have h_σ_dyn_mem := p.σ_dyn_mem V_S xa₀.1 xa₀.2
  -- By uniqueness, sStar = σ_dyn V_S xa₀.1 xa₀.2
  have h_eq : sStar = p.σ_dyn V_S xa₀.1 xa₀.2 := by
    apply h_unique xa₀.1 xa₀.2 sStar (p.σ_dyn V_S xa₀.1 xa₀.2) hsStar_mem h_σ_dyn_mem
    · exact h_sStar_max
    · exact h_σ_dyn_max
  -- The subsequence (s_seq ∘ φ) tends to σ_dyn xa₀
  rw [h_eq] at h_sub_tendsto
  -- But h_far says dist (s_seq n) (σ_dyn xa₀) ≥ ε for all n, including φ n
  have h_far_sub : ∀ n, ε ≤ dist (s_seq (φ n)) (p.σ_dyn V_S xa₀.1 xa₀.2) := by
    intro n
    have := h_far (φ n)
    -- h_far says: ¬ (dist ... < ε), i.e., dist ... ≥ ε
    rw [hs_def]
    linarith [h_far (φ n)]
  -- The limit of (s_seq ∘ φ) is σ_dyn xa₀, but each term is ≥ ε away. Contradiction.
  have h_tendsto_zero : Tendsto (fun n => dist (s_seq (φ n)) (p.σ_dyn V_S xa₀.1 xa₀.2))
                                 atTop (𝓝 0) := by
    rw [show (0 : ℝ) = dist (p.σ_dyn V_S xa₀.1 xa₀.2) (p.σ_dyn V_S xa₀.1 xa₀.2) from
        (dist_self _).symm]
    exact (continuous_id.dist continuous_const).continuousAt.tendsto.comp h_sub_tendsto
  -- ε ≤ dist (s_seq (φ n)) (σ_dyn xa₀), tendsto 0 → ε ≤ 0, contradiction
  have h_zero_ge_ε : ε ≤ 0 := by
    apply ge_of_tendsto h_tendsto_zero
    exact Filter.Eventually.of_forall h_far_sub
  linarith

/-! ## State-local Berge continuity of `σ_dyn V_S` (Design A)

The global `σ_dyn_continuous_of_unique` requires uniqueness of the
dynamic Sender argmax at *every* `x : ℝ`, including unphysical states
`x ∉ [0,1]` that the clamped dynamics never visit. For a substantive
interior-argmax economy, uniqueness genuinely fails off `[0,1]` (a
convex clip kink can create two equal maxima), so the global form is
too strong. The state-local companion below needs uniqueness only at
physical states `x ∈ S = [0,1]`, and concludes joint continuity of
`σ_dyn V_S` on `S ×ˢ univ` — which is all the BCF-on-`↥S`
construction requires (every visited state is in `S`).

Round BJ4.3 (2026-10-08) adds the compliance-local companion
`σ_dyn_continuousOn_SI_of_unique_on`: uniqueness only at physical states and
physical compliance levels `a ∈ I`, continuity on `S ×ˢ I`. Both are instances
of `σ_dyn_continuousOn_of_unique_at`, which takes the set of uniqueness points
as a parameter. -/

/-- **Berge continuity of `σ_dyn V_S` on any set of uniqueness points (round
BJ4.3, 2026-10-08).** General in `F`. If the dynamic Sender argmax is unique
at every point `(x, a)` of a set `T ⊆ ℝ × ℝ`, the `Classical.choose`-defined
`σ_dyn V_S` is continuous on `T`. The Berge limit step
(`isMaxOn_sender_obj_of_limit`) is uniqueness-free; uniqueness is invoked only
at the limit point, which lies in `T` because continuity on `T` is tested at
points of `T`. This is the common engine of the state-local form
(`T = S ×ˢ univ`) and the compliance-local form (`T = S ×ˢ I`); its proof is
the former proof of `σ_dyn_continuousOn_S_of_unique_on`, with the set left
free. -/
theorem σ_dyn_continuousOn_of_unique_at
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (T : Set (ℝ × ℝ))
    (h_unique : ∀ xa ∈ T, ∀ s₁ s₂,
        s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
        IsMaxOn (fun s' => p.U_S xa.1 xa.2 s'
          + p.β_S * V_S (Sanctions.clipS' (p.F xa.1 s')))
          Sanctions.I s₁ →
        IsMaxOn (fun s' => p.U_S xa.1 xa.2 s'
          + p.β_S * V_S (Sanctions.clipS' (p.F xa.1 s')))
          Sanctions.I s₂ → s₁ = s₂) :
    ContinuousOn (fun (xa : ℝ × ℝ) => p.σ_dyn V_S xa.1 xa.2) T := by
  rw [Metric.continuousOn_iff]
  intro xa₀ hxa₀ ε hε
  by_contra h_neg
  push Not at h_neg
  -- For each n, pick xa_n ∈ T with dist xa_n xa₀ < 1/(n+1) but
  -- |σ_dyn xa_n - σ_dyn xa₀| ≥ ε.
  choose xa_seq h_mem h_close h_far using
    fun n : ℕ => h_neg (1 / (n + 1)) (by positivity)
  -- Tendsto xa_seq → xa₀.
  have h_xa_tendsto : Tendsto xa_seq atTop (𝓝 xa₀) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    calc dist (xa_seq n) xa₀
        < 1 / (n + 1) := h_close n
      _ ≤ 1 / (N + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hn 1
      _ < δ := hN
  -- s_seq n := σ_dyn V_S xa_n, all in the compact I.
  set s_seq : ℕ → ℝ := fun n => p.σ_dyn V_S (xa_seq n).1 (xa_seq n).2 with hs_def
  have hs_mem : ∀ n, s_seq n ∈ Sanctions.I := fun n => p.σ_dyn_mem V_S _ _
  have h_compact_I : IsCompact (Sanctions.I : Set ℝ) := isCompact_Icc
  obtain ⟨sStar, hsStar_mem, φ, hφ_mono, h_sub_tendsto⟩ :=
    h_compact_I.tendsto_subseq hs_mem
  have h_xa_sub_tendsto : Tendsto (xa_seq ∘ φ) atTop (𝓝 xa₀) :=
    h_xa_tendsto.comp hφ_mono.tendsto_atTop
  have h_s_max_sub : ∀ n, IsMaxOn
      (fun s => p.U_S (xa_seq (φ n)).1 (xa_seq (φ n)).2 s
        + p.β_S * V_S (Sanctions.clipS' (p.F (xa_seq (φ n)).1 s)))
      Sanctions.I (s_seq (φ n)) := fun n => p.σ_dyn_isMaxOn V_S _ _
  -- Berge: sStar is a max at xa₀ (uniqueness-free limit step).
  have h_sStar_max := p.isMaxOn_sender_obj_of_limit V_S
    h_xa_sub_tendsto h_sub_tendsto h_s_max_sub
  have h_σ_dyn_max := p.σ_dyn_isMaxOn V_S xa₀.1 xa₀.2
  have h_σ_dyn_mem := p.σ_dyn_mem V_S xa₀.1 xa₀.2
  -- Uniqueness AT xa₀ (xa₀ ∈ T): sStar = σ_dyn xa₀.
  have h_eq : sStar = p.σ_dyn V_S xa₀.1 xa₀.2 := by
    apply h_unique xa₀ hxa₀ sStar (p.σ_dyn V_S xa₀.1 xa₀.2)
      hsStar_mem h_σ_dyn_mem
    · exact h_sStar_max
    · exact h_σ_dyn_max
  rw [h_eq] at h_sub_tendsto
  have h_far_sub : ∀ n, ε ≤ dist (s_seq (φ n)) (p.σ_dyn V_S xa₀.1 xa₀.2) := by
    intro n
    rw [hs_def]
    linarith [h_far (φ n)]
  have h_tendsto_zero :
      Tendsto (fun n => dist (s_seq (φ n)) (p.σ_dyn V_S xa₀.1 xa₀.2))
              atTop (𝓝 0) := by
    rw [show (0 : ℝ) = dist (p.σ_dyn V_S xa₀.1 xa₀.2) (p.σ_dyn V_S xa₀.1 xa₀.2)
          from (dist_self _).symm]
    exact (continuous_id.dist continuous_const).continuousAt.tendsto.comp h_sub_tendsto
  have h_zero_ge_ε : ε ≤ 0 := by
    apply ge_of_tendsto h_tendsto_zero
    exact Filter.Eventually.of_forall h_far_sub
  linarith

/-- **State-local Berge continuity of `σ_dyn V_S`.** Under uniqueness
of the dynamic Sender argmax *for states `x ∈ S`* (the physical state
space `[0,1]`), the `Classical.choose`-defined `σ_dyn V_S` is jointly
continuous in `(x, a)` on `S ×ˢ univ`. State-local companion of
`σ_dyn_continuous_of_unique`. The Berge limit step
(`isMaxOn_sender_obj_of_limit`) is uniqueness-free and reused verbatim;
uniqueness is invoked only at the limit point `xa₀`, whose first
coordinate lies in `S` by hypothesis. Since round BJ4.3 (2026-10-08) a
corollary of `σ_dyn_continuousOn_of_unique_at` at `T = S ×ˢ univ`; statement
unchanged. -/
theorem σ_dyn_continuousOn_S_of_unique_on
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_unique : ∀ x ∈ Sanctions.S, ∀ a s₁ s₂,
        s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₁ →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₂ → s₁ = s₂) :
    ContinuousOn (fun (xa : ℝ × ℝ) => p.σ_dyn V_S xa.1 xa.2)
      (Sanctions.S ×ˢ (Set.univ : Set ℝ)) :=
  p.σ_dyn_continuousOn_of_unique_at V_S _
    (fun xa hxa => h_unique xa.1 hxa.1 xa.2)

/-- **Compliance-local Berge continuity of `σ_dyn V_S` (round BJ4.3,
2026-10-08).** General in `F`. Under uniqueness of the dynamic Sender argmax
at physical states `x ∈ S` *and physical compliance levels `a ∈ I`*, the
`Classical.choose`-defined `σ_dyn V_S` is jointly continuous on `S ×ˢ I`.
Compliance-local sibling of `σ_dyn_continuousOn_S_of_unique_on`: uniqueness at
compliance levels outside `[0,1]` is dropped, and continuity is concluded on
`S ×ˢ I` instead of `S ×ˢ univ`. That is all the joint Target Bellman operator
needs, since the Target's choice set is `I`. Same proof (the instance
`T = S ×ˢ I` of `σ_dyn_continuousOn_of_unique_at`). -/
theorem σ_dyn_continuousOn_SI_of_unique_on
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (h_unique : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I, ∀ s₁ s₂,
        s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₁ →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₂ → s₁ = s₂) :
    ContinuousOn (fun (xa : ℝ × ℝ) => p.σ_dyn V_S xa.1 xa.2)
      (Sanctions.S ×ˢ Sanctions.I) :=
  p.σ_dyn_continuousOn_of_unique_at V_S _
    (fun xa hxa => h_unique xa.1 hxa.1 xa.2 hxa.2)

/-! ## SenderResponse instance for the forward-looking argmax

Under a parametric uniqueness hypothesis (uniqueness of the dynamic
argmax for each `V_S`), the `Classical.choose`-defined `σ_dyn` is a
genuine `Sanctions.JointMPE.SenderResponse` instance — the abstract
forward-looking analog of `staticSenderResponse` from `HeSunMPE.lean`.

The uniqueness hypothesis is the only structural condition needed
(continuity of `σ_dyn V_S` in `(x, a)` follows from Berge's theorem
above). The hypothesis is the local theorem-parameter form; at a
concrete instantiation, it is dischargeable from strict concavity of
the complete dynamic Sender objective in $s$ (or from another direct
argmax-uniqueness argument). Strict concavity of the stage payoff
$U_S$ alone is not sufficient. -/

/-- **Forward-looking dynamic `SenderResponse` instance** under
uniqueness of the dynamic argmax. Wraps `σ_dyn` into the
`Sanctions.JointMPE.SenderResponse` interface. -/
noncomputable def dynamicSenderResponse
    (h_unique : ∀ (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ)
      (s₁ s₂ : ℝ), s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₁ →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₂ → s₁ = s₂) :
    Sanctions.JointMPE.SenderResponse where
  σ V_S x a := p.σ_dyn V_S x a
  σ_mem V_S x a := p.σ_dyn_mem V_S x a
  σ_continuous V_S := p.σ_dyn_continuous_of_unique V_S (h_unique V_S)

/-- **Argmax certification of `dynamicSenderResponse`.** The response
packaged in `dynamicSenderResponse` IS the dynamic Sender argmax. -/
theorem dynamicSenderResponse_isMaxOn
    (h_unique : ∀ (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ)
      (s₁ s₂ : ℝ), s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₁ →
        IsMaxOn (fun s' => p.U_S x a s'
          + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
          Sanctions.I s₂ → s₁ = s₂)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    IsMaxOn (fun s' => p.U_S x a s'
      + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
      Sanctions.I ((p.dynamicSenderResponse h_unique).σ V_S x a) :=
  p.σ_dyn_isMaxOn V_S x a

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
