/-
Sanctions/Theory/LockIn/SigmaDynComparison.lean

**Direct derivation of dynamic ≥ stage Sender argmax under monotone
Sender continuation value.**

The paper-level economic claim "forward-looking Sender weakly more
aggressive than myopic Sender on the basin" is the load-bearing
hypothesis $\sigma^{\rm dyn}_{V_S}(x,\alpha(x))\geq\sigma(x,\alpha(x))$
of the `DynamicLockIn` comparison theorems. This module discharges it
from the canonical economic primitive: monotonicity of $V_S$ in the
state (which is itself dischargeable from BellmanS cone preservation
when the Sender integrand is monotone).

The argument is Milgrom-Shannon / Topkis single-crossing: at any
$(x, a)$, the dynamic Sender objective
$g(s) := U_S(x,a,s) + \beta_S \cdot V_S(F(x, s))$ differs from the
stage Sender objective $f(s) := U_S(x,a,s)$ by the *monotone
non-decreasing* (in $s$) term $\beta_S \cdot V_S(F(x,s))$ — non-
negativity of $\beta_S$ + monotonicity of $V_S$ + monotonicity of
$F(x, \cdot)$ on $[0, 1]$ give the increment $g - f$ monotone
non-decreasing. This single-crossing property shifts the argmax set
of $g$ "upward" relative to the argmax set of $f$ in the strong-set
order; in particular, $\max(s_f, s_g)$ is a maximizer of $g$ for any
stage-argmax $s_f$ and any dynamic-argmax $s_g$.

The conclusion is an **existence-level** statement:

  `∃ s* ∈ [0, 1], IsMaxOn (dynamic objective) s* ∧ p.σ x a ≤ s*`

This is *not* the same as the pointwise $p.\sigma_{\rm dyn}\,V_S\,x\,a \geq p.\sigma\,x\,a$
that one would want for plugging into `dynamicLockInSanctions_ge_lockInSanctions`
because $\sigma_{\rm dyn}$ is `Classical.choose`-defined and might
select a different (lower) dynamic argmax when the dynamic argmax set
is non-singleton. The pointwise inequality requires uniqueness of the
dynamic argmax — discharged from strict concavity or strict
monotonicity of the **complete dynamic objective** in $s$ at a
concrete instantiation. Stage concavity of $U_S$ alone gives only
stage-argmax uniqueness. (Audit-27 docstring correction: uniqueness collapses
$\sigma_{\rm dyn}\,V_S = \sigma_{\rm dyn}^{\rm top}\,V_S$ — the
upper-argmax selector — *not* $\sigma_{\rm dyn}\,V_S = \sigma$. The
upper selector satisfies the unconditional comparison
$\sigma_{\rm dyn}^{\rm top}\,V_S \geq \sigma$ under monotone $V_S$;
uniqueness merely identifies the `Classical.choose` selector with the
upper selector, yielding $\sigma_{\rm dyn}\,V_S \geq \sigma$.)

The general Berge-style pointwise derivation under uniqueness is
machine-checked in this module via `σ_dyn_ge_sigma_of_unique`
(building on the upper-argmax selector `σ_dyn_top`), and the joint
`(x, a)`-continuity of `σ_dyn V_S` under uniqueness is machine-checked
in `Theory/Equilibrium/BergeContinuity.lean` (`σ_dyn_continuous_of_unique`).
The single-step wrapper
`pointwise_σ_dyn_ge_σ_from_integrand_monotone` below derives the
pointwise comparison hypothesis from primitive monotonicity of the
Sender stage payoff in x + uniqueness.

## Rule compliance

**Rule 1.** $\sigma$ and $\sigma_{\rm dyn}\,V_S$ are both
equilibrium-derived (stage / dynamic argmaxes via `Classical.choose`
on compact-image existence). The new theorem is a derivation of
their *relative ordering*, not a hand-chosen sanction rule.

**Rule 3.** Local theorem-parameter hypothesis `Monotone V_S` only;
no new fields on `AbstractGame.Params`; no new Postulates. Per Rule 3,
local hypotheses on an existing theorem parameter are exempt; the
$V_S$-monotonicity hypothesis is the canonical conclusion of the
Sender BCF monotone-cone preservation theorem
(`bellmanS_BCF_preserves_monotone` in `Theory/Bellman/BellmanS`)
when the Sender integrand is monotone in the state — i.e. it is
already a derivable primitive at any concrete instantiation.

**Rule 5.** Fully parametric over `(p : Params, V_S, x, a)`. No
witness-specific content.
-/

import Sanctions.Foundations.MonotoneDifferenceArgmax
import Sanctions.Theory.Equilibrium.JointMPE
import Sanctions.Foundations.MilgromShannon

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Milgrom-Shannon: upper argmax of $g$ above any argmax of $f$
when $g - f$ is monotone non-decreasing. -/

/-- **Milgrom-Shannon-style upper-argmax preservation.** Let $f, g$
be real-valued functions on $\mathbb{R}$, with the difference
$g - f$ monotone non-decreasing on `[0, 1]`. Then for any argmax
$s_f$ of $f$ on `[0, 1]` and any argmax $s_g$ of $g$ on `[0, 1]`,
$\max(s_f, s_g)$ is also an argmax of $g$ on `[0, 1]`. -/
theorem isMaxOn_max_of_monotone_diff
    {f g : ℝ → ℝ}
    (h_diff_mono : MonotoneOn (fun s => g s - f s) Sanctions.I)
    {s_f s_g : ℝ}
    (hs_f : s_f ∈ Sanctions.I)
    (hs_g : s_g ∈ Sanctions.I)
    (h_f_max : IsMaxOn f Sanctions.I s_f)
    (h_g_max : IsMaxOn g Sanctions.I s_g) :
    IsMaxOn g Sanctions.I (max s_f s_g) :=
  -- doc 68, L7: the mathematics lives in
  -- `Foundations/MonotoneDifferenceArgmax.lean`; this is the `[0,1]` instance
  -- kept under its historical name for the consumers below.
  Sanctions.Foundations.MonotoneDifferenceArgmax.isMaxOn_max_of_monotone_diff
    h_diff_mono hs_f hs_g h_f_max h_g_max

/-- `max` of two elements of `[0, 1]` is in `[0, 1]`. -/
theorem _root_.Sanctions.max_mem_I {s_f s_g : ℝ}
    (hs_f : s_f ∈ Sanctions.I) (hs_g : s_g ∈ Sanctions.I) :
    max s_f s_g ∈ Sanctions.I :=
  ⟨le_max_iff.mpr (Or.inl hs_f.1), max_le hs_f.2 hs_g.2⟩

/-! ## Dynamic argmax above stage argmax under monotone $V_S$ -/

/-- The Sender continuation map $s \mapsto V_S(\mathrm{clipS}'(F(x,s)))$
is monotone non-decreasing in $s$ on `[0, 1]` when $V_S$ is monotone
non-decreasing on `↥S`.

Rule 22: general in `F`. The proof is `p.F_mono_s`, the `Params` field saying a
harsher sanction never lowers next period's entrenchment; no functional form of
the transition is used. (Corrected 2026-09-01 — this docstring previously wrote
the affine law $(1-\delta)x + \delta s$, which the statement does not assume.) -/
theorem sender_continuation_mono_in_s
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (h_V_S_mono : Monotone V_S) (x : ℝ) :
    MonotoneOn (fun s => V_S (Sanctions.clipS' (p.F x s)))
               Sanctions.I := by
  intro s₁ _ s₂ _ hle
  apply h_V_S_mono
  apply Sanctions.clipS'_mono
  exact p.F_mono_s x hle

/-- The increment from stage to dynamic Sender objective is
$\beta_S \cdot V_S(F(x, s))$, monotone non-decreasing in $s$ under
the monotone-$V_S$ hypothesis. -/
theorem dynamic_minus_stage_mono_in_s
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (h_V_S_mono : Monotone V_S) (x a : ℝ) :
    MonotoneOn (fun s => (p.U_S x a s
        + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
        - p.U_S x a s)
        Sanctions.I := by
  have h_simp : (fun s : ℝ => (p.U_S x a s
        + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
        - p.U_S x a s)
      = (fun s : ℝ => p.β_S * V_S
          (Sanctions.clipS' (p.F x s))) := by
    funext s; ring
  rw [h_simp]
  intro s₁ hs₁ s₂ hs₂ hle
  have h_V : V_S (Sanctions.clipS' (p.F x s₁))
              ≤ V_S (Sanctions.clipS' (p.F x s₂)) :=
    p.sender_continuation_mono_in_s V_S h_V_S_mono x hs₁ hs₂ hle
  have hβ : 0 ≤ p.β_S := p.β_S_mem.1
  exact mul_le_mul_of_nonneg_left h_V hβ

/-- **Dynamic argmax above any stage maximiser (existence), selection-free.**
Under monotone $V_S$, for **every** maximiser `m` of the stage payoff
$s \mapsto U_S(x,a,s)$ on `[0, 1]` there is a maximiser `sStar` of the
dynamic Sender objective $s \mapsto U_S(x,a,s) + \beta_S \cdot V_S(F(x,s))$
on `[0, 1]` with `m ≤ sStar`. Economically: whichever myopic best response
the Sender would pick, some forward-looking best response sanctions at least
as hard, because a monotone continuation value only adds a term that rises in
the sanction.

Rule 22: general in `F` (the transition enters only through `F_mono_s`, inside
`dynamic_minus_stage_mono_in_s`). Selection-free sibling of
`exists_dynamic_argmax_ge_sigma` (BH6.8, 2026-10-07): the `Params` stage
selector `σ` is replaced by an arbitrary stage maximiser `m`, which is all
that proof ever read from `σ` (`σ_mem` and `σ_isMaxOn_U_S`). No hypothesis is
added; the σ-form is the instance `m := p.σ x a`. -/
theorem exists_dynamic_argmax_ge_of_stage_max
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (h_V_S_mono : Monotone V_S) {x a m : ℝ}
    (hm : m ∈ Sanctions.I)
    (hmax : IsMaxOn (fun s => p.U_S x a s) Sanctions.I m) :
    ∃ sStar ∈ Sanctions.I,
      IsMaxOn (fun s => p.U_S x a s
        + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
        Sanctions.I sStar
      ∧ m ≤ sStar := by
  obtain ⟨s_dyn, h_s_dyn_mem, h_s_dyn_max⟩ := p.sender_arg_max_exists V_S x a
  refine ⟨max m s_dyn, Sanctions.max_mem_I hm h_s_dyn_mem, ?_, le_max_left _ _⟩
  exact isMaxOn_max_of_monotone_diff
    (p.dynamic_minus_stage_mono_in_s V_S h_V_S_mono x a)
    hm h_s_dyn_mem hmax h_s_dyn_max

/-- **Dynamic argmax above stage argmax (existence).** Under monotone
$V_S$, there exists a maximizer `sStar` of the dynamic Sender objective
$s \mapsto U_S(x,a,s) + \beta_S \cdot V_S(F(x,s))$ on `[0, 1]` with
`p.σ x a ≤ sStar`.

This is the direct derivation of the paper-level "$\sigma^{\rm dyn}_{V_S}
\geq \sigma$" claim from the canonical primitive (monotone Sender
continuation value). It is *existence-level*; pointwise
`p.σ_dyn V_S x a ≥ p.σ x a` via the project's `Classical.choose`-
defined `σ_dyn` additionally requires uniqueness of the dynamic
argmax (e.g. via strict monotonicity of `U_S` in `s` — see the
companion `σ_dyn_eq_one_of_strictMono` below when the continuation
preserves that monotonicity — or via strict concavity of the complete
dynamic objective), which is the deferred Berge-selector open content.

General in `F`. Since BH6.8 (2026-10-07) a one-line instance of the
selection-free `exists_dynamic_argmax_ge_of_stage_max` at `m := p.σ x a`;
statement unchanged. -/
theorem exists_dynamic_argmax_ge_sigma
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (h_V_S_mono : Monotone V_S) (x a : ℝ) :
    ∃ sStar ∈ Sanctions.I,
      IsMaxOn (fun s => p.U_S x a s
        + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
        Sanctions.I sStar
      ∧ p.σ x a ≤ sStar :=
  p.exists_dynamic_argmax_ge_of_stage_max V_S h_V_S_mono (p.σ_mem x a)
    (p.σ_isMaxOn_U_S x a)

/-! ## Pointwise $\sigma_{\rm dyn}\,V_S \geq \sigma$ under uniqueness

When the dynamic argmax is unique (singleton argmax set), the
`Classical.choose`-selected $\sigma_{\rm dyn}\,V_S\,x\,a$ equals that
unique element, and the existence theorem above collapses to a
pointwise comparison. The cleanest uniqueness sufficient condition is
strict monotonicity of the dynamic Sender objective in $s$, which
under monotone $V_S$ reduces to strict monotonicity of $U_S$ in $s$. -/

/-- If the dynamic Sender objective is strictly monotone non-decreasing
in $s$ on `[0, 1]`, then its unique argmax on `[0, 1]` is $s = 1$, and
$\sigma_{\rm dyn}\,V_S\,x\,a = 1$. -/
theorem σ_dyn_eq_one_of_strictMono
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ)
    (h_strict :
      StrictMonoOn (fun s => p.U_S x a s
        + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
        Sanctions.I) :
    p.σ_dyn V_S x a = 1 := by
  have h_mem : p.σ_dyn V_S x a ∈ Sanctions.I := p.σ_dyn_mem V_S x a
  have h_one_mem : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl _⟩
  have h_max : IsMaxOn (fun s => p.U_S x a s
      + p.β_S * V_S (Sanctions.clipS' (p.F x s)))
      Sanctions.I (p.σ_dyn V_S x a) :=
    p.σ_dyn_isMaxOn V_S x a
  -- The max value at σ_dyn is ≥ the value at 1
  have h_ge_at_one : (fun s => p.U_S x a s
      + p.β_S * V_S (Sanctions.clipS' (p.F x s))) 1
        ≤ (fun s => p.U_S x a s
      + p.β_S * V_S (Sanctions.clipS' (p.F x s))) (p.σ_dyn V_S x a) :=
    h_max h_one_mem
  -- By strict monotonicity, this forces σ_dyn = 1
  by_contra h_ne
  have h_lt : p.σ_dyn V_S x a < 1 := lt_of_le_of_ne h_mem.2 h_ne
  have h_strict' := h_strict h_mem h_one_mem h_lt
  linarith

/-! ## Upper-argmax selector and unconditional pointwise comparison

The previous `exists_dynamic_argmax_ge_sigma` gives existence of a
dynamic argmax weakly above the stage argmax under monotone $V_S$.
The `Classical.choose`-defined `σ_dyn V_S` might not pick this upper
argmax when the argmax set is non-singleton — Classical.choose is
arbitrary.

The fix below: define an *alternative* dynamic argmax selector
`σ_dyn_top V_S x a` = the supremum (= maximum, by closedness) of the
dynamic argmax set on `[0, 1]`. This is the *upper* dynamic argmax
and satisfies the pointwise `σ_dyn_top V_S x a ≥ p.σ x a`
*unconditionally* under monotone $V_S$. Under uniqueness of the
dynamic argmax (the canonical Berge route, e.g. from strict concavity
of the complete dynamic objective in $s$), `σ_dyn V_S = σ_dyn_top V_S`
pointwise, giving the
pointwise `σ_dyn V_S x a ≥ p.σ x a` for the project's
`Classical.choose`-defined `σ_dyn` as well. -/

/-- The set of dynamic Sender argmaxes on `[0, 1]` at `(x, a)`,
given continuation value `V_S`. -/
def dynamicArgmaxSet (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : Set ℝ :=
  {s | s ∈ Sanctions.I ∧
    IsMaxOn (fun s' => p.U_S x a s'
      + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
      Sanctions.I s}

theorem dynamicArgmaxSet_nonempty (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    (p.dynamicArgmaxSet V_S x a).Nonempty := by
  obtain ⟨s, hs_mem, hs_max⟩ := p.sender_arg_max_exists V_S x a
  exact ⟨s, hs_mem, hs_max⟩

theorem dynamicArgmaxSet_subset_I
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    p.dynamicArgmaxSet V_S x a ⊆ Sanctions.I :=
  fun _ h => h.1

theorem dynamicArgmaxSet_bddAbove
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    BddAbove (p.dynamicArgmaxSet V_S x a) := by
  refine ⟨1, ?_⟩
  intro s hs
  exact hs.1.2

/-- The dynamic argmax set is closed on `[0, 1]` (since it is the
preimage of `{sSup}` under the continuous Sender objective,
intersected with the closed interval). -/
theorem dynamicArgmaxSet_isClosed
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    IsClosed (p.dynamicArgmaxSet V_S x a) := by
  unfold dynamicArgmaxSet
  -- The set is the intersection of I with the preimage of a closed set
  -- under a continuous function. Concretely:
  -- {s | s ∈ I ∧ ∀ s' ∈ I, f s' ≤ f s}
  -- = {s | s ∈ I ∧ f s = sSup (f '' I)} (by IsMaxOn definition)
  have h_cont := p.sender_integrand_continuous_in_s V_S.continuous x a
  set M : ℝ := sSup ((fun s' => p.U_S x a s'
      + p.β_S * V_S (Sanctions.clipS' (p.F x s'))) '' Sanctions.I)
  -- Rewrite the set as I ∩ (objective ⁻¹' {M}), assuming we can identify IsMaxOn with f s = M.
  have h_set_eq : {s | s ∈ Sanctions.I ∧ IsMaxOn (fun s' => p.U_S x a s'
      + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
      Sanctions.I s}
    = Sanctions.I ∩ (fun s' => p.U_S x a s'
        + p.β_S * V_S (Sanctions.clipS' (p.F x s')))⁻¹' {M} := by
    ext s
    constructor
    · rintro ⟨hs_mem, hs_max⟩
      refine ⟨hs_mem, ?_⟩
      apply le_antisymm
      · exact le_csSup
          ((isCompact_Icc.image_of_continuousOn h_cont.continuousOn).bddAbove)
          ⟨s, hs_mem, rfl⟩
      · -- Show M ≤ f s via the fact that s is an argmax
        apply csSup_le
        · exact ⟨_, ⟨0, by simp [Sanctions.I], rfl⟩⟩
        · rintro y ⟨s', hs', rfl⟩
          exact hs_max hs'
    · rintro ⟨hs_mem, hs_eq⟩
      refine ⟨hs_mem, ?_⟩
      intro s' hs'
      have hs'_le : (fun s'' => p.U_S x a s''
          + p.β_S * V_S (Sanctions.clipS' (p.F x s''))) s' ≤ M :=
        le_csSup
          ((isCompact_Icc.image_of_continuousOn h_cont.continuousOn).bddAbove)
          ⟨s', hs', rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hs_eq
      simp only [hs_eq]
      exact hs'_le
  rw [h_set_eq]
  exact (isClosed_Icc).inter (isClosed_singleton.preimage h_cont)

/-- The *upper* dynamic argmax: the supremum of the dynamic argmax
set on `[0, 1]`. Well-defined since the set is non-empty closed
bounded. -/
noncomputable def σ_dyn_top
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  sSup (p.dynamicArgmaxSet V_S x a)

/-- The upper dynamic argmax is itself a dynamic argmax. -/
theorem σ_dyn_top_mem_dynamicArgmaxSet
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    p.σ_dyn_top V_S x a ∈ p.dynamicArgmaxSet V_S x a := by
  -- A non-empty closed bounded subset of ℝ contains its sSup.
  have h_ne := p.dynamicArgmaxSet_nonempty V_S x a
  have h_bdd := p.dynamicArgmaxSet_bddAbove V_S x a
  have h_closed := p.dynamicArgmaxSet_isClosed V_S x a
  -- IsClosed.csSup_mem (non-empty, BddAbove, IsClosed implies sSup ∈ set)
  exact h_closed.csSup_mem h_ne h_bdd

/-- The upper dynamic argmax is in `[0, 1]`. -/
theorem σ_dyn_top_mem_I
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    p.σ_dyn_top V_S x a ∈ Sanctions.I :=
  (p.σ_dyn_top_mem_dynamicArgmaxSet V_S x a).1

/-- The upper dynamic argmax is a maximizer of the dynamic Sender objective. -/
theorem σ_dyn_top_isMaxOn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    IsMaxOn (fun s' => p.U_S x a s'
      + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
      Sanctions.I (p.σ_dyn_top V_S x a) :=
  (p.σ_dyn_top_mem_dynamicArgmaxSet V_S x a).2

/-- **Every stage maximiser lies weakly below the greatest dynamic maximiser**
under monotone $V_S$ — selection-free. If `m ∈ [0, 1]` maximises the stage
payoff $s \mapsto U_S(x,a,s)$ on `[0, 1]`, then `m ≤ σ_dyn_top V_S x a`.
Economically: the greatest forward-looking sanction is at least every myopic
best response, not just the one the `Params` selector `σ` happens to pick, so
the dominance comparison does not depend on how a tied stage argmax is
resolved.

The comparison is against `σ_dyn_top`, the **greatest** dynamic maximiser, and
must stay so: "every stage maximiser ≤ every dynamic maximiser" is false under
`Monotone V_S` alone (a constant `V_S` with a tied stage argmax).

Rule 22: general in `F` (only `F_mono_s`). Selection-free form of
`σ_dyn_top_ge_sigma` (BH6.8, 2026-10-07): the selector `σ` is replaced by any
stage maximiser `m`; no hypothesis is added. -/
theorem stage_max_le_σ_dyn_top
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (h_V_S_mono : Monotone V_S) {x a m : ℝ}
    (hm : m ∈ Sanctions.I)
    (hmax : IsMaxOn (fun s => p.U_S x a s) Sanctions.I m) :
    m ≤ p.σ_dyn_top V_S x a := by
  -- The upper argmax is the sup of the argmax set, which contains
  -- a maximizer ≥ m by exists_dynamic_argmax_ge_of_stage_max.
  obtain ⟨sStar, hsStar_mem, hsStar_max, hsStar_ge⟩ :=
    p.exists_dynamic_argmax_ge_of_stage_max V_S h_V_S_mono hm hmax
  have h_in_set : sStar ∈ p.dynamicArgmaxSet V_S x a := ⟨hsStar_mem, hsStar_max⟩
  exact le_trans hsStar_ge
    (le_csSup (p.dynamicArgmaxSet_bddAbove V_S x a) h_in_set)

/-- **Unconditional pointwise `σ_dyn_top ≥ σ`** under monotone $V_S$.
This is the direct derivation of the paper-level
"$\sigma^{\rm dyn}_{V_S}\geq\sigma$" comparison for the
*upper-argmax* selector $\sigma^{\rm dyn,top}$, with no uniqueness
hypothesis.

General in `F`. Since BH6.8 (2026-10-07) a one-line σ-instance of the
selection-free `stage_max_le_σ_dyn_top` (`m := p.σ x a`); statement
unchanged. -/
theorem σ_dyn_top_ge_sigma
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (h_V_S_mono : Monotone V_S) (x a : ℝ) :
    p.σ x a ≤ p.σ_dyn_top V_S x a :=
  p.stage_max_le_σ_dyn_top V_S h_V_S_mono (p.σ_mem x a) (p.σ_isMaxOn_U_S x a)

/-- **At `β_S = 0` the greatest dynamic maximiser is the greatest stage
maximiser — with no uniqueness hypothesis.** For every continuation value
`V_S`, `σ_dyn_top V_S x a` is the supremum of the stage argmax set
`{s ∈ [0, 1] | s maximises U_S(x, a, ·) on [0, 1]}`. Economically: a Sender
that puts zero weight on the future picks the greatest myopic best response,
however the stage argmax is tied, whatever value it attaches to future states.

Rule 22: general in `F` (the transition term is multiplied by `β_S = 0`).
Selection-free sharpening of `σ_dyn_top_eq_σ_of_βS_zero`
(`Mechanism/ZeroDiscountSelector.lean`), which needs the stage argmax to be a
singleton (`huniq`) to identify the selector with `p.σ x a`; without `huniq`
what remains is this identity with the supremum of the stage argmax set
(BH6.8, 2026-10-07). -/
theorem σ_dyn_top_eq_sSup_stageArgmax_of_βS_zero (hβ : p.β_S = 0)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    p.σ_dyn_top V_S x a
      = sSup {s | s ∈ Sanctions.I ∧
          IsMaxOn (fun s' => p.U_S x a s') Sanctions.I s} := by
  unfold σ_dyn_top dynamicArgmaxSet
  simp only [hβ, zero_mul, add_zero]

/-! ## Pointwise $\sigma_{\rm dyn}\,V_S \geq \sigma$ under uniqueness

Under uniqueness of the dynamic argmax (a sufficient condition is strict
concavity of the *complete* dynamic Sender objective in the sanction; stage
concavity of $U_S$ alone is not sufficient — at $F(x,s) = s$, $\beta_S = 1/2$,
$U_S = -s^2$, $V_S(y) = 2y^2$ the complete objective is constant in $s$), the
`Classical.choose`-defined
$\sigma_{\rm dyn}\,V_S$ equals $\sigma_{\rm dyn}^{\rm top}\,V_S$, and
the pointwise comparison `σ_dyn V_S x a ≥ σ x a` follows. -/

/-- **Under uniqueness of the dynamic argmax**, the
`Classical.choose`-defined `σ_dyn V_S` agrees with the upper-argmax
`σ_dyn_top V_S` pointwise. -/
theorem σ_dyn_eq_σ_dyn_top_of_unique
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ)
    (h_unique : ∀ s₁ s₂, s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
      IsMaxOn (fun s' => p.U_S x a s'
        + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
        Sanctions.I s₁ →
      IsMaxOn (fun s' => p.U_S x a s'
        + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
        Sanctions.I s₂ → s₁ = s₂) :
    p.σ_dyn V_S x a = p.σ_dyn_top V_S x a := by
  apply h_unique
  · exact p.σ_dyn_mem V_S x a
  · exact p.σ_dyn_top_mem_I V_S x a
  · exact p.σ_dyn_isMaxOn V_S x a
  · exact p.σ_dyn_top_isMaxOn V_S x a

/-- **Pointwise `σ_dyn V_S x a ≥ σ x a`** under monotone $V_S$ plus
uniqueness of the dynamic argmax. This is the project's "Berge-route"
derivation of the load-bearing comparison hypothesis: the
$V_S$-monotonicity is the canonical economic primitive (derivable
from BellmanS cone preservation when the Sender integrand is
monotone), and uniqueness is the canonical sufficient condition for
the Classical.choose selector to land on the upper-argmax (typically
discharged from strict concavity of the complete dynamic objective in
$s$, or by a direct uniqueness proof). Stage strict concavity alone is
not such a discharge. -/
theorem σ_dyn_ge_sigma_of_unique
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (h_V_S_mono : Monotone V_S)
    (x a : ℝ)
    (h_unique : ∀ s₁ s₂, s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
      IsMaxOn (fun s' => p.U_S x a s'
        + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
        Sanctions.I s₁ →
      IsMaxOn (fun s' => p.U_S x a s'
        + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
        Sanctions.I s₂ → s₁ = s₂) :
    p.σ x a ≤ p.σ_dyn V_S x a := by
  rw [p.σ_dyn_eq_σ_dyn_top_of_unique V_S x a h_unique]
  exact p.σ_dyn_top_ge_sigma V_S h_V_S_mono x a

/-- Uniqueness of an argmax follows from strict monotonicity of the
objective on a chain: if `f` is strictly monotone on `I` then both
maximizers must equal the right endpoint. (A canonical sufficient
condition at concrete instantiations where the dynamic objective is
strictly monotone in $s$.) -/
theorem unique_argmax_of_strictMono
    {f : ℝ → ℝ} (h_strict : StrictMonoOn f Sanctions.I)
    {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Sanctions.I) (hs₂ : s₂ ∈ Sanctions.I)
    (h₁ : IsMaxOn f Sanctions.I s₁) (h₂ : IsMaxOn f Sanctions.I s₂) :
    s₁ = s₂ := by
  -- A strictly monotone function on a closed interval attains its
  -- maximum uniquely at the right endpoint; both maximizers equal 1.
  have h_one_mem : (1 : ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl _⟩
  -- Show s₁ = 1 and s₂ = 1
  have hs₁_eq_one : s₁ = 1 := by
    by_contra h_ne
    have h_lt : s₁ < 1 := lt_of_le_of_ne hs₁.2 h_ne
    have h_strict' := h_strict hs₁ h_one_mem h_lt
    have h_max : f 1 ≤ f s₁ := h₁ h_one_mem
    linarith
  have hs₂_eq_one : s₂ = 1 := by
    by_contra h_ne
    have h_lt : s₂ < 1 := lt_of_le_of_ne hs₂.2 h_ne
    have h_strict' := h_strict hs₂ h_one_mem h_lt
    have h_max : f 1 ≤ f s₂ := h₂ h_one_mem
    linarith
  rw [hs₁_eq_one, hs₂_eq_one]

/-! ## One-step wrapper: pointwise `σ_dyn ≥ σ` from integrand monotonicity + uniqueness

The dominance theorems in `DynamicLockIn` consume a load-bearing
pointwise hypothesis `p.σ x (α x) ≤ p.σ_dyn V_S x (α x)` on the basin.
This module already provides the two ingredients that derive it from
canonical primitives:

* `V_S_monotone_of_integrand_monotone` (from `Theory/Bellman/BellmanS`):
  monotone Sender stage payoff `U_S(·, α(·), s)` in `x` ⇒ `V_S α` monotone
  on the state space (via Banach cone preservation);
* `σ_dyn_ge_sigma_of_unique`: monotone `V_S` + uniqueness of the dynamic
  argmax ⇒ pointwise `σ x a ≤ σ_dyn V_S x a` for the
  `Classical.choose`-defined `σ_dyn`.

The wrapper below packages them in a single theorem, so the call site
can discharge the dominance theorems' pointwise hypothesis from the
primitive integrand-monotonicity + uniqueness alone. -/

/-- **Pointwise `σ ≤ σ_dyn V_S` from primitives.** Combines
`V_S_monotone_of_integrand_monotone` (the canonical Sender BCF
cone-preservation) with `σ_dyn_ge_sigma_of_unique` (the uniqueness-
route pointwise comparison) into a single discharge: under monotone
Sender stage payoff in `x` plus uniqueness of the dynamic argmax,
the project's `Classical.choose`-defined `σ_dyn (V_S α hα)` pointwise
dominates `σ`. -/
theorem pointwise_σ_dyn_ge_σ_from_integrand_monotone
    {α : ℝ → ℝ} (hα : Continuous α)
    (h_U_S_mono : ∀ s ∈ Sanctions.I, ∀ x ∈ Sanctions.S, ∀ y ∈ Sanctions.S,
      x ≤ y → p.U_S x (α x) s ≤ p.U_S y (α y) s)
    (h_unique : ∀ x a s₁ s₂, s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
      IsMaxOn (fun s' => p.U_S x a s'
        + p.β_S * (p.V_S α hα)
                    (Sanctions.clipS' (p.F x s')))
        Sanctions.I s₁ →
      IsMaxOn (fun s' => p.U_S x a s'
        + p.β_S * (p.V_S α hα)
                    (Sanctions.clipS' (p.F x s')))
        Sanctions.I s₂ → s₁ = s₂) :
    ∀ x a, p.σ x a ≤ p.σ_dyn (p.V_S α hα) x a := by
  intro x a
  -- Derive Monotone V_S from the integrand-monotone primitive.
  have h_V_S_mono_subtype :=
    p.V_S_monotone_of_integrand_monotone hα h_U_S_mono
  have h_V_S_mono : Monotone (p.V_S α hα) :=
    fun x y h => h_V_S_mono_subtype h
  exact p.σ_dyn_ge_sigma_of_unique (p.V_S α hα) h_V_S_mono x a (h_unique x a)

/-! ## §10 The lower dynamic argmax `σ_dyn_bot` (Issue 6 sibling)

The existing `σ_dyn_top` defined above is the *upper* element of the
dynamic argmax set. The paper's selector convention is the greatest
selector --- this is the Milgrom-Roberts 1990 upper-rationalizable
bound on a Vives 1990 lattice game, machine-checked at
`Foundations/VivesLattice.lean`. The referee's Issue 6 critique
flags that the selector convention has no typed mirror at the Lean
level: a reader cannot ask "what does the lower-selection counterpart
look like?" without finding the answer. The sibling defined below
fills the gap.

A second observation in the same Issue 6 critique is that under
`DynamicArgmaxUnique` the selector debate is structurally moot. Stage
Assumption 3 alone does not establish this predicate: the continuation
term can offset stage curvature. The
`extremal_selectors_coincide_under_DynamicArgmaxUnique` lemma below
records the correctly conditioned statement. -/

/-- The dynamic argmax set is bounded below by `0`. Companion to
`dynamicArgmaxSet_bddAbove`. -/
theorem dynamicArgmaxSet_bddBelow
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    BddBelow (p.dynamicArgmaxSet V_S x a) := by
  refine ⟨0, ?_⟩
  intro s hs
  exact hs.1.1

/-- The *lower* dynamic argmax: the infimum of the dynamic argmax set
on `[0, 1]`. Well-defined since the set is non-empty closed bounded.
Sibling of `σ_dyn_top`. -/
noncomputable def σ_dyn_bot
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) : ℝ :=
  sInf (p.dynamicArgmaxSet V_S x a)

/-- The lower dynamic argmax is itself a dynamic argmax. Mirror of
`σ_dyn_top_mem_dynamicArgmaxSet`. -/
theorem σ_dyn_bot_mem_dynamicArgmaxSet
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    p.σ_dyn_bot V_S x a ∈ p.dynamicArgmaxSet V_S x a := by
  have h_ne := p.dynamicArgmaxSet_nonempty V_S x a
  have h_bdd := p.dynamicArgmaxSet_bddBelow V_S x a
  have h_closed := p.dynamicArgmaxSet_isClosed V_S x a
  exact h_closed.csInf_mem h_ne h_bdd

/-- The lower dynamic argmax is in `[0, 1]`. Mirror of
`σ_dyn_top_mem_I`. -/
theorem σ_dyn_bot_mem_I
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    p.σ_dyn_bot V_S x a ∈ Sanctions.I :=
  (p.σ_dyn_bot_mem_dynamicArgmaxSet V_S x a).1

/-- The lower dynamic argmax is a maximizer of the dynamic Sender
objective. Mirror of `σ_dyn_top_isMaxOn`. -/
theorem σ_dyn_bot_isMaxOn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    IsMaxOn (fun s' => p.U_S x a s'
      + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
      Sanctions.I (p.σ_dyn_bot V_S x a) :=
  (p.σ_dyn_bot_mem_dynamicArgmaxSet V_S x a).2

/-- **Extremal-selector dichotomy.** The lower dynamic argmax never
exceeds the upper dynamic argmax. Balbus-Reffett-Wozny 2013 Lemma 3.1
specialized to the 1-D Sender-action slice. -/
theorem σ_dyn_bot_le_σ_dyn_top
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ) :
    p.σ_dyn_bot V_S x a ≤ p.σ_dyn_top V_S x a := by
  have h_top_mem : p.σ_dyn_top V_S x a ∈ p.dynamicArgmaxSet V_S x a :=
    p.σ_dyn_top_mem_dynamicArgmaxSet V_S x a
  exact csInf_le (p.dynamicArgmaxSet_bddBelow V_S x a) h_top_mem

/-- **BRW 2013 Corollary 3.1 collapse-on-uniqueness (per-(x, a) form).**
When the dynamic argmax is a singleton at `(x, a)`, the upper and lower
selectors coincide there. If the complete dynamic objective is
strictly concave (or otherwise has a unique maximizer) at every
`(V_S, x, a)` triple, the selector debate is structurally moot at every
basin state. Uniform strict concavity of the stage payoff `U_S` alone
does not establish this.

The hypothesis is the per-`(x, a)` unfolding of `DynamicArgmaxUnique`
(defined in `Theory/Equilibrium/SelectionRobust.lean`), inlined here to
avoid the upstream import. The named-`DynamicArgmaxUnique`-hypothesis
form is delivered by the carrier-level corollary in
`Theory/Equilibrium/SelectorBistability.lean`.

This is the formal record that the referee's Issue 6 critique of the
selector convention dissolves under the explicitly stated
dynamic-argmax uniqueness condition: both extremal selectors agree on
the unique argmax. -/
theorem extremal_selectors_coincide_at_unique_argmax
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ)
    (h_unique : ∀ s₁ s₂, s₁ ∈ Sanctions.I → s₂ ∈ Sanctions.I →
      IsMaxOn (fun s' => p.U_S x a s'
        + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
        Sanctions.I s₁ →
      IsMaxOn (fun s' => p.U_S x a s'
        + p.β_S * V_S (Sanctions.clipS' (p.F x s')))
        Sanctions.I s₂ → s₁ = s₂) :
    p.σ_dyn_bot V_S x a = p.σ_dyn_top V_S x a := by
  -- σ_dyn_bot and σ_dyn_top are both maximizers (by σ_dyn_bot_isMaxOn,
  -- σ_dyn_top_isMaxOn) in Sanctions.I (by σ_dyn_bot_mem_I,
  -- σ_dyn_top_mem_I), so uniqueness forces them equal.
  exact h_unique (p.σ_dyn_bot V_S x a) (p.σ_dyn_top V_S x a)
    (p.σ_dyn_bot_mem_I V_S x a)
    (p.σ_dyn_top_mem_I V_S x a)
    (p.σ_dyn_bot_isMaxOn V_S x a)
    (p.σ_dyn_top_isMaxOn V_S x a)

/-! ## §11 Theorem 2 paper-facing wrapper (Issue 4)

The JET referee's Issue 4 critique observed that the paper's Theorem 2
(statewise dynamic-over-myopic Sender-response dominance) compared
`σ(x, α_M(x)) ≤ σ_dyn_top V_S x (α(x))` at *different* α's
(the myopic equilibrium's `α_M` on the left, the dynamic equilibrium's
`α` on the right), and that the proof in App A hand-waved the
`σ` side without establishing a monotone-argmax-in-parameter bound on
it.

The clean restatement, machine-checked below, is the **same-α form**:
at any fixed Target policy `α : ℝ → ℝ`, and at any monotone Sender
continuation value `V_S`, the dynamic Sender response upper bound
`σ_dyn_top V_S x (α x)` dominates the static-equilibrium Sender
response `σ x (α x)`. Both sides use the *same* `α`; the comparison
is between the dynamic-objective argmax (which adds the monotone
continuation increment `β_S · V_S(F(x, s))`) and the static-objective
argmax. The result is a direct application of Milgrom-Shannon
single-crossing on the dynamic Sender objective in `s` parameterised
by the continuation value `V_S`: adding a monotone non-decreasing
term to a continuous objective shifts the upper argmax weakly up.

This is the Milgrom-Shannon kernel; the paper's "different α"
comparison is recovered as a downstream corollary, but is **not** the
substantive Theorem 2 content. -/

/-- **Theorem 2 paper-facing wrapper (Issue 4).** Same-α Milgrom-Shannon
form of the dynamic-over-myopic Sender-response dominance: at any
fixed Target policy `α : ℝ → ℝ`, monotone Sender continuation value
`V_S` shifts the upper Sender argmax weakly upward. Concretely, the
static stage selector `σ x (α x)` is dominated by the upper dynamic
argmax `σ_dyn_top V_S x (α x)` pointwise in `x`.

The single-crossing property powering this comparison is
`dynamic_minus_stage_mono_in_s`: the increment from the static
Sender objective to the dynamic one is `β_S · V_S(F(x, ·))`, which is
monotone non-decreasing in `s` because `β_S ≥ 0`, `V_S` is monotone
non-decreasing, and `F(x, ·)` is monotone non-decreasing by the `Params`
field `p.F_mono_s` — see `sender_continuation_mono_in_s`. Milgrom-Shannon
Theorem 4 then delivers monotonicity of the upper argmax.

Rule 22: **no functional form of `F` is used anywhere in this chain.**
(Corrected 2026-09-01 — this passage previously asserted
`F(x, ·) = (1-δ)·x + δ·s`, the affine instance, which neither the statement
nor the proof requires.)

This is the **canonical paper-facing Theorem 2** for the Round-1
revision of the JET manuscript. The proof is a one-line delegation
to `σ_dyn_top_ge_sigma` specialised at `a = α x`. -/
theorem theorem2_dynamic_dominates_myopic_at_same_alpha
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (h_V_S_mono : Monotone V_S)
    (α : ℝ → ℝ) (x : ℝ) :
    p.σ x (α x) ≤ p.σ_dyn_top V_S x (α x) :=
  p.σ_dyn_top_ge_sigma V_S h_V_S_mono x (α x)

/-- **Theorem 2 paper-facing wrapper, on-basin form.** Restricts the
universal `x : ℝ` quantifier of `theorem2_dynamic_dominates_myopic_at_same_alpha`
to a hypothesis `x ∈ basin` for paper-facing legibility. The proof
ignores the basin hypothesis (the statewise bound is unconditional in
`x` at the abstract level; the basin constraint becomes load-bearing
only when one needs `V_S` membership in the Sender-carrier class). -/
theorem theorem2_dynamic_dominates_myopic_at_same_alpha_on_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (h_V_S_mono : Monotone V_S)
    (α : ℝ → ℝ) {xT xS : ℝ} {x : ℝ}
    (_hx : x ∈ Set.Icc (max xT xS) (1 : ℝ)) :
    p.σ x (α x) ≤ p.σ_dyn_top V_S x (α x) :=
  p.theorem2_dynamic_dominates_myopic_at_same_alpha V_S h_V_S_mono α x

/-! ## Action-antitonicity of the upper dynamic Sender selector

The dynamic analogue of the stage theorem
`sigma_antitoneOn_a_of_U_S_decreasing_differences`
(`DifferentPolicyComparator.lean`): the *greatest* dynamic Sender
selector `σ_dyn_top V_S x ·` is `AntitoneOn` in the action `a`,
derived from the existing decreasing-differences primitive on the
Sender stage payoff `U_S(x, ·, ·)` in `(s, a)`. -/

/-- **Round-1 dynamic σ-antitone discharger.** For a fixed state `x`
and a fixed Sender continuation value `V_S`, suppose:

* `U_S(x, ·, ·)` has *decreasing differences* in `(s, a)` on
  `Sanctions.I × Sanctions.I` (`hDD`: the marginal Sender stage gain
  from more sanctions falls as the Target complies more — paper:
  `∂²U_S/∂s∂a ≤ 0`);
* at every action `a ∈ Sanctions.I` the *upper dynamic* Sender argmax
  `σ_dyn_top V_S x a` is *strictly* unique on `[0, 1]` against the
  dynamic objective (`h_unique`: no tie with any other feasible
  sanction once the discounted continuation increment
  `β_S · V_S(F(x, ·))` is included).

Then the greatest dynamic Sender selector `σ_dyn_top V_S x ·` is
`AntitoneOn` on `Sanctions.I`: raising the Target's compliance lowers
the Sender's forward-looking sanction response.

The proof is the dynamic port of
`sigma_antitoneOn_a_of_U_S_decreasing_differences`. The only
non-mechanical step is the decreasing-differences *transfer*: the
dynamic objective `U_S(x, a, s) + β_S · V_S(F(x, s))` differs from the
stage objective `U_S(x, a, s)` only by a term **independent of `a`**,
so that term cancels in the `(s; a)` cross-difference and decreasing
differences passes through verbatim from `hDD`. The Rule-1 coupling
`σ_dyn_top_isMaxOn` + membership `σ_dyn_top_mem_I` then feed the
Foundations lemma
`Sanctions.MilgromShannon.argmax_antitone_of_decreasingDifferencesOn_strict`. -/
theorem σ_dyn_top_antitoneOn_a_of_SenderActionDD
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (x : ℝ)
    (hDD :
      Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
        (fun s a => p.U_S x a s))
    (h_unique :
      ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I, s ≠ p.σ_dyn_top V_S x a →
        p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s))
          < p.U_S x a (p.σ_dyn_top V_S x a)
            + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x a)))) :
    AntitoneOn (fun a => p.σ_dyn_top V_S x a) Sanctions.I := by
  intro a₁ ha₁ a₂ ha₂ ha_le
  -- Decreasing-differences TRANSFER: the continuation increment
  -- `β_S · V_S(F(x, s))` does not depend on `a`, so it cancels in the
  -- (s; a) cross-difference and DD passes through verbatim from `hDD`.
  have hDD_dyn :
      Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
        (fun s a => p.U_S x a s
          + p.β_S * V_S (Sanctions.clipS' (p.F x s))) := by
    intro s₁ s₂ t t' hs₁ hs₂ hs_le ht ht' htt
    have h := hDD hs₁ hs₂ hs_le ht ht' htt
    simp only
    linarith
  -- Recover the maximizer facts from `σ_dyn_top_isMaxOn` (Rule-1 coupling).
  have hmax_a₁ : ∀ s ∈ Sanctions.I,
      p.U_S x a₁ s + p.β_S * V_S (Sanctions.clipS' (p.F x s))
        ≤ p.U_S x a₁ (p.σ_dyn_top V_S x a₁)
          + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x a₁))) :=
    fun s hs => p.σ_dyn_top_isMaxOn V_S x a₁ hs
  have hmax_a₂ : ∀ s ∈ Sanctions.I,
      p.U_S x a₂ s + p.β_S * V_S (Sanctions.clipS' (p.F x s))
        ≤ p.U_S x a₂ (p.σ_dyn_top V_S x a₂)
          + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x a₂))) :=
    fun s hs => p.σ_dyn_top_isMaxOn V_S x a₂ hs
  -- Membership of the upper dynamic argmax in I.
  have hin_a₁ : p.σ_dyn_top V_S x a₁ ∈ Sanctions.I := p.σ_dyn_top_mem_I V_S x a₁
  have hin_a₂ : p.σ_dyn_top V_S x a₂ ∈ Sanctions.I := p.σ_dyn_top_mem_I V_S x a₂
  -- Strict-uniqueness at each action.
  have hs_strict_a₁ := h_unique a₁ ha₁
  have hs_strict_a₂ := h_unique a₂ ha₂
  -- Apply the Foundations dual MS Theorem 4' to the dynamic objective
  -- `f(s, a) := U_S(x, a, s) + β_S · V_S(F(x, s))`.
  exact Sanctions.MilgromShannon.argmax_antitone_of_decreasingDifferencesOn_strict
    hDD_dyn ha_le ha₁ ha₂ hin_a₁ hin_a₂ hs_strict_a₁ hs_strict_a₂

/-! ## Step 2 — isotonicity of the upper dynamic Sender selector in `V_S`

The "slaved-existence" route raises the Sender continuation value
`V_S` and needs the upper dynamic Sender selector `σ_dyn_top V_S` to
move **upward** with it. The selector is the greatest argmax of the
dynamic objective `s ↦ U_S(x, a, s) + β_S · V_S(clipS'(F(x, s)))`.
Raising `V_S` to `V_S'` adds the term
`β_S · (V_S' − V_S)(clipS'(F(x, s)))` to the objective; when that
added term is **monotone non-decreasing in the choice `s`**, the
Milgrom-Shannon strong-set-order shift moves the greatest argmax
weakly up. This is the exact dual of the Step-1 antitonicity lemma:
there the added term was antitone in `a` (decreasing differences),
here it is monotone in `s` (an increasing-difference / single-crossing
shift in `V_S`). -/

/-- **Step 2 — `σ_dyn_top` isotone in `V_S` under increment-monotonicity.**

For two Sender continuation values `V_S ≤ V_S'` (pointwise BCF order),
suppose the *increment composed through the basin transition*
`s ↦ (V_S' − V_S)(clipS'(F(x, s)))` is monotone non-decreasing on the
sanction set `[0, 1]` (`h_incr_mono`: the extra continuation value the
higher Sender value attaches to a transition rises with the sanction
level). Then the greatest dynamic Sender selector rises weakly:
`σ_dyn_top V_S x a ≤ σ_dyn_top V_S' x a` for every state `x` and
action `a`.

The increment-monotonicity hypothesis is stated **directly over the
BCF data** (Rule-14 safe: it is a `MonotoneOn` of a concrete function
built from the two value functions, the clip and the transition — not
an opaque `Prop`) and as a plain theorem parameter (Rule 3: no new
`Params` field, no new Postulate). The result is fully parametric in
`(p, V_S, V_S', x, a)` (Rule 5).

The pointwise order `_h_le : ∀ y, V_S y ≤ V_S' y` is the *economic
framing* premise (we compare a lower Sender value to a higher one);
it is **not** logically consumed by the argmax-shift argument, which
needs only that the *increment* is monotone in the choice. It is kept
in the signature (underscore-prefixed) so the comparison the theorem
makes is legible, per the slaved-existence route's `V_S ≤ V_S'` step;
the substantive content lives entirely in `h_incr_mono`.

The proof transfers the increment monotonicity (scaled by `β_S ≥ 0`)
into `MonotoneOn` of the *difference of dynamic objectives*, applies
the Milgrom-Shannon `isMaxOn_max_of_monotone_diff` to conclude
`max(σ_dyn_top V_S x a, σ_dyn_top V_S' x a)` is itself an argmax of
the `V_S'`-objective, hence lies in its argmax set and is therefore
`≤` the sup `σ_dyn_top V_S' x a`; since
`σ_dyn_top V_S x a ≤ max(…)`, the claim follows. -/
theorem σ_dyn_top_monotone_in_V_S_of_monotoneDifference
    (V_S V_S' : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (_h_le : ∀ y, V_S y ≤ V_S' y)
    (x a : ℝ)
    (h_incr_mono :
      MonotoneOn (fun s => V_S' (Sanctions.clipS' (p.F x s))
                            - V_S (Sanctions.clipS' (p.F x s)))
        Sanctions.I) :
    p.σ_dyn_top V_S x a ≤ p.σ_dyn_top V_S' x a := by
  -- Abbreviations for the two dynamic objectives.
  set f : ℝ → ℝ := fun s => p.U_S x a s
      + p.β_S * V_S (Sanctions.clipS' (p.F x s)) with hf
  set g : ℝ → ℝ := fun s => p.U_S x a s
      + p.β_S * V_S' (Sanctions.clipS' (p.F x s)) with hg
  -- The difference of dynamic objectives equals `β_S · (increment)`,
  -- which is monotone non-decreasing on `[0,1]` (β_S ≥ 0).
  have hβ : 0 ≤ p.β_S := p.β_S_mem.1
  have h_diff_mono : MonotoneOn (fun s => g s - f s) Sanctions.I := by
    have h_simp : (fun s : ℝ => g s - f s)
        = (fun s : ℝ => p.β_S
            * (V_S' (Sanctions.clipS' (p.F x s))
               - V_S (Sanctions.clipS' (p.F x s)))) := by
      funext s; simp only [hf, hg]; ring
    rw [h_simp]
    intro s₁ hs₁ s₂ hs₂ hle
    exact mul_le_mul_of_nonneg_left (h_incr_mono hs₁ hs₂ hle) hβ
  -- The two upper selectors are argmaxes of their respective objectives.
  have h_f_max : IsMaxOn f Sanctions.I (p.σ_dyn_top V_S x a) :=
    p.σ_dyn_top_isMaxOn V_S x a
  have h_g_max : IsMaxOn g Sanctions.I (p.σ_dyn_top V_S' x a) :=
    p.σ_dyn_top_isMaxOn V_S' x a
  have h_f_mem : p.σ_dyn_top V_S x a ∈ Sanctions.I := p.σ_dyn_top_mem_I V_S x a
  have h_g_mem : p.σ_dyn_top V_S' x a ∈ Sanctions.I := p.σ_dyn_top_mem_I V_S' x a
  -- `max` of the two selectors is itself an argmax of the `V_S'` objective.
  have h_max_max : IsMaxOn g Sanctions.I
      (max (p.σ_dyn_top V_S x a) (p.σ_dyn_top V_S' x a)) :=
    isMaxOn_max_of_monotone_diff h_diff_mono h_f_mem h_g_mem h_f_max h_g_max
  have h_max_mem : max (p.σ_dyn_top V_S x a) (p.σ_dyn_top V_S' x a) ∈ Sanctions.I :=
    Sanctions.max_mem_I h_f_mem h_g_mem
  -- Hence `max(…)` lies in the `V_S'` dynamic argmax set, so it is
  -- `≤` the sup `σ_dyn_top V_S'`.
  have h_in_set : max (p.σ_dyn_top V_S x a) (p.σ_dyn_top V_S' x a)
      ∈ p.dynamicArgmaxSet V_S' x a := ⟨h_max_mem, h_max_max⟩
  have h_max_le : max (p.σ_dyn_top V_S x a) (p.σ_dyn_top V_S' x a)
      ≤ p.σ_dyn_top V_S' x a :=
    le_csSup (p.dynamicArgmaxSet_bddAbove V_S' x a) h_in_set
  exact le_trans (le_max_left _ _) h_max_le

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
