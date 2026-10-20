/-
Sanctions/Theory/Certificates/SubpivotChordNecessity.lean

**What P5 costs, in any economy (2026-08-13).**

`SenderPersistencePackage.sender_subpivot_chord` — P5, the transition-adjusted
sub-pivot chord — supplies the *level* half of persistence: it is what puts the
Sender's greatest response at or above the pivot. This file identifies exactly
what it demands of the primitives, with **no functional form, no numerics, and
no restriction on the transition `F`**.

## The statement

`subpivot_chord_forces_static_response_ge_pivot`: if the chord holds over
`[0, P]` at state `x` and compliance `a`, then `P ≤ p.σ x a`.

`p.σ` is the Sender's *stage* argmax — a `Params` field coupled to `U_S` by
`σ_isMaxOn_U_S`, so it is an optimization result, not a chosen function. Hence:

> **P5 implies the Sender's own static optimum already lies at or above the
> pivot.**

One direction only. P5 is strictly stronger than that screen: it must also cover
the continuation allowance `β_S · K_S · dist(F x s₁, F x s₂)`, which the screen
does not see. `quadSender_chord_iff` below makes the gap exact for the quadratic
family — the screen is P5 at allowance zero. So P5 *front-loads* the level half
of persistence into the stage payoff; it is not merely the static condition.

The proof is three lines and uses nothing but that coupling: the chord makes
`U_S x a ·` strictly increasing across `[0, P]`, so no point below `P` can
maximise it, so the maximiser is at or above `P`.

## Why this is the useful form

It converts a hypothesis about *chords of the stage payoff* into a statement
about an object the model already carries — and it is checkable at any candidate
economy by evaluating one `Params` field, with no equilibrium, no value
function, and no fixed point. That makes it a *screen*: an economy failing it
cannot support the persistence route, whatever is true of its equilibria.

Two corollaries sharpen it.

* `subpivot_chord_at_top_forces_corner` — at `x = 1` with pivot `1`, P5 forces
  `p.σ 1 a = 1`. **So P5 pins the sanction to the corner at the top state.** It
  says nothing whatever about any `x < 1`: the theorem above constrains `σ` only
  through the pivot at that same state. An equilibrium path started below the
  top is therefore free to be interior and strictly rising at every finite date,
  with the corner only as its limit. "Persistence forces sanctions equal to one
  at every date" does not follow from P5. That leaves untouched the separate
  fact that the currently constructed witness `persistence_generalF_corner` *is*
  flat at one — flatness is a property of that witness, not a consequence of the
  hypothesis.

* `SenderPersistencePackage.static_response_ge_pivot` — the package-level
  version: every persistence package forces
  `max x (max xT xS) ≤ p.σ x (D.α_on V_T V_S x)` at every basin state and every
  carrier pair. This is the form to check a candidate witness against. Since
  round BJ1.3 (2026-10-07) P5 is stated in pivot-star form on the basin
  `[max xT xS, 1]`, so the screen reads the star form
  (`subpivot_star_chord_forces_static_response_ge_pivot`, which the pairwise
  statement implies) and holds on the basin rather than on `[xS, 1]`.

## Rule compliance

**Rule 3.** No new assumption anywhere. The package-level screen takes no
hypothesis beyond the package itself: `0 ≤ K_S` is *derived* from P2 and carrier
nonemptiness (`ValueLipschitzWith.nonneg`), not assumed.
**Rule 5.** Parametric first: general `p : Params`, arbitrary `P`. The
mechanism-witness refutation in
`Examples/CoupledRoute/LowDeltaSubpivotChordObstruction.lean` is a corollary.
**Rule 19.** Stays in `Theory/` — it mentions `Params` throughout and is
project-specific, not external theory.
**Rule 22.** General `F`. The transition enters only through `dist ≥ 0`, so the
result holds for every admissible transition, affine or not.
-/

import Sanctions.Theory.Certificates.SenderPersistencePackage

namespace Sanctions

open Set

noncomputable section

namespace AbstractGame
namespace Params

/-! ## The necessary condition -/

/-- **P5 forces the Sender's static response up to the pivot.**

If, at state `x` and compliance `a`, every chord of the Sender stage payoff over
`[0, P]` strictly exceeds the transition-adjusted continuation allowance, then
the Sender's stage argmax `p.σ x a` lies at or above `P`.

The chord makes `U_S x a ·` strictly increasing on `[0, P]`; `σ x a` maximises it
on `[0,1]` (`σ_isMaxOn_U_S`); a maximiser cannot sit strictly below `P` when the
payoff is still rising there. -/
theorem subpivot_chord_forces_static_response_ge_pivot
    (p : Params) {K_S x a P : ℝ}
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hKS : 0 ≤ K_S)
    (hchord : ∀ s₁ ∈ Set.Icc (0 : ℝ) P, ∀ s₂ ∈ Set.Icc (0 : ℝ) P, s₁ < s₂ →
      p.β_S * K_S *
          dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x s₂))
        < p.U_S x a s₂ - p.U_S x a s₁) :
    P ≤ p.σ x a := by
  by_contra hcon'
  have hcon : p.σ x a < P := not_le.mp hcon'
  obtain ⟨hσ0, hσ1⟩ := p.σ_mem x a
  have hstep :=
    hchord (p.σ x a) ⟨hσ0, hcon.le⟩ P ⟨hP0, le_rfl⟩ hcon
  have hnn :
      0 ≤ p.β_S * K_S *
        dist (Sanctions.clipS' (p.F x (p.σ x a))) (Sanctions.clipS' (p.F x P)) :=
    mul_nonneg (mul_nonneg p.β_S_mem.1 hKS) dist_nonneg
  have hmax : p.U_S x a P ≤ p.U_S x a (p.σ x a) :=
    p.σ_isMaxOn_U_S x a (Set.mem_Icc.mpr ⟨hP0, hP1⟩)
  linarith

/-- **The star chord forces the Sender's static response up to the pivot**
(round BJ1.3, 2026-10-07). If, at state `x` and compliance `a`, moving from every
sanction below `P` up to `P` gains more stage payoff than the transition-adjusted
continuation allowance, then the Sender's stage argmax `p.σ x a` lies at or above
`P`.

This is the form P5 takes since round BJ1.3, and it is all the screen ever used:
the proof of `subpivot_chord_forces_static_response_ge_pivot` compares the argmax
only with `P`. The pairwise chord implies it (instantiate the upper sanction at
`P`). General in `F`: the transition enters only through `dist ≥ 0`. -/
theorem subpivot_star_chord_forces_static_response_ge_pivot
    (p : Params) {K_S x a P : ℝ}
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hKS : 0 ≤ K_S)
    (hstar : ∀ s₁ ∈ Set.Ico (0 : ℝ) P,
      p.β_S * K_S *
          dist (Sanctions.clipS' (p.F x s₁)) (Sanctions.clipS' (p.F x P))
        < p.U_S x a P - p.U_S x a s₁) :
    P ≤ p.σ x a := by
  by_contra hcon'
  have hcon : p.σ x a < P := not_le.mp hcon'
  obtain ⟨hσ0, -⟩ := p.σ_mem x a
  have hstep := hstar (p.σ x a) ⟨hσ0, hcon⟩
  have hnn :
      0 ≤ p.β_S * K_S *
        dist (Sanctions.clipS' (p.F x (p.σ x a))) (Sanctions.clipS' (p.F x P)) :=
    mul_nonneg (mul_nonneg p.β_S_mem.1 hKS) dist_nonneg
  have hmax : p.U_S x a P ≤ p.U_S x a (p.σ x a) :=
    p.σ_isMaxOn_U_S x a (Set.mem_Icc.mpr ⟨hP0, hP1⟩)
  linarith

/-- **At the top state, P5 pins the sanction to the corner — and only there.**

With pivot `1`, the theorem above gives `1 ≤ p.σ 1 a`, and `σ` is feasible, so
`p.σ 1 a = 1`.

This is the whole of P5's corner content. Nothing here constrains `p.σ x a` for
`x < 1`, because the pivot at state `x` is `max x (max xT xS)`, not `1`. -/
theorem subpivot_chord_at_top_forces_corner
    (p : Params) {K_S a : ℝ} (hKS : 0 ≤ K_S)
    (hchord : ∀ s₁ ∈ Set.Icc (0 : ℝ) 1, ∀ s₂ ∈ Set.Icc (0 : ℝ) 1, s₁ < s₂ →
      p.β_S * K_S *
          dist (Sanctions.clipS' (p.F 1 s₁)) (Sanctions.clipS' (p.F 1 s₂))
        < p.U_S 1 a s₂ - p.U_S 1 a s₁) :
    p.σ 1 a = 1 :=
  le_antisymm (p.σ_mem 1 a).2
    (subpivot_chord_forces_static_response_ge_pivot p zero_le_one le_rfl hKS hchord)


/-! ## The design screen: which economies can pay P5's price

The theorem above is a *necessary* condition, so it doubles as a search
instrument. For the quadratic Sender stage payoff — the shape every witness in
this development uses — it reduces to one inequality among the coefficients,
which is what makes locating an admissible witness a calculation rather than a
sweep. -/

/-- **The quadratic Sender stage payoff family.**

`c` is the own-action curvature `-∂²U_S/∂s²`, `r` the rally cross-partial
`∂²U_S/∂s∂x`, `u0` the sanction intercept, `w` the placation cross-partial
`-∂²U_S/∂s∂a`, and `q` the state stake. -/
noncomputable def quadSenderPayoff (c r u0 w q x a s : ℝ) : ℝ :=
  a - (c / 2) * s ^ 2 - s * (u0 + w * a - r * x) + q * x

/-- The unconstrained maximiser of `quadSenderPayoff` in the sanction. -/
noncomputable def quadSenderVertex (c r u0 w x a : ℝ) : ℝ :=
  (r * x - u0 - w * a) / c

/-- **The screen, in coefficients.**

The Sender's unconstrained static optimum clears the inherited state exactly when
the *rally-minus-curvature margin* `r - c` covers the intercept plus the placated
compliance. Combined with `subpivot_chord_forces_static_response_ge_pivot`, this
is a necessary condition on any economy whose persistence route is to close at
pivot `x` — see `quadSenderVertex_ge_state_of_clip_ge` for the bridge from the
clipped response, which needs `0 < x` (at `x = 0` the clip floor satisfies
`x ≤ σ` while the vertex sits below zero). -/
theorem quadSenderVertex_ge_state_iff
    {c r u0 w x a : ℝ} (hc : 0 < c) :
    x ≤ quadSenderVertex c r u0 w x a ↔ u0 + w * a ≤ (r - c) * x := by
  rw [quadSenderVertex, le_div_iff₀ hc]
  constructor <;> intro h <;> nlinarith


/-- **The bridge from the clipped response to the vertex.**

If the *clipped* static response reaches the state, so does the unclipped vertex
— provided `0 < x`. At `x = 0` the implication fails: the clip floor gives
`0 ≤ σ` for free while the vertex may sit strictly below zero. -/
theorem quadSenderVertex_ge_state_of_clip_ge
    {c r u0 w x a : ℝ} (hx : 0 < x)
    (hclip : x ≤ max 0 (min 1 (quadSenderVertex c r u0 w x a))) :
    x ≤ quadSenderVertex c r u0 w x a := by
  rcases max_cases (0 : ℝ) (min 1 (quadSenderVertex c r u0 w x a)) with
    ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at hclip; linarith
  · rw [he] at hclip
    exact le_trans hclip (min_le_right _ _)

/-- **P5 for the quadratic family, exactly.**

For curvature `c > 0` and a nondegenerate pivot `P > 0`, the chord condition at
allowance constant `C` over `[0, P]` holds **iff**

  `C ≤ r·x - u0 - w·a - c·P`.

The right side is `c · (vertex - P)`: the curvature times the gap between the
Sender's unconstrained optimum and the pivot. So P5 is the vertex screen
*strengthened by the continuation allowance* — at `C = 0` the two coincide, and
for `C = β_S·K_S·δ > 0` the vertex must clear the pivot by `C/c`. This is the
exact form the necessary condition above approximates. -/
theorem quadSender_chord_iff
    {c r u0 w q x a P C : ℝ} (hc : 0 < c) (hP : 0 < P) :
    (∀ s₁ ∈ Set.Icc (0 : ℝ) P, ∀ s₂ ∈ Set.Icc (0 : ℝ) P, s₁ < s₂ →
        C * (s₂ - s₁) < quadSenderPayoff c r u0 w q x a s₂
                          - quadSenderPayoff c r u0 w q x a s₁)
      ↔ C ≤ r * x - u0 - w * a - c * P := by
  have hexp : ∀ s₁ s₂ : ℝ,
      quadSenderPayoff c r u0 w q x a s₂ - quadSenderPayoff c r u0 w q x a s₁
        = (s₂ - s₁) * ((r * x - u0 - w * a) - (c / 2) * (s₁ + s₂)) := by
    intro s₁ s₂; unfold quadSenderPayoff; ring
  constructor
  · intro h
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have ht0 : 0 < min P (2 * ε / c) := lt_min hP (by positivity)
    have htP : min P (2 * ε / c) ≤ P := min_le_left _ _
    have hte : min P (2 * ε / c) ≤ 2 * ε / c := min_le_right _ _
    have hct : c * min P (2 * ε / c) ≤ 2 * ε := by
      have := (le_div_iff₀ hc).mp hte
      linarith
    have hstep := h (P - min P (2 * ε / c)) ⟨by linarith, by linarith⟩
      P ⟨hP.le, le_rfl⟩ (by linarith)
    rw [hexp] at hstep
    have hdiv : C < (r * x - u0 - w * a) - (c / 2) *
        ((P - min P (2 * ε / c)) + P) := by
      refine lt_of_mul_lt_mul_right ?_ ht0.le
      calc C * min P (2 * ε / c)
          = C * (P - (P - min P (2 * ε / c))) := by ring
        _ < (P - (P - min P (2 * ε / c))) *
              ((r * x - u0 - w * a) - (c / 2) *
                ((P - min P (2 * ε / c)) + P)) := hstep
        _ = ((r * x - u0 - w * a) - (c / 2) *
              ((P - min P (2 * ε / c)) + P)) * min P (2 * ε / c) := by ring
    linarith
  · intro h s₁ hs₁ s₂ hs₂ hlt
    rw [hexp]
    have hs1P : s₁ < P := lt_of_lt_of_le hlt hs₂.2
    have hbig : C < (r * x - u0 - w * a) - (c / 2) * (s₁ + s₂) := by
      nlinarith [hs₂.2, hs1P]
    nlinarith [hlt, hbig]

/-! ## The package-level screen -/

variable {p : Params}

/-- **Every persistence package forces the static Sender response to the pivot.**

At every basin state `x ∈ [max xT xS, 1]` and every carrier pair, the Sender's
stage argmax against the carrier's Target policy lies at or above the pivot
`max x (max xT xS)`.

This is the cheapest available screen on a candidate witness economy: it is a
statement about `Params` fields alone — no equilibrium, no value function, no
fixed point — so an economy that fails it cannot support the persistence route
however its equilibria turn out.

Round BJ1.3 (2026-10-07): the package's P5 now lives on the basin, in pivot-star
form, so the screen holds on the basin `[max xT xS, 1]` instead of the Sender's
own range `[xS, 1]`, and goes through
`subpivot_star_chord_forces_static_response_ge_pivot`. On the basin the pivot is
the state itself, so the conclusion reads `x ≤ σ`. General in `F`. -/
theorem SenderPersistencePackage.static_response_ge_pivot
    {D : p.ValueClass2} {E : p.FeedbackStackelbergEquilibriumTop}
    {xT xS K_S : ℝ}
    (hpkg : p.SenderPersistencePackage D E xT xS K_S)
    (V_T : D.CarrierT) (V_S : D.CarrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (max xT xS) (1 : ℝ)) :
    max x (max xT xS) ≤ p.σ x (D.α_on V_T V_S x) := by
  have hKS : 0 ≤ K_S :=
    (hpkg.sender_carrier_lipschitz E.V_S hpkg.sender_value_mem).nonneg
  obtain ⟨hxT0, hxT1⟩ := hpkg.xT_mem
  obtain ⟨-, hxS1⟩ := hpkg.xS_mem
  have hx0 : 0 ≤ x := le_trans (le_trans hxT0 (le_max_left xT xS)) hx.1
  refine subpivot_star_chord_forces_static_response_ge_pivot p
    (le_max_of_le_left hx0) (max_le hx.2 (max_le hxT1 hxS1)) hKS ?_
  exact hpkg.sender_subpivot_chord V_T V_S x hx

/-! ## P5's reach, and what it therefore cannot deliver (2026-08-14)

P5 is a hypothesis about chords over `[0, max x s̄]`. Everything it says about the
Sender's objective is confined to that range. Two consequences, both of which
bound what any persistence argument can extract from it.

The first is arithmetic and immediate: at any state at or above the sanction
floor, `max x s̄` collapses to `x`, so **P5 constrains the objective only at
sanctions weakly below the current state**. It is silent about every sanction
above it.

The second is a refutation, and its scope must be stated exactly.

What the persistence route extracts from P5, against the carrier Lipschitz bound
P2, is *strict monotonicity of the Sender's dynamic objective on the sub-pivot
range* — that and nothing more
(`senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz`).
The refutation below shows those extracted consequences, together with weak
persistence and greatest-selector optimality, do **not** imply strict
persistence: a single-peaked objective whose peak sits exactly at the current
state satisfies all of them and leaves the ratchet weak.

**Scope, stated three ways so it cannot drift.**

* What is refuted: the *route* — the implication from P5's extracted consequences
  to strict persistence.
* What is **not** refuted: the raw hypothesis. No complete `Params` economy has
  been constructed that satisfies the full P5 package while strict persistence
  fails, so "P5 does not imply strict persistence" is an expectation here, not a
  theorem. The expectation rests on `subpivot_range_collapses_above_floor`: P5's
  range genuinely mentions no sanction above the current state once that state is
  at or above the floor. Converting the expectation into a theorem needs a
  witness economy, and is logged as its own round.
* What is not claimed either way: that no economy has strict persistence. Several
  do.

One further correction, to a sentence this file previously carried. Strictness is
unnecessary for *orbit convergence and order selection*
(`Theory/LockIn/BasinAttraction.lean`, Phase 3), but it remains necessary for
attraction of a whole basin to one common limit. Those are different claims and
the earlier wording ran them together. -/

/-- **Above the sanction floor, P5's range is just `[0, x]`.**

Arithmetic, and the point of the section: at a state at or above the floor the
sub-pivot range collapses to the sanctions weakly below the current state, so P5
says nothing about any sanction exceeding it. -/
theorem subpivot_range_collapses_above_floor {x sbar : ℝ} (h : sbar ≤ x) :
    Set.Icc (0 : ℝ) (max x sbar) = Set.Icc 0 x := by
  rw [max_eq_left h]

/-- **P5's sub-pivot strict monotonicity, plus weak persistence, does not give
strict persistence.**

Every hypothesis of the persistence route is met, in the abstract shape the route
supplies it:

* the Sender's objective is strictly increasing on the sub-pivot range
  `[0, max x s̄]` — this is what P5 against P2's Lipschitz carrier delivers
  (`senderDynObjective_strictMono_of_transition_adjusted_chord_and_V_lipschitz`);
* `r` is a genuine maximizer of the objective over the feasible set, and is the
  *greatest* one — the defining property of `σ_dyn_top`;
* the weak level condition `max x s̄ ≤ r` holds;
* the state lies at or above the floor, which is the interior case.

And the conclusion `x < r` is false. The witness is a single-peaked objective
whose peak sits exactly at `x`: it rises strictly all the way up to `x`, so P5's
conclusion holds on the whole sub-pivot range, and then falls, so `x` is the
unique maximizer and the greatest response is exactly `x`.

Rule-11 verdict, at its exact scope: the profitable upward deviation the strict
ratchet needs is **not derivable from the consequences the current persistence
route extracts from P5**. It is not shown here that the full P5 package fails to
imply it — that would require a complete `Params` counterexample, which has not
been built.

Any route to interior strictness through these consequences must therefore add
something, and nothing was added. The order-selection theorem in
`BasinAttraction.lean` reaches an extremal rest point without strictness, but
that is per-orbit selection, not attraction of the basin to one common limit. -/
theorem subpivot_strictMono_and_weak_level_insufficient_for_strict_ratchet :
    ¬ ∀ (obj : ℝ → ℝ) (r x sbar : ℝ),
        x ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ sbar → sbar ≤ x →
        StrictMonoOn obj (Set.Icc 0 (max x sbar)) →
        r ∈ Set.Icc (0 : ℝ) 1 →
        IsMaxOn obj (Set.Icc (0 : ℝ) 1) r →
        (∀ z ∈ Set.Icc (0 : ℝ) 1, IsMaxOn obj (Set.Icc (0 : ℝ) 1) z → z ≤ r) →
        max x sbar ≤ r →
        x < r := by
  intro h
  have hmax : IsMaxOn (fun s : ℝ => -(s - 1 / 2) ^ 2) (Set.Icc (0 : ℝ) 1)
      (1 / 2) := by
    intro z _
    simp only [Set.mem_setOf_eq]
    nlinarith [sq_nonneg (z - 1 / 2)]
  have hbad := h (fun s => -(s - 1 / 2) ^ 2) (1 / 2) (1 / 2) 0
    (by norm_num) le_rfl (by norm_num)
    (by
      intro u hu v hv huv
      simp only []
      have hu2 : u ≤ 1 / 2 := by simpa using hu.2
      have hv2 : v ≤ 1 / 2 := by simpa using hv.2
      have hu1 : (0 : ℝ) ≤ u := hu.1
      nlinarith)
    (by norm_num) hmax
    (by
      intro z _ hz
      have h1 : (fun s : ℝ => -(s - 1 / 2) ^ 2) (1 / 2)
          ≤ (fun s : ℝ => -(s - 1 / 2) ^ 2) z := hz (by norm_num)
      simp only [] at h1
      nlinarith [sq_nonneg (z - 1 / 2)])
    (by norm_num)
  exact absurd hbad (lt_irrefl _)

end Params
end AbstractGame

end

end Sanctions
