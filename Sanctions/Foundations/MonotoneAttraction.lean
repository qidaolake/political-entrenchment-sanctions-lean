/-
Sanctions/Foundations/MonotoneAttraction.lean

**Attraction to a named fixed point for a monotone interval map.**

This is general one-dimensional order dynamics: an abstract map `G : ℝ → ℝ` on a
compact interval. Nothing here mentions sanctions, a transition law, an
equilibrium, a payoff family, or a parameter value (Rule 19).

## What this adds, and why the existing lemma is not enough

`StokeyLucas.monotone_orbit_converges` (SLP 1989 §6.1) already proves that every
orbit of a continuous monotone self-map of `[a,b]` converges to *some* fixed
point in `[a,b]`. That is convergence to an unnamed limit, and it is strictly
weaker than attraction: it does not say two different starting points share a
limit, and it therefore cannot support the word *attractor*.

The missing step is the uniqueness hypothesis. `monotone_orbit_tendsto_of_unique`
supplies it: if `x_star` is the **only** fixed point of `G` in `[a,b]`, every
orbit from `[a,b]` converges to `x_star`.

## Order selection: the same conclusion without any uniqueness hypothesis

Uniqueness is a strong thing to ask for, and a certified basin need not have it.
The `A1`–`A3` group drops it altogether. Without assuming anything about how many
rest points the interval contains, the orbit's **first movement** determines
which one is reached, and the one reached is extremal in the order:
`monotoneOn_orbit_tendsto_least_fixedPoint_above` (upward first step selects the
least fixed point weakly above the start),
`monotoneOn_orbit_tendsto_greatest_fixedPoint_below` (its mirror), and
`monotoneOn_orbit_tendsto_order_selected_fixedPoint`, which packages the
exhaustive trichotomy. Read as dynamics, this is what "the initial condition
selects the long-run outcome" means when stated at full generality.

**Selection is not attraction, and the difference is the whole point of the
counterexample below.** In the order-selection group the limit is bound *after*
the starting point and may depend on it; the claim is that each orbit converges
and that its limit is extremal on the side it moved. Attraction — one named
point, reached from every start in the interval — is a strictly stronger
statement, and the identity map satisfies the first while failing the second
everywhere. So dropping uniqueness costs something real, and what it costs is
recorded in `nonunique_fixedPoint_breaks_named_limit`. The `A4` and threshold
groups recover attraction, and the strict sign condition is exactly what they pay
for it.

The final section makes that exchange rate exact: attraction to a common limit,
uniqueness of the rest point in the basin, and the strict sign condition are
**equivalent** here. So any sufficient condition for whole-basin attraction must
*imply* uniqueness of the basin's rest point — which does not close the search,
it aims it. Conditions that **derive** uniqueness from deeper primitives, rather
than assume it or assume the full pointwise sign pattern, remain the open and
worthwhile target.

## Attribution

The order-selection group is not new mathematics. It is the one-dimensional case
of classical monotone iteration in an ordered Banach space: Amann (1976),
*Fixed point equations and nonlinear eigenvalue problems in ordered Banach
spaces*, SIAM Review 18(4), **Theorem 6.1** — an increasing map with a lower
solution `ȳ ≤ f(ȳ)` and an upper solution `f(ŷ) ≤ ŷ` has a minimal fixed point
above `ȳ`, reached as the increasing limit of `fᵏ(ȳ)` — and **Corollary 6.2** for
the maximal mirror. `monotoneOn_orbit_tendsto_least_fixedPoint_above` and
`monotoneOn_orbit_tendsto_greatest_fixedPoint_below` are those statements
specialized to a compact real interval, where continuity supplies the compactness
Amann assumes. A local copy of the source is in
`PaperRefer/MathTheory/FixedPointOrderedBanachSpaces-Amann-1976.md`.

What this file contributes is the Lean development, the trichotomy packaging, the
refutations that fix the boundary of each statement, and — with
`Theory/LockIn/BasinAttraction.lean` — the connection to an equilibrium-generated
transition. Not the order-theoretic step itself.

The `A4` group then shows the basin itself need not be handed in: where `G` lies
strictly above the diagonal on `[a, x*)` and fixes `x*`, invariance of `[a, x*]`
and uniqueness of the rest point are both **derived**
(`strictAbove_Ico_basin_tendsto`), so the basin is determined by the sign of
`G x − x` rather than drawn around a numerical witness.

The next group derives the **boundary** too. A point where the sign of `G x − x`
changes is a rest point by continuity alone (`signFlip_is_fixedPoint`), so a
threshold separating a wash-out region from a ratchet region is a steady state of
the same map rather than a separate assumption, and the two regions either side
of it are basins with different long-run outcomes.

The last group removes the remaining hand-in. `signFlip_is_fixedPoint` still
takes the *crossing* from outside, along with the sign pattern on both sides of
it. `leastWeakAbove_spec` constructs the crossing instead, as
`sInf {x ∈ [a,b] : x ≤ G x}` — the lowest state at which erosion stops — from two
**endpoint readings** and continuity. The strict sign region below the threshold
is then a conclusion, and the threshold is a function of `G` and the window
alone. `greatestWeakBelow_spec` mirrors it, and
`derivedThresholds_eq_iff_unique_fixedPoint` says the two coincide exactly when
the window holds one rest point. Between them the construction claims nothing,
which `derivedThresholds_can_differ` shows is the correct amount to claim.

The basin lemmas in that group also drop **monotonicity**: once the strict sign
holds throughout an interval, each orbit step moves the same way because of the
sign, not because `G` is order-preserving, so only a feasibility bound is needed
(`strictBelow_basin_tendsto_of_lowerBound` and its mirror). That is what makes a
derived threshold usable across a region where `G` is known to be continuous but
is *not* known to be monotone.

## The hypothesis is load-bearing, and this is the paper's live boundary

`nonunique_fixedPoint_breaks_named_limit` refutes the version without uniqueness,
using the identity map on `[0,1]`: it is continuous, monotone, self-mapping, and
`0` is a fixed point, yet the orbit from `1` is constantly `1` and does not
converge to `0`. Every point is fixed, so "converges to some fixed point" is
vacuously satisfied while attraction fails everywhere.

That is exactly the gap between what this development proves and the word
*attractor*, so the counterexample is retained rather than treated as a textbook
aside.

Continuity is refutation-tested too, and formally: `derivedThreshold_needs_continuity`
exhibits a jump map with the *same* endpoint readings as
`leastWeakAbove_spec` assumes and no rest point in the window at all, so
continuity carries that group's entire content. Monotonicity was also
refutation-tested during development — `x ↦ 1 - x` on `[0,1]` has the unique
fixed point `1/2` and the orbit from `0` cycles `0,1,0,1,…`, which kills the
monotonicity-free version of the *uniqueness* route — but note that the
sign-region route does not need it at all, which is why the
`…_of_lowerBound` / `…_of_upperBound` pair exists.

## Scope

Everything below is a statement about `G`, `[a,b]`, and a fixed point. Nothing
is claimed about Lyapunov stability, rates of convergence, or robustness of `G`
under perturbation; `step_away_of_strict_above_diagonal` in particular is a
*directional* one-step statement and is deliberately not called repulsion in any
Lyapunov sense.

One earlier theorem here was **vacuous** and has been removed; see
`strictAbove_on_closed_Icc_contradictory`, which now records the contradiction
permanently.
-/

import Sanctions.Foundations.StokeyLucas

namespace Sanctions
namespace MonotoneAttraction

open Filter Topology

/-! ## A utility used throughout: orbits of a self-map stay put -/

/-- Every iterate of a self-map of `[a,b]` started in `[a,b]` lies in `[a,b]`. -/
theorem orbit_mem_Icc {G : ℝ → ℝ} {a b : ℝ}
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) : ∀ n, G^[n] x₀ ∈ Set.Icc a b := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ k ih => rw [Function.iterate_succ_apply']; exact hG_maps _ ih

/-! ## Target A — attraction to the unique fixed point -/

/-- **Every orbit converges to the unique fixed point.**

If `G` is continuous and non-decreasing, maps `[a,b]` into itself, and `x_star`
is the only point of `[a,b]` that `G` fixes, then the orbit of every starting
point in `[a,b]` converges to `x_star`.

This is the smallest addition to `StokeyLucas.monotone_orbit_converges` that
upgrades "converges to *some* fixed point" into "converges to *this* fixed
point" — the difference between a certified basin and an attractor. -/
theorem monotone_orbit_tendsto_of_unique
    {G : ℝ → ℝ} {a b x_star : ℝ} (hab : a ≤ b)
    (hG_mono : Monotone G) (hG_cont : Continuous G)
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    (hUniq : ∀ y ∈ Set.Icc a b, G y = y → y = x_star)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star) := by
  obtain ⟨z, hz_mem, hz_fix, hz_tendsto⟩ :=
    Sanctions.StokeyLucas.monotone_orbit_converges hab hG_mono hG_cont hG_maps hx₀
  rwa [hUniq z hz_mem hz_fix] at hz_tendsto

/-- **The named point really is a fixed point of the interval.**

Non-vacuity for `monotone_orbit_tendsto_of_unique`: its uniqueness hypothesis is
stated as "every interval fixed point equals `x_star`", which on its own does not
say `x_star` is one. Under the same hypotheses it is one, because the interval is
nonempty and the orbit from `a` produces a fixed point that uniqueness then
identifies with `x_star`. -/
theorem uniqueFixedPoint_mem_and_isFixed
    {G : ℝ → ℝ} {a b x_star : ℝ} (hab : a ≤ b)
    (hG_mono : Monotone G) (hG_cont : Continuous G)
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    (hUniq : ∀ y ∈ Set.Icc a b, G y = y → y = x_star) :
    x_star ∈ Set.Icc a b ∧ G x_star = x_star := by
  obtain ⟨z, hz_mem, hz_fix, _⟩ :=
    Sanctions.StokeyLucas.monotone_orbit_converges hab hG_mono hG_cont hG_maps
      (Set.left_mem_Icc.mpr hab)
  have hz : z = x_star := hUniq z hz_mem hz_fix
  exact ⟨hz ▸ hz_mem, hz ▸ hz_fix⟩

/-! ## The refutation: uniqueness cannot be dropped -/

/-- **Without fixed-point uniqueness, orbits need not reach a named limit.**

The identity map on `[0,1]` is continuous, non-decreasing, and self-mapping, and
`0` is one of its fixed points — yet the orbit from `1` is constantly `1`.

This is the precise gap between `StokeyLucas.monotone_orbit_converges` and
attraction, and hence between a certified invariant basin and an *attractor*. -/
theorem nonunique_fixedPoint_breaks_named_limit :
    ¬ ∀ (G : ℝ → ℝ) (a b x_star : ℝ), a ≤ b → Monotone G → Continuous G →
        (∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b) →
        x_star ∈ Set.Icc a b → G x_star = x_star →
        ∀ x₀ ∈ Set.Icc a b,
          Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star) := by
  intro h
  have hbad := h id 0 1 0 (by norm_num) monotone_id continuous_id
    (fun x hx => hx) (by norm_num) rfl 1 (by norm_num)
  have hrw : (fun n : ℕ => (id : ℝ → ℝ)^[n] 1) = fun _ : ℕ => (1 : ℝ) := by
    funext n; simp
  rw [hrw] at hbad
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hbad tendsto_const_nhds
  norm_num at this


/-- **A weak level condition does not give fixed-point uniqueness.**

Even a map that lies weakly *above* the diagonal everywhere on `[a,b]` — the
order condition a ratchet argument supplies — can fix every point of the
interval. The identity map again.

This is the abstract form of the obstruction that separates the persistence
hypotheses from attraction: a level condition stated with `≤` constrains
direction but permits a continuum of rest points. -/
theorem weak_level_condition_insufficient :
    ¬ ∀ (G : ℝ → ℝ) (a b : ℝ), a ≤ b → Monotone G → Continuous G →
        (∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b) →
        (∀ x ∈ Set.Icc a b, x ≤ G x) →
        ∃! y, y ∈ Set.Icc a b ∧ G y = y := by
  intro h
  obtain ⟨y, -, huniq⟩ := h id 0 1 (by norm_num) monotone_id continuous_id
    (fun x hx => hx) (fun x _ => le_rfl)
  have h0 : (0 : ℝ) = y := huniq 0 ⟨by norm_num, rfl⟩
  have h1 : (1 : ℝ) = y := huniq 1 ⟨by norm_num, rfl⟩
  rw [← h0] at h1
  norm_num at h1


/-! ## Target A, localized — hypotheses only on the interval

The intended application supplies `MonotoneOn` and `ContinuousOn` over the
certified basin, never global regularity: an equilibrium-derived rule is
monotone where a single-crossing condition has been established and nowhere
else. The global statement above is therefore unusable as-is, and relativizing
it is not cosmetic.

The reduction is to clamp: `H = G ∘ (clamp to [a,b])` is globally monotone and
globally continuous, agrees with `G` on `[a,b]`, and has the same orbits from
starting points in `[a,b]`, because every iterate stays there. -/

/-- Clamp a real to `[a, b]`. -/
noncomputable def clampIcc (a b x : ℝ) : ℝ := max a (min b x)

theorem clampIcc_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    clampIcc a b x ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clampIcc_eq_self {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    clampIcc a b x = x := by
  rw [clampIcc, min_eq_right hx.2, max_eq_right hx.1]

theorem clampIcc_mono (a b : ℝ) : Monotone (clampIcc a b) := fun _ _ hxy =>
  max_le_max le_rfl (min_le_min le_rfl hxy)

theorem clampIcc_continuous (a b : ℝ) : Continuous (clampIcc a b) := by
  unfold clampIcc; fun_prop

/-- **Localized SLP convergence: the orbit reaches *some* fixed point.**

`StokeyLucas.monotone_orbit_converges` with monotonicity and continuity required
only on `[a,b]`. Everything localized below factors through this one clamping
argument rather than repeating it. -/
theorem monotoneOn_orbit_converges
    {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    ∃ x_star ∈ Set.Icc a b, G x_star = x_star ∧
      Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star) := by
  have hmem := clampIcc_mem hab
  set H : ℝ → ℝ := fun x => G (clampIcc a b x) with hH
  have hH_mono : Monotone H := fun _ _ hxy =>
    hG_mono (hmem _) (hmem _) (clampIcc_mono a b hxy)
  have hH_cont : Continuous H :=
    hG_cont.comp_continuous (clampIcc_continuous a b) hmem
  have hH_eq : ∀ x ∈ Set.Icc a b, H x = G x := by
    intro x hx; rw [hH]; simp only [clampIcc_eq_self hx]
  have hH_maps : ∀ x ∈ Set.Icc a b, H x ∈ Set.Icc a b := by
    intro x hx; rw [hH_eq x hx]; exact hG_maps x hx
  have horb : ∀ n, G^[n] x₀ = H^[n] x₀ := by
    have hmemG := orbit_mem_Icc hG_maps hx₀
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
        hH_eq _ (hmemG k)]
  obtain ⟨z, hz_mem, hz_fix, hz_tendsto⟩ :=
    Sanctions.StokeyLucas.monotone_orbit_converges hab hH_mono hH_cont hH_maps hx₀
  exact ⟨z, hz_mem, by rwa [hH_eq z hz_mem] at hz_fix,
    by rw [funext horb]; exact hz_tendsto⟩

/-- **Attraction to the unique fixed point, with interval-local hypotheses.**

Identical to `monotone_orbit_tendsto_of_unique` except that monotonicity and
continuity are required only on `[a,b]`. This is the form an
equilibrium-derived closed loop can actually supply. -/
theorem monotoneOn_orbit_tendsto_of_unique
    {G : ℝ → ℝ} {a b x_star : ℝ} (hab : a ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    (hUniq : ∀ y ∈ Set.Icc a b, G y = y → y = x_star)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star) := by
  obtain ⟨z, hz_mem, hz_fix, hz_tendsto⟩ :=
    monotoneOn_orbit_converges hab hG_mono hG_cont hG_maps hx₀
  rwa [hUniq z hz_mem hz_fix] at hz_tendsto

/-- The localized companion to `uniqueFixedPoint_mem_and_isFixed`. -/
theorem uniqueFixedPointOn_mem_and_isFixed
    {G : ℝ → ℝ} {a b x_star : ℝ} (hab : a ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    (hUniq : ∀ y ∈ Set.Icc a b, G y = y → y = x_star) :
    x_star ∈ Set.Icc a b ∧ G x_star = x_star := by
  obtain ⟨z, hz_mem, hz_fix, _⟩ :=
    monotoneOn_orbit_converges hab hG_mono hG_cont hG_maps
      (Set.left_mem_Icc.mpr hab)
  have hz : z = x_star := hUniq z hz_mem hz_fix
  exact ⟨hz ▸ hz_mem, hz ▸ hz_fix⟩

/-! ## Strict one-sided drift — convergence with no monotonicity of the map

Everything above assumes `MonotoneOn G`. That is the classical hypothesis, and
for a closed loop `G x = F (x, R x)` built from an equilibrium sanction rule it
is exactly the one that is not available: `R` is a greatest-argmax selector
composed with a Bellman-optimal policy, upper semicontinuous at best, and nothing
makes it monotone.

The two theorems here drop it. What replaces it is a *strict one-sided drift*
condition — the map lies strictly above the diagonal below some level, and
strictly below it above — which is what an escalation ratchet supplies directly.
The argument is then elementary and does not touch monotone-map theory at all:
strict drift makes the orbit itself monotone (whatever `G` does elsewhere),
boundedness gives a limit, continuity makes the limit a fixed point, and strict
drift excludes every candidate but the target.

Continuity is still essential and is still the hypothesis that must be earned;
see the counterexamples cited in the section below. -/

/-- **Convergence to the top from strict upward drift.**

No monotonicity of `G`. The orbit rises strictly while below `1`, is trapped
below `1`, and therefore converges; continuity makes the limit fixed, and strict
drift rules out any fixed point below the top.

`hmaps` asks only for the upper bound: the lower one is free, because a strictly
rising orbit never returns below where it started. -/
theorem tendsto_top_of_continuous_strict_above_diagonal
    {G : ℝ → ℝ} {xbar x0 : ℝ} (hbar : xbar ≤ 1)
    (hx0 : x0 ∈ Set.Icc xbar 1)
    (hcont : ContinuousOn G (Set.Icc xbar 1))
    (hmaps : ∀ x ∈ Set.Icc xbar 1, G x ≤ 1)
    (hgt : ∀ x ∈ Set.Ico xbar 1, x < G x)
    (htop : G 1 = 1) :
    Filter.Tendsto (fun n => G^[n] x0) Filter.atTop (𝓝 1) := by
  have hmem : ∀ n, G^[n] x0 ∈ Set.Icc xbar 1 := by
    intro n
    induction n with
    | zero => simpa using hx0
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases eq_or_lt_of_le ih.2 with h | h
      · rw [h, htop]; exact ⟨hbar, le_rfl⟩
      · exact ⟨le_of_lt (lt_of_le_of_lt ih.1 (hgt _ ⟨ih.1, h⟩)), hmaps _ ih⟩
  have hmono : Monotone (fun n => G^[n] x0) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [Function.iterate_succ_apply']
    rcases eq_or_lt_of_le (hmem n).2 with h | h
    · rw [h, htop]
    · exact le_of_lt (hgt _ ⟨(hmem n).1, h⟩)
  obtain ⟨l, hl⟩ := (tendsto_atTop_of_monotone hmono).resolve_left
    (by
      intro hdiv
      obtain ⟨n, hn⟩ := (hdiv.eventually_ge_atTop 2).exists
      exact absurd (hmem n).2 (not_le.mpr (by linarith)))
  have hlub : l ≤ 1 :=
    le_of_tendsto hl (Filter.Eventually.of_forall fun n => (hmem n).2)
  have hllb : xbar ≤ l :=
    ge_of_tendsto hl (Filter.Eventually.of_forall fun n => (hmem n).1)
  have hfix : G l = l := by
    have hGl : Filter.Tendsto (fun n => G (G^[n] x0)) Filter.atTop (𝓝 (G l)) :=
      (hcont l ⟨hllb, hlub⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hl, Filter.Eventually.of_forall hmem⟩)
    have hshift : Filter.Tendsto (fun n => G (G^[n] x0)) Filter.atTop (𝓝 l) := by
      have hre : (fun n => G (G^[n] x0)) = fun n => G^[n + 1] x0 := by
        funext n; rw [Function.iterate_succ_apply']
      rw [hre]
      exact hl.comp (Filter.tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hGl hshift
  rcases eq_or_lt_of_le hlub with h | h
  · rwa [h] at hl
  · exact absurd hfix (ne_of_gt (hgt l ⟨hllb, h⟩))

/-- **Convergence to an interior rest point, from drift that crosses it.**

The sibling of the theorem above for a closed loop whose escalation stops short
of the top: `G` lies strictly above the diagonal below `x_star` and weakly below
it at and above `x_star`, so an orbit starting below rises to `x_star` and stops.

This is the shape an *active continuation channel* produces — escalation that is
self-limiting because the entrenchment it causes eventually outweighs the
coercion it buys — as opposed to the top-convergence case where escalation never
turns around. Both are wanted; neither implies the other. -/
theorem tendsto_fixedPoint_of_crossing
    {G : ℝ → ℝ} {xbar x_star x0 : ℝ} (hbar : xbar ≤ x_star)
    (hx0 : x0 ∈ Set.Icc xbar x_star)
    (hcont : ContinuousOn G (Set.Icc xbar x_star))
    (hbelow : ∀ x ∈ Set.Ico xbar x_star, x < G x)
    (hnotover : ∀ x ∈ Set.Ico xbar x_star, G x ≤ x_star)
    (hstar : G x_star = x_star) :
    Filter.Tendsto (fun n => G^[n] x0) Filter.atTop (𝓝 x_star) := by
  have hmem : ∀ n, G^[n] x0 ∈ Set.Icc xbar x_star := by
    intro n
    induction n with
    | zero => simpa using hx0
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases eq_or_lt_of_le ih.2 with h | h
      · rw [h, hstar]; exact ⟨hbar, le_rfl⟩
      · exact ⟨le_of_lt (lt_of_le_of_lt ih.1 (hbelow _ ⟨ih.1, h⟩)),
          hnotover _ ⟨ih.1, h⟩⟩
  have hmono : Monotone (fun n => G^[n] x0) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [Function.iterate_succ_apply']
    rcases eq_or_lt_of_le (hmem n).2 with h | h
    · rw [h, hstar]
    · exact le_of_lt (hbelow _ ⟨(hmem n).1, h⟩)
  obtain ⟨l, hl⟩ := (tendsto_atTop_of_monotone hmono).resolve_left
    (by
      intro hdiv
      obtain ⟨n, hn⟩ := (hdiv.eventually_ge_atTop (x_star + 1)).exists
      exact absurd (hmem n).2 (not_le.mpr (by linarith)))
  have hlub : l ≤ x_star :=
    le_of_tendsto hl (Filter.Eventually.of_forall fun n => (hmem n).2)
  have hllb : xbar ≤ l :=
    ge_of_tendsto hl (Filter.Eventually.of_forall fun n => (hmem n).1)
  have hfix : G l = l := by
    have hGl : Filter.Tendsto (fun n => G (G^[n] x0)) Filter.atTop (𝓝 (G l)) :=
      (hcont l ⟨hllb, hlub⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hl, Filter.Eventually.of_forall hmem⟩)
    have hshift : Filter.Tendsto (fun n => G (G^[n] x0)) Filter.atTop (𝓝 l) := by
      have hre : (fun n => G (G^[n] x0)) = fun n => G^[n + 1] x0 := by
        funext n; rw [Function.iterate_succ_apply']
      rw [hre]
      exact hl.comp (Filter.tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hGl hshift
  rcases eq_or_lt_of_le hlub with h | h
  · rwa [h] at hl
  · exact absurd hfix (ne_of_gt (hbelow l ⟨hllb, h⟩))

/-! ## Targets A1–A3 — order selection, with no uniqueness assumption at all

Everything above needs the fixed point to be **unique** on the interval. That is
a strong hypothesis and, in the intended application, exactly the one that is not
available: a certified basin can perfectly well contain several rest points.

The theorems in this section drop it entirely. Without any uniqueness
assumption, the orbit's **first movement** already determines which rest point is
reached, and the one reached is extremal in the order: from an upward first step
the orbit converges to the *least* fixed point weakly above the start, from a
downward first step to the *greatest* fixed point weakly below it. This is what
turns "the state settles somewhere" into "the initial condition selects the
outcome" — the honest form of path dependence, and it needs no numerical
construction and no basin drawn by hand.

The two counterexamples above still bind. Continuity remains essential:
`MonotoneThreshold.monotone_selfMap_orbit_limit_need_not_be_fixed` exhibits a
monotone self-map of `[0,2]` whose orbit from `0` converges to `1`, which is not
fixed, while the least fixed point is `2`. And the upward-step hypothesis is
load-bearing: see `least_fixedPoint_above_needs_upward_first_step`. -/

/-- **The orbit is non-decreasing after an upward first step.** -/
theorem monotoneOn_orbit_monotone_of_le_apply
    {G : ℝ → ℝ} {a b : ℝ}
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (hup : x₀ ≤ G x₀) :
    Monotone (fun n => G^[n] x₀) := by
  have hmem := orbit_mem_Icc hG_maps hx₀
  refine monotone_nat_of_le_succ (fun n => ?_)
  induction n with
  | zero => simpa using hup
  | succ k ih =>
    have h := hG_mono (hmem k) (hmem (k + 1)) ih
    rwa [← Function.iterate_succ_apply' G k x₀,
      ← Function.iterate_succ_apply' G (k + 1) x₀] at h

/-- **The orbit never passes a fixed point that starts above it.** -/
theorem monotoneOn_orbit_le_fixedPoint_above
    {G : ℝ → ℝ} {a b y : ℝ}
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b) (hfix : G y = y) (hle : x₀ ≤ y) :
    ∀ n, G^[n] x₀ ≤ y := by
  have hmem := orbit_mem_Icc hG_maps hx₀
  intro n
  induction n with
  | zero => simpa using hle
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := hG_mono (hmem k) hy ih
    rwa [hfix] at h

/-- **Target A1 — an upward first step selects the least fixed point above.**

For a continuous non-decreasing self-map of `[a,b]` and a start `x₀` with
`x₀ ≤ G x₀`, the orbit converges to a point `x*` which is a fixed point, lies
weakly above `x₀`, and is **below every** fixed point of `[a,b]` that lies weakly
above `x₀`. No uniqueness hypothesis anywhere.

The two order facts are separate: the orbit rises (so `x₀ ≤ x*`), and it can
never cross a rest point lying above it (so `x*` is least). Together they say the
limit is the first rest point the state meets on its way up. -/
theorem monotoneOn_orbit_tendsto_least_fixedPoint_above
    {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (hup : x₀ ≤ G x₀) :
    ∃ x_star ∈ Set.Icc a b,
      G x_star = x_star ∧ x₀ ≤ x_star ∧
      (∀ y ∈ Set.Icc a b, G y = y → x₀ ≤ y → x_star ≤ y) ∧
      Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star) := by
  obtain ⟨z, hz_mem, hz_fix, hz_tendsto⟩ :=
    monotoneOn_orbit_converges hab hG_mono hG_cont hG_maps hx₀
  refine ⟨z, hz_mem, hz_fix, ?_, ?_, hz_tendsto⟩
  · have hmono := monotoneOn_orbit_monotone_of_le_apply hG_mono hG_maps hx₀ hup
    have h := ge_of_tendsto' hz_tendsto (fun n => hmono (Nat.zero_le n))
    simpa using h
  · intro y hy hfy hxy
    exact le_of_tendsto' hz_tendsto
      (monotoneOn_orbit_le_fixedPoint_above hG_mono hG_maps hx₀ hy hfy hxy)

/-- **The upward first step cannot be dropped from Target A1.**

Halving on `[0,1]` is continuous, non-decreasing and self-mapping, and its only
fixed point is `0`. Started at `1` the orbit descends, so there is no fixed point
weakly above the start at all — the conclusion of A1 fails outright, not merely
its extremality clause.

Rule-11 artifact: A1's hypothesis `hup` is load-bearing, not decorative. -/
theorem least_fixedPoint_above_needs_upward_first_step :
    ¬ ∀ (G : ℝ → ℝ) (a b x₀ : ℝ), a ≤ b → MonotoneOn G (Set.Icc a b) →
        ContinuousOn G (Set.Icc a b) →
        (∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b) →
        x₀ ∈ Set.Icc a b →
        ∃ x_star ∈ Set.Icc a b, G x_star = x_star ∧ x₀ ≤ x_star := by
  intro h
  obtain ⟨z, _, hz_fix, hz_ge⟩ :=
    h (fun x => x / 2) 0 1 1 (by norm_num)
      (fun x _ y _ hxy => by dsimp only; linarith)
      ((by fun_prop : Continuous fun x : ℝ => x / 2).continuousOn)
      (fun x hx => ⟨by dsimp only; linarith [hx.1], by dsimp only; linarith [hx.2]⟩)
      (by norm_num)
  have hz : z / 2 = z := hz_fix
  linarith

/-- **The orbit is non-increasing after a downward first step.** -/
theorem monotoneOn_orbit_antitone_of_apply_le
    {G : ℝ → ℝ} {a b : ℝ}
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (hdown : G x₀ ≤ x₀) :
    Antitone (fun n => G^[n] x₀) := by
  have hmem := orbit_mem_Icc hG_maps hx₀
  refine antitone_nat_of_succ_le (fun n => ?_)
  induction n with
  | zero => simpa using hdown
  | succ k ih =>
    have h := hG_mono (hmem (k + 1)) (hmem k) ih
    rwa [← Function.iterate_succ_apply' G k x₀,
      ← Function.iterate_succ_apply' G (k + 1) x₀] at h

/-- **The orbit never passes a fixed point that starts below it.** -/
theorem monotoneOn_orbit_ge_fixedPoint_below
    {G : ℝ → ℝ} {a b y : ℝ}
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b) (hfix : G y = y) (hle : y ≤ x₀) :
    ∀ n, y ≤ G^[n] x₀ := by
  have hmem := orbit_mem_Icc hG_maps hx₀
  intro n
  induction n with
  | zero => simpa using hle
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := hG_mono hy (hmem k) ih
    rwa [hfix] at h

/-- **Target A2 — a downward first step selects the greatest fixed point below.**

The exact mirror of A1: with `G x₀ ≤ x₀` the orbit converges to a fixed point
weakly below `x₀` that dominates every fixed point of `[a,b]` weakly below `x₀`.
Economically this is the wash-out direction — the state falls to the highest rest
point beneath where it started. -/
theorem monotoneOn_orbit_tendsto_greatest_fixedPoint_below
    {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (hdown : G x₀ ≤ x₀) :
    ∃ x_star ∈ Set.Icc a b,
      G x_star = x_star ∧ x_star ≤ x₀ ∧
      (∀ y ∈ Set.Icc a b, G y = y → y ≤ x₀ → y ≤ x_star) ∧
      Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star) := by
  obtain ⟨z, hz_mem, hz_fix, hz_tendsto⟩ :=
    monotoneOn_orbit_converges hab hG_mono hG_cont hG_maps hx₀
  refine ⟨z, hz_mem, hz_fix, ?_, ?_, hz_tendsto⟩
  · have hanti := monotoneOn_orbit_antitone_of_apply_le hG_mono hG_maps hx₀ hdown
    have h := le_of_tendsto' hz_tendsto (fun n => hanti (Nat.zero_le n))
    simpa using h
  · intro y hy hfy hxy
    exact ge_of_tendsto' hz_tendsto
      (monotoneOn_orbit_ge_fixedPoint_below hG_mono hG_maps hx₀ hy hfy hxy)

/-- An orbit started at a fixed point never moves. -/
theorem orbit_const_of_fixed {G : ℝ → ℝ} {x₀ : ℝ} (hfix : G x₀ = x₀) :
    ∀ n, G^[n] x₀ = x₀ := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]

/-- **Target A3 — the complete initial-condition classification.**

The three cases of `lt_trichotomy (G x₀) x₀`, so the classification is
exhaustive: whichever way the state first moves is the way it goes, and the limit
is extremal on that side.

* a **strictly** upward first step converges to the least fixed point above `x₀`,
  and that fixed point is strictly above `x₀`;
* a strictly downward first step converges to the greatest fixed point below
  `x₀`, strictly below it;
* no first step at all means `x₀` is already a rest point and stays one.

The strictness in the first two conclusions is an upgrade over A1 and A2, and it
is where the classification earns its name: had the selected fixed point equalled
`x₀`, then `x₀` would have been fixed, contradicting the first step. -/
theorem monotoneOn_orbit_tendsto_order_selected_fixedPoint
    {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    (x₀ < G x₀ →
      ∃ x_star ∈ Set.Icc a b, G x_star = x_star ∧ x₀ < x_star ∧
        (∀ y ∈ Set.Icc a b, G y = y → x₀ ≤ y → x_star ≤ y) ∧
        Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star)) ∧
    (G x₀ < x₀ →
      ∃ x_star ∈ Set.Icc a b, G x_star = x_star ∧ x_star < x₀ ∧
        (∀ y ∈ Set.Icc a b, G y = y → y ≤ x₀ → y ≤ x_star) ∧
        Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star)) ∧
    (G x₀ = x₀ → Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x₀)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hlt
    obtain ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_tendsto⟩ :=
      monotoneOn_orbit_tendsto_least_fixedPoint_above hab hG_mono hG_cont hG_maps
        hx₀ (le_of_lt hlt)
    refine ⟨z, hz_mem, hz_fix, lt_of_le_of_ne hz_ge ?_, hz_least, hz_tendsto⟩
    rintro rfl
    exact absurd hz_fix (ne_of_gt hlt)
  · intro hlt
    obtain ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_tendsto⟩ :=
      monotoneOn_orbit_tendsto_greatest_fixedPoint_below hab hG_mono hG_cont
        hG_maps hx₀ (le_of_lt hlt)
    refine ⟨z, hz_mem, hz_fix, lt_of_le_of_ne hz_le ?_, hz_greatest, hz_tendsto⟩
    rintro rfl
    exact absurd hz_fix (ne_of_lt hlt)
  · intro hfix
    rw [funext (orbit_const_of_fixed hfix)]
    exact tendsto_const_nhds

/-- **Every initial condition selects an extremal fixed point.**

The unconditional reading of A3: drop the case split and what survives is that
the limit exists, is a rest point, and is extremal on whichever side the state
approached it from. Nothing is assumed about the number of rest points. -/
theorem monotoneOn_orbit_tendsto_extremal_fixedPoint
    {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    ∃ x_star ∈ Set.Icc a b, G x_star = x_star ∧
      Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star) ∧
      ((x₀ ≤ x_star ∧ ∀ y ∈ Set.Icc a b, G y = y → x₀ ≤ y → x_star ≤ y) ∨
       (x_star ≤ x₀ ∧ ∀ y ∈ Set.Icc a b, G y = y → y ≤ x₀ → y ≤ x_star)) := by
  rcases le_total x₀ (G x₀) with hup | hdown
  · obtain ⟨z, hz_mem, hz_fix, hz_ge, hz_least, hz_tendsto⟩ :=
      monotoneOn_orbit_tendsto_least_fixedPoint_above hab hG_mono hG_cont hG_maps
        hx₀ hup
    exact ⟨z, hz_mem, hz_fix, hz_tendsto, Or.inl ⟨hz_ge, hz_least⟩⟩
  · obtain ⟨z, hz_mem, hz_fix, hz_le, hz_greatest, hz_tendsto⟩ :=
      monotoneOn_orbit_tendsto_greatest_fixedPoint_below hab hG_mono hG_cont
        hG_maps hx₀ hdown
    exact ⟨z, hz_mem, hz_fix, hz_tendsto, Or.inr ⟨hz_le, hz_greatest⟩⟩

/-! ## Target B — two disjoint invariant intervals -/

/-- **Two-basin attraction.** One map, two disjoint invariant intervals, each
with its own unique fixed point: every orbit converges to the fixed point of the
interval it started in.

Note what this is *not*. There is a single map `G` throughout. The starting point
selects a limit **within one map**, not among several. Read as an equilibrium
statement, it is initial-condition selection inside one equilibrium, and carries
no multiplicity or switching content. -/
theorem twoBasin_tendsto
    {G : ℝ → ℝ} {aL bL aH bH xL xH : ℝ}
    (hL : aL ≤ bL) (hH : aH ≤ bH)
    (hG_mono : Monotone G) (hG_cont : Continuous G)
    (hmapL : ∀ x ∈ Set.Icc aL bL, G x ∈ Set.Icc aL bL)
    (hmapH : ∀ x ∈ Set.Icc aH bH, G x ∈ Set.Icc aH bH)
    (huL : ∀ y ∈ Set.Icc aL bL, G y = y → y = xL)
    (huH : ∀ y ∈ Set.Icc aH bH, G y = y → y = xH) :
    (∀ x₀ ∈ Set.Icc aL bL,
        Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 xL)) ∧
      (∀ x₀ ∈ Set.Icc aH bH,
        Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 xH)) :=
  ⟨fun _ hx => monotone_orbit_tendsto_of_unique hL hG_mono hG_cont hmapL huL hx,
   fun _ hx => monotone_orbit_tendsto_of_unique hH hG_mono hG_cont hmapH huH hx⟩

/-- **Separated basins have distinct limits, so the initial condition selects.**

If the low interval lies strictly below the high one, the two limit points are
distinct and ordered. This is the honest formal content of "dual-basin path
dependence": one map, two limits, history choosing between them. -/
theorem twoBasin_limits_distinct
    {G : ℝ → ℝ} {aL bL aH bH xL xH : ℝ}
    (hL : aL ≤ bL) (hH : aH ≤ bH) (hsep : bL < aH)
    (hG_mono : Monotone G) (hG_cont : Continuous G)
    (hmapL : ∀ x ∈ Set.Icc aL bL, G x ∈ Set.Icc aL bL)
    (hmapH : ∀ x ∈ Set.Icc aH bH, G x ∈ Set.Icc aH bH)
    (huL : ∀ y ∈ Set.Icc aL bL, G y = y → y = xL)
    (huH : ∀ y ∈ Set.Icc aH bH, G y = y → y = xH) :
    xL < xH := by
  have hxL := (uniqueFixedPoint_mem_and_isFixed hL hG_mono hG_cont hmapL huL).1
  have hxH := (uniqueFixedPoint_mem_and_isFixed hH hG_mono hG_cont hmapH huH).1
  exact lt_of_le_of_lt hxL.2 (lt_of_lt_of_le hsep hxH.1)

/-! ## Target B, second half — the honest one-sided statement -/

/-- **One-step motion away from a fixed point.**

If `G` fixes `x_L` and lies strictly above the diagonal at a point `x` to its
right, then `x` is strictly further from `x_L` after one step.

Deliberately weak. This is a statement about one step at one point; it is not
Lyapunov instability, not repulsion of a neighbourhood, and not a claim that the
orbit leaves any particular set. -/
theorem step_away_of_strict_above_diagonal
    {G : ℝ → ℝ} {xL x : ℝ} (hfix : G xL = xL) (hlt : xL < x) (habove : x < G x) :
    |x - xL| < |G x - G xL| := by
  rw [hfix, abs_of_pos (by linarith : (0:ℝ) < x - xL),
    abs_of_pos (by linarith : (0:ℝ) < G x - xL)]
  linarith

/-! ## The strict-ratchet orbit, on the correct domain

An earlier version of this section carried

```
theorem strictMono_orbit_of_strict_above
    (hG_maps  : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    (hstrict  : ∀ x ∈ Set.Icc a b, x < G x)
    (hx₀ : x₀ ∈ Set.Icc a b) : StrictMono (fun n => G^[n] x₀)
```

which is **vacuous**: at the right endpoint the two hypotheses give `G b ≤ b`
and `b < G b` at once, so they are contradictory on every nonempty interval.
`strictAbove_on_closed_Icc_contradictory` records that permanently, so the
formulation cannot return unnoticed.

The repair is to ask for strictness only on the half-open `[a, b)`, which is
what a ratchet condition ever actually delivers: the endpoint is where the rule
meets the diagonal, not a point it rises above. The honest conclusion is then a
one-step statement plus monotonicity of the orbit up to the endpoint, since an
orbit that reaches `b` may stop there. -/

/-- **The closed-interval form of a strict ratchet is contradictory.**

Invariance of `[a,b]` forces `G b ≤ b`; strictness at every point of `[a,b]`
forces `b < G b`. Kept as a regression artifact. -/
theorem strictAbove_on_closed_Icc_contradictory
    {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    (hstrict : ∀ x ∈ Set.Icc a b, x < G x) : False := by
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have h1 : G b ≤ b := (hG_maps b hb).2
  have h2 : b < G b := hstrict b hb
  linarith

/-- **One strict step from any state below the endpoint.**

With strictness required only on `[a, b)`, the orbit rises strictly at every
step taken from a state strictly below the endpoint. Nothing is claimed about a
step taken from `b` itself. -/
theorem orbit_lt_succ_of_mem_Ico
    {G : ℝ → ℝ} {a b : ℝ}
    (hstrict : ∀ x ∈ Set.Ico a b, x < G x)
    {x₀ : ℝ} {n : ℕ} (hn : G^[n] x₀ ∈ Set.Ico a b) :
    G^[n] x₀ < G^[n + 1] x₀ := by
  have h := hstrict _ hn
  simpa [Function.iterate_succ_apply'] using h

/-- **The orbit is non-decreasing once the endpoint is fixed.**

Strictness on `[a,b)` plus `G b = b` gives a genuinely monotone orbit: below the
endpoint it rises, and at the endpoint it rests. This is the non-vacuous
replacement for the deleted `strictMono_orbit_of_strict_above`; it is `Monotone`
rather than `StrictMono` precisely because an orbit that reaches `b` stops. -/
theorem orbit_monotone_of_strict_above_Ico
    {G : ℝ → ℝ} {a b : ℝ}
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    (hstrict : ∀ x ∈ Set.Ico a b, x < G x)
    (hfix_b : G b = b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Monotone (fun n => G^[n] x₀) := by
  have hmem : ∀ n, G^[n] x₀ ∈ Set.Icc a b := by
    intro n
    induction n with
    | zero => simpa using hx₀
    | succ k ih => rw [Function.iterate_succ']; exact hG_maps _ ih
  refine monotone_nat_of_le_succ (fun n => ?_)
  rcases lt_or_eq_of_le (hmem n).2 with hlt | heq
  · exact le_of_lt (orbit_lt_succ_of_mem_Ico hstrict ⟨(hmem n).1, hlt⟩)
  · have : G^[n + 1] x₀ = b := by
      rw [Function.iterate_succ_apply', heq, hfix_b]
    rw [this, heq]

/-! ## Target A4 — a strict sign region *is* a basin, and invariance is derived

The two-basin theorem above takes invariance as a hypothesis: someone must
supply an interval the map sends into itself. That is what makes a basin look
like something drawn by hand around a numerical witness.

It is not needed. If the map lies strictly above the diagonal on `[a, x*)` and
fixes `x*`, then `[a, x*]` is invariant **as a consequence**: monotonicity plus
`G x* = x*` caps the image at `x*`, and strictness floors it above `a`. The same
strictness rules out any other rest point in the interval, so uniqueness is
derived too, and attraction follows with neither hypothesis assumed.

So the basin is determined by the **sign of `G x − x`** together with the rest
point that bounds the sign region — not by a functional form, a parameter vector,
or a chosen interval. That is the form in which a basin claim generalizes. -/

/-- **A strict-above sign region with a fixed top is invariant.**

Derived, not assumed: the image is capped by `G x ≤ G x* = x*` (monotonicity) and
floored by `a ≤ x < G x` (strictness), with the endpoint handled by `G x* = x*`
itself. -/
theorem strictAbove_mapsTo_of_fixed_right
    {G : ℝ → ℝ} {a x_star : ℝ} (hax : a ≤ x_star)
    (hG_mono : MonotoneOn G (Set.Icc a x_star))
    (hfix : G x_star = x_star)
    (hstrict : ∀ x ∈ Set.Ico a x_star, x < G x) :
    ∀ x ∈ Set.Icc a x_star, G x ∈ Set.Icc a x_star := by
  intro x hx
  have hupper : G x ≤ x_star := by
    have h := hG_mono hx ⟨hax, le_rfl⟩ hx.2
    rwa [hfix] at h
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · exact ⟨le_of_lt (lt_of_le_of_lt hx.1 (hstrict x ⟨hx.1, hlt⟩)), hupper⟩
  · exact ⟨by rw [heq, hfix]; exact hax, hupper⟩

/-- **A strict-below sign region with a fixed bottom is invariant.** The mirror
of `strictAbove_mapsTo_of_fixed_right`. -/
theorem strictBelow_mapsTo_of_fixed_left
    {G : ℝ → ℝ} {x_star b : ℝ} (hxb : x_star ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc x_star b))
    (hfix : G x_star = x_star)
    (hstrict : ∀ x ∈ Set.Ioc x_star b, G x < x) :
    ∀ x ∈ Set.Icc x_star b, G x ∈ Set.Icc x_star b := by
  intro x hx
  have hlower : x_star ≤ G x := by
    have h := hG_mono ⟨le_rfl, hxb⟩ hx hx.1
    rwa [hfix] at h
  rcases lt_or_eq_of_le hx.1 with hlt | heq
  · exact ⟨hlower, le_of_lt (lt_of_lt_of_le (hstrict x ⟨hlt, hx.2⟩) hx.2)⟩
  · exact ⟨hlower, by rw [← heq, hfix]; exact hxb⟩

/-- **Target A4 — the strict-above sign region is an attraction basin.**

If `G` lies strictly above the diagonal throughout `[a, x*)` and fixes `x*`, then
every orbit started anywhere in `[a, x*]` converges to `x*`. Neither invariance
of the interval nor uniqueness of the rest point is assumed: both follow from the
sign condition.

This is the general-position form of the ratchet claim. Contrast
`strictAbove_on_closed_Icc_contradictory`: asking for strictness at `x*` as well
is contradictory, so the half-open region is not a technical convenience but the
only coherent statement. -/
theorem strictAbove_Ico_basin_tendsto
    {G : ℝ → ℝ} {a x_star : ℝ} (hax : a ≤ x_star)
    (hG_mono : MonotoneOn G (Set.Icc a x_star))
    (hG_cont : ContinuousOn G (Set.Icc a x_star))
    (hfix : G x_star = x_star)
    (hstrict : ∀ x ∈ Set.Ico a x_star, x < G x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a x_star) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star) := by
  refine monotoneOn_orbit_tendsto_of_unique hax hG_mono hG_cont
    (strictAbove_mapsTo_of_fixed_right hax hG_mono hfix hstrict) ?_ hx₀
  intro y hy hfy
  by_contra hne
  have h := hstrict y ⟨hy.1, lt_of_le_of_ne hy.2 hne⟩
  rw [hfy] at h
  exact lt_irrefl y h

/-- **Target A4, mirrored — the strict-below sign region is an attraction
basin.** Wash-out to the bottom of the region, again with invariance and
uniqueness derived from the sign condition rather than assumed. -/
theorem strictBelow_Ioc_basin_tendsto
    {G : ℝ → ℝ} {x_star b : ℝ} (hxb : x_star ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc x_star b))
    (hG_cont : ContinuousOn G (Set.Icc x_star b))
    (hfix : G x_star = x_star)
    (hstrict : ∀ x ∈ Set.Ioc x_star b, G x < x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc x_star b) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star) := by
  refine monotoneOn_orbit_tendsto_of_unique hxb hG_mono hG_cont
    (strictBelow_mapsTo_of_fixed_left hxb hG_mono hfix hstrict) ?_ hx₀
  intro y hy hfy
  by_contra hne
  have h := hstrict y ⟨lt_of_le_of_ne hy.1 (Ne.symm hne), hy.2⟩
  rw [hfy] at h
  exact lt_irrefl y h

/-! ### Boundary limit helpers

Two packaged one-sided approach filters. Each bundles the limit of `G`, the
limit of the identity, and the `NeBot` witness that makes the comparison
non-vacuous, so the four sign-to-boundary lemmas below are one line each. -/

private theorem leftLimit {G : ℝ → ℝ} {a c : ℝ} (hac : a < c)
    (hG_cont : ContinuousOn G (Set.Icc a c)) :
    Filter.Tendsto G (𝓝[Set.Ico a c] c) (𝓝 (G c)) ∧
      Filter.Tendsto (fun x : ℝ => x) (𝓝[Set.Ico a c] c) (𝓝 c) ∧
      (𝓝[Set.Ico a c] c).NeBot :=
  ⟨(hG_cont c ⟨le_of_lt hac, le_rfl⟩).mono Set.Ico_subset_Icc_self,
   tendsto_id.mono_left nhdsWithin_le_nhds, right_nhdsWithin_Ico_neBot hac⟩

private theorem rightLimit {G : ℝ → ℝ} {c b : ℝ} (hcb : c < b)
    (hG_cont : ContinuousOn G (Set.Icc c b)) :
    Filter.Tendsto G (𝓝[Set.Ioc c b] c) (𝓝 (G c)) ∧
      Filter.Tendsto (fun x : ℝ => x) (𝓝[Set.Ioc c b] c) (𝓝 c) ∧
      (𝓝[Set.Ioc c b] c).NeBot :=
  ⟨(hG_cont c ⟨le_rfl, le_of_lt hcb⟩).mono Set.Ioc_subset_Icc_self,
   tendsto_id.mono_left nhdsWithin_le_nhds, left_nhdsWithin_Ioc_neBot hcb⟩

/-! ## Phase 6 — the basin boundary is derived from the sign of `G x − x`

Target A4 already removed the invariance hypothesis. What it still asks for is
the boundary: someone must hand in a point `x*` and a proof that `G` fixes it.

That is not needed either. A boundary of a strict sign region **is** a rest
point, by continuity alone: approaching it through points where `G x > x` forces
`G x* ≥ x*`, and one inequality on the far side closes it. So the whole
structure — where the basins are, where they end, and which rest point each one
reaches — is determined by the sign of `G x − x`, with no functional form, no
parameter vector, and no interval chosen in advance.

The formulation here is order-theoretic rather than topological: no connected
components, no `IsPreconnected`, no interval-decomposition machinery. Sign
regions enter only as hypotheses of the form "`G x > x` throughout `[a, c)`",
which is what an economic condition actually delivers, and the four limit lemmas
convert the sign on the open side into a weak inequality at the boundary. Naming
`{x | x < G x}` and `{x | G x < x}` as sets would add notation without
shortening a single proof below, so they are not introduced.

The economic payoff is `signFlip_is_fixedPoint`: a **threshold** — a state where
wash-out gives way to ratchet — is a rest point of the closed loop, not an extra
assumption. `threshold_below_tendsto_left` and `threshold_above_tendsto_right`
then split the interval around it into two basins with different long-run
outcomes. History-dependence, with the dividing line derived. -/

/-- Approaching `c` from the left through a strict-above region forces
`c ≤ G c`. -/
theorem le_apply_of_strictAbove_Ico
    {G : ℝ → ℝ} {a c : ℝ} (hac : a < c)
    (hG_cont : ContinuousOn G (Set.Icc a c))
    (hstrict : ∀ x ∈ Set.Ico a c, x < G x) : c ≤ G c := by
  obtain ⟨htG, htid, _hne⟩ := leftLimit hac hG_cont
  exact le_of_tendsto_of_tendsto htid htG
    (by filter_upwards [self_mem_nhdsWithin] with x hx using le_of_lt (hstrict x hx))

/-- Approaching `c` from the left through a strict-below region forces
`G c ≤ c`. -/
theorem apply_le_of_strictBelow_Ico
    {G : ℝ → ℝ} {a c : ℝ} (hac : a < c)
    (hG_cont : ContinuousOn G (Set.Icc a c))
    (hstrict : ∀ x ∈ Set.Ico a c, G x < x) : G c ≤ c := by
  obtain ⟨htG, htid, _hne⟩ := leftLimit hac hG_cont
  exact le_of_tendsto_of_tendsto htG htid
    (by filter_upwards [self_mem_nhdsWithin] with x hx using le_of_lt (hstrict x hx))

/-- Approaching `c` from the right through a strict-below region forces
`G c ≤ c`. -/
theorem apply_le_of_strictBelow_Ioc
    {G : ℝ → ℝ} {c b : ℝ} (hcb : c < b)
    (hG_cont : ContinuousOn G (Set.Icc c b))
    (hstrict : ∀ x ∈ Set.Ioc c b, G x < x) : G c ≤ c := by
  obtain ⟨htG, htid, _hne⟩ := rightLimit hcb hG_cont
  exact le_of_tendsto_of_tendsto htG htid
    (by filter_upwards [self_mem_nhdsWithin] with x hx using le_of_lt (hstrict x hx))

/-- Approaching `c` from the right through a strict-above region forces
`c ≤ G c`. -/
theorem le_apply_of_strictAbove_Ioc
    {G : ℝ → ℝ} {c b : ℝ} (hcb : c < b)
    (hG_cont : ContinuousOn G (Set.Icc c b))
    (hstrict : ∀ x ∈ Set.Ioc c b, x < G x) : c ≤ G c := by
  obtain ⟨htG, htid, _hne⟩ := rightLimit hcb hG_cont
  exact le_of_tendsto_of_tendsto htid htG
    (by filter_upwards [self_mem_nhdsWithin] with x hx using le_of_lt (hstrict x hx))

/-- **A threshold is a rest point.**

Where the map crosses the diagonal — strictly below on one side, strictly above
on the other — the crossing point is fixed. Continuity from the left gives
`G t ≤ t`, continuity from the right gives `t ≤ G t`.

Read as dynamics, this says the dividing line between a wash-out region and a
ratchet region is not an extra assumption. It is a steady state of the same map,
and it is where it is because of where the sign changes. -/
theorem signFlip_is_fixedPoint
    {G : ℝ → ℝ} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hdown : ∀ x ∈ Set.Ioo a t, G x < x)
    (hup : ∀ x ∈ Set.Ioo t b, x < G x) : G t = t := by
  have hle : G t ≤ t :=
    apply_le_of_strictBelow_Ico (a := (a + t) / 2) (c := t) (by linarith)
      (hG_cont.mono (Set.Icc_subset_Icc (by linarith) (by linarith)))
      (fun x hx => hdown x ⟨by linarith [hx.1], hx.2⟩)
  have hge : t ≤ G t :=
    le_apply_of_strictAbove_Ioc (c := t) (b := (t + b) / 2) (by linarith)
      (hG_cont.mono (Set.Icc_subset_Icc (by linarith) (by linarith)))
      (fun x hx => hup x ⟨hx.1, by linarith [hx.2]⟩)
  exact le_antisymm hle hge

/-- **A4 with the boundary derived rather than supplied.**

`strictAbove_Ico_basin_tendsto` asks for `G x* = x*`. Here the far-side
inequality `G c ≤ c` suffices — feasibility of the interval already gives it in
the intended application — and continuity upgrades it to an equality. So both the
invariance of the basin and the fixedness of its boundary now follow from the
sign condition. -/
theorem strictAbove_Ico_basin_tendsto_of_apply_le
    {G : ℝ → ℝ} {a c : ℝ} (hac : a < c)
    (hG_mono : MonotoneOn G (Set.Icc a c))
    (hG_cont : ContinuousOn G (Set.Icc a c))
    (hstrict : ∀ x ∈ Set.Ico a c, x < G x)
    (hle : G c ≤ c)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a c) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 c) :=
  strictAbove_Ico_basin_tendsto (le_of_lt hac) hG_mono hG_cont
    (le_antisymm hle (le_apply_of_strictAbove_Ico hac hG_cont hstrict)) hstrict hx₀

/-- The wash-out mirror of `strictAbove_Ico_basin_tendsto_of_apply_le`. -/
theorem strictBelow_Ioc_basin_tendsto_of_le_apply
    {G : ℝ → ℝ} {c b : ℝ} (hcb : c < b)
    (hG_mono : MonotoneOn G (Set.Icc c b))
    (hG_cont : ContinuousOn G (Set.Icc c b))
    (hstrict : ∀ x ∈ Set.Ioc c b, G x < x)
    (hge : c ≤ G c)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc c b) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 c) :=
  strictBelow_Ioc_basin_tendsto (le_of_lt hcb) hG_mono hG_cont
    (le_antisymm (apply_le_of_strictBelow_Ioc hcb hG_cont hstrict) hge) hstrict hx₀

/-- **Below the threshold, every path washes out to the bottom.**

The strict-below region `(a, t)` is a basin of `a`: every start in `[a, t)`
converges to `a`. Note the half-open interval — the threshold itself is a rest
point and does not move, so it belongs to neither basin. -/
theorem threshold_below_tendsto_left
    {G : ℝ → ℝ} {a t : ℝ}
    (hG_mono : MonotoneOn G (Set.Icc a t))
    (hG_cont : ContinuousOn G (Set.Icc a t))
    (hfix_a : G a = a)
    (hdown : ∀ x ∈ Set.Ioo a t, G x < x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ico a t) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 a) := by
  have hsub : Set.Icc a x₀ ⊆ Set.Icc a t :=
    Set.Icc_subset_Icc le_rfl (le_of_lt hx₀.2)
  exact strictBelow_Ioc_basin_tendsto hx₀.1 (hG_mono.mono hsub) (hG_cont.mono hsub)
    hfix_a (fun x hx => hdown x ⟨hx.1, lt_of_le_of_lt hx.2 hx₀.2⟩)
    (Set.right_mem_Icc.mpr hx₀.1)

/-- **Above the threshold, every path ratchets to the top.** The mirror: the
strict-above region `(t, b)` is a basin of `b`, and every start in `(t, b]`
converges to `b`.

Together with `threshold_below_tendsto_left` and `signFlip_is_fixedPoint`, this
is dual-basin path dependence with the dividing line **derived**: one map, one
sign change, two long-run outcomes, and the initial state deciding between
them. -/
theorem threshold_above_tendsto_right
    {G : ℝ → ℝ} {t b : ℝ}
    (hG_mono : MonotoneOn G (Set.Icc t b))
    (hG_cont : ContinuousOn G (Set.Icc t b))
    (hfix_b : G b = b)
    (hup : ∀ x ∈ Set.Ioo t b, x < G x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioc t b) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 b) := by
  have hsub : Set.Icc x₀ b ⊆ Set.Icc t b :=
    Set.Icc_subset_Icc (le_of_lt hx₀.1) le_rfl
  exact strictAbove_Ico_basin_tendsto hx₀.2 (hG_mono.mono hsub) (hG_cont.mono hsub)
    hfix_b (fun x hx => hup x ⟨lt_of_lt_of_le hx₀.1 hx.1, hx.2⟩)
    (Set.left_mem_Icc.mpr hx₀.2)

/-! ## Attraction, uniqueness and the strict sign condition are the same thing

This section settles a question the development had been answering loosely. Three
conditions on a monotone continuous self-map of `[a,b]` are **equivalent**:

1. every orbit from `[a,b]` converges to `x_star` (attraction to a common limit);
2. `x_star` is the only fixed point of `G` in `[a,b]`;
3. `G x < x` above `x_star` and `x < G x` below it, throughout `[a,b]`.

`1 ⟹ 2` is immediate and is the direction that had been missing: an orbit started
at a fixed point never moves, so if it converges to `x_star` it *is* `x_star`.
`2 ⟹ 1` is `monotoneOn_orbit_tendsto_of_unique`. `2 ⟹ 3` runs through the orbit:
a point above `x_star` whose image were weakly above it would have a rising orbit,
whose limit would then exceed `x_star`. `3 ⟹ 2` is one line.

Two consequences worth stating in words, because the surrounding prose has been
imprecise about both.

* **Fixed-point uniqueness inside the basin is *necessary* for attraction, not
  merely one sufficient route to it.** Earlier drafts wrote "a strict sign
  condition, fixed-point uniqueness, or another isolation condition", as though
  these were three alternatives of unknown relative strength. The first and second
  are equivalent here, and the third is not enough — see below.
* **Strictness is not a stronger hypothesis than uniqueness in this setting; it is
  the same hypothesis.** So the interior question — can a whole basin be shown to
  reach one long-run outcome? — is exactly the question of whether the basin has
  one rest point. That aims the search rather than ending it: any sufficient
  route must imply basin uniqueness, and the useful routes are the ones that
  *derive* it from primitives instead of assuming it.

`isolated_fixedPoint_insufficient_for_attraction` closes the remaining gap: a
fixed point can be *locally* isolated and still fail to attract the whole claimed
basin, because another isolated fixed point elsewhere in the interval holds its
own orbit. Note the exact scope — the witness there attracts a great deal, just
not everything claimed for it. Local information about `x_star` never settles a
basin-wide claim; the condition is global to the basin. -/

/-- **Attraction to a common limit forces that limit to be the only rest point.**

An orbit started at a fixed point is constant, so if every orbit in `[a,b]`
converges to `x_star`, any fixed point of `[a,b]` equals `x_star`. No regularity
of `G` at all is needed — not monotonicity, not continuity, not invariance. -/
theorem attraction_forces_unique_fixedPoint
    {G : ℝ → ℝ} {a b x_star : ℝ}
    (hattract : ∀ x₀ ∈ Set.Icc a b,
      Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star)) :
    ∀ y ∈ Set.Icc a b, G y = y → y = x_star := by
  intro y hy hfix
  have h := hattract y hy
  rw [funext (orbit_const_of_fixed hfix)] at h
  exact (tendsto_nhds_unique h tendsto_const_nhds).symm

/-- **Above a unique rest point the map lies strictly below the diagonal.**

If it did not, the orbit from that point would rise and its limit would exceed
`x_star`, contradicting convergence to `x_star`. -/
theorem apply_lt_self_of_unique_fixedPoint
    {G : ℝ → ℝ} {a b x_star : ℝ} (hab : a ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    (hUniq : ∀ y ∈ Set.Icc a b, G y = y → y = x_star)
    {x : ℝ} (hx : x ∈ Set.Icc a b) (hlt : x_star < x) : G x < x := by
  by_contra hcon
  have hup : x ≤ G x := not_lt.mp hcon
  have hmono := monotoneOn_orbit_monotone_of_le_apply hG_mono hG_maps hx hup
  have htend :=
    monotoneOn_orbit_tendsto_of_unique hab hG_mono hG_cont hG_maps hUniq hx
  have h := ge_of_tendsto' htend (fun n => hmono (Nat.zero_le n))
  simp only [Function.iterate_zero_apply] at h
  linarith

/-- **Below a unique rest point the map lies strictly above the diagonal.** -/
theorem self_lt_apply_of_unique_fixedPoint
    {G : ℝ → ℝ} {a b x_star : ℝ} (hab : a ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b)
    (hUniq : ∀ y ∈ Set.Icc a b, G y = y → y = x_star)
    {x : ℝ} (hx : x ∈ Set.Icc a b) (hlt : x < x_star) : x < G x := by
  by_contra hcon
  have hdown : G x ≤ x := not_lt.mp hcon
  have hanti := monotoneOn_orbit_antitone_of_apply_le hG_mono hG_maps hx hdown
  have htend :=
    monotoneOn_orbit_tendsto_of_unique hab hG_mono hG_cont hG_maps hUniq hx
  have h := le_of_tendsto' htend (fun n => hanti (Nat.zero_le n))
  simp only [Function.iterate_zero_apply] at h
  linarith

/-- **Attraction to a common limit is equivalent to uniqueness of the rest
point.**

The characterization the development needed. Read left to right it says an
attraction claim always carries a uniqueness claim with it, so the word cannot be
used more cheaply than the condition. Read right to left it is
`monotoneOn_orbit_tendsto_of_unique`. -/
theorem attraction_iff_unique_fixedPoint
    {G : ℝ → ℝ} {a b x_star : ℝ} (hab : a ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b) :
    (∀ x₀ ∈ Set.Icc a b,
        Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star))
      ↔ (∀ y ∈ Set.Icc a b, G y = y → y = x_star) :=
  ⟨attraction_forces_unique_fixedPoint,
   fun hUniq _ hx => monotoneOn_orbit_tendsto_of_unique hab hG_mono hG_cont
     hG_maps hUniq hx⟩

/-- **Uniqueness of the rest point is equivalent to the strict sign condition.**

So the strict sign condition is not a stronger assumption bought at extra cost;
in this setting it is uniqueness written out pointwise. Combined with
`attraction_iff_unique_fixedPoint`, all three of attraction, uniqueness and strict
signing are the same condition. -/
theorem unique_fixedPoint_iff_strictly_signed
    {G : ℝ → ℝ} {a b x_star : ℝ} (hab : a ≤ b)
    (hG_mono : MonotoneOn G (Set.Icc a b))
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hG_maps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b) :
    (∀ y ∈ Set.Icc a b, G y = y → y = x_star)
      ↔ ((∀ x ∈ Set.Icc a b, x_star < x → G x < x) ∧
         (∀ x ∈ Set.Icc a b, x < x_star → x < G x)) := by
  constructor
  · intro hUniq
    exact ⟨fun x hx h => apply_lt_self_of_unique_fixedPoint hab hG_mono hG_cont
        hG_maps hUniq hx h,
      fun x hx h => self_lt_apply_of_unique_fixedPoint hab hG_mono hG_cont
        hG_maps hUniq hx h⟩
  · rintro ⟨hhi, hlo⟩ y hy hfix
    rcases lt_trichotomy y x_star with h | h | h
    · exact absurd hfix (ne_of_lt (hlo y hy h)).symm
    · exact h
    · exact absurd hfix (ne_of_lt (hhi y hy h))

/-- **A locally isolated rest point need not attract anything.**

Squaring on `[0,1]` is continuous, non-decreasing and self-mapping. Its rest
points are `0` and `1`, both isolated, and `0` is isolated with room to spare.
Yet the orbit from `1` is constantly `1`, so `0` does **not** attract the interval
claimed for it.

Read the scope precisely: `0` attracts all of `[0,1)`, which is most of the
interval. What fails is the basin-wide claim, and it fails because of a second
rest point at the far end — not because `0` is weakly attracting near itself.
That is the point: isolation is *local* information about `x_star`, and a
basin-wide claim is *global*. Anything strong enough to give it has to rule out
rest points everywhere in the basin, which by `attraction_iff_unique_fixedPoint`
is exactly what it must do. -/
theorem isolated_fixedPoint_insufficient_for_attraction :
    ¬ ∀ (G : ℝ → ℝ) (a b x_star : ℝ), a ≤ b → MonotoneOn G (Set.Icc a b) →
        ContinuousOn G (Set.Icc a b) →
        (∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b) →
        x_star ∈ Set.Icc a b → G x_star = x_star →
        (∃ ε > 0, ∀ y ∈ Set.Icc a b, |y - x_star| < ε → G y = y → y = x_star) →
        ∀ x₀ ∈ Set.Icc a b,
          Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 x_star) := by
  intro h
  have hbad := h (fun x => x ^ 2) 0 1 0 zero_le_one
    (fun u hu v hv huv => by dsimp only; nlinarith [hu.1, hv.1])
    (by fun_prop)
    (fun x hx => ⟨by positivity, by dsimp only; nlinarith [hx.1, hx.2]⟩)
    ⟨le_rfl, zero_le_one⟩ (by norm_num)
    ⟨1 / 2, by norm_num, by
      intro y hy hyd hfix
      have h2 : y ^ 2 = y := hfix
      have hy0 : y * (y - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hy0 with h0 | h1
      · exact h0
      · exfalso
        have hy1 : y = 1 := by linarith
        rw [hy1] at hyd
        norm_num at hyd⟩
    1 ⟨zero_le_one, le_rfl⟩
  have hfix1 : ∀ n : ℕ, (fun x : ℝ => x ^ 2)^[n] 1 = 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]; norm_num
  rw [funext hfix1] at hbad
  have hcontra : (0 : ℝ) = 1 := tendsto_nhds_unique hbad tendsto_const_nhds
  norm_num at hcontra

/-! ## Phase 7 — the threshold as a function of the map

Phase 6 shows that *if* the map crosses the diagonal at `t`, then `t` is a rest
point. It does not say a crossing exists, and it does not say where it is:
`signFlip_is_fixedPoint` takes the sign pattern on both sides of `t` as a
hypothesis, so `t` still arrives from outside.

This section removes that. Given only two endpoint readings — the map is
strictly below the diagonal at the bottom of a window, and weakly above it at
the top — the crossing is **constructed** as

  `leastWeakAbove G a b = sInf {x ∈ [a,b] | x ≤ G x}`,

the lowest state in the window at which erosion stops. Continuity of `G` makes
that set closed, so the infimum is attained and lies in it; and every state
strictly below the infimum is outside the set, which *is* the strict-erosion
sign region. So the sign pattern below the threshold is a **conclusion**, not a
hypothesis, and the threshold is a function of `G` and the window alone. It is
also the least rest point of the window, since every rest point sits in the set.

The mirror `greatestWeakBelow` is the highest state at which building stops, and
the strict-building region above it comes out the same way. The two coincide
exactly when the window holds one rest point
(`derivedThresholds_eq_iff_unique_fixedPoint`), and between them the construction
claims nothing — which is honest, because a monotone map may fix a whole
subinterval.

Two facts are load-bearing and recorded as refutations: continuity cannot be
dropped (`derivedThreshold_needs_continuity` — a jump map with the same endpoint
readings has no rest point in the window at all), and the two thresholds really
can differ (`derivedThresholds_can_differ`).

The section opens with two basin lemmas that drop **monotonicity** from the A4
pair. Once the strict sign holds on the whole interval, the orbit is monotone for
free — each step moves the same way because of the sign, not because `G` is
order-preserving — so all that is needed is a bound keeping the orbit inside.
This matters for the intended application: a derived threshold can be extracted
across a region where the map is known to be continuous but is *not* known to be
monotone, and the basin conclusion still lands there. -/

/-- **Wash-out without monotonicity.**

`strictBelow_Ioc_basin_tendsto` assumes `G` is order-preserving on the interval.
It need not be. If `G` sits strictly below the diagonal throughout `(a,b]`, every
step moves down whatever `G` does elsewhere, so the orbit is decreasing on its
own; a lower bound at `a` keeps it in the interval, and continuity identifies the
limit as a rest point, which the strict sign forces to be `a`.

Economically: if the closed loop erodes the political state at every state in the
region, entrenchment washes out to the bottom — and this needs no assumption that
higher inherited states produce higher next states. -/
theorem strictBelow_basin_tendsto_of_lowerBound
    {G : ℝ → ℝ} {a b : ℝ}
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hfix_a : G a = a)
    (hstrict : ∀ x ∈ Set.Ioc a b, G x < x)
    (hlb : ∀ x ∈ Set.Icc a b, a ≤ G x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 a) := by
  have hle : ∀ x ∈ Set.Icc a b, G x ≤ x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · exact le_of_eq (by rw [← h, hfix_a])
    · exact le_of_lt (hstrict x ⟨h, hx.2⟩)
  have hmaps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b :=
    fun x hx => ⟨hlb x hx, le_trans (hle x hx) hx.2⟩
  have hmem : ∀ n, G^[n] x₀ ∈ Set.Icc a b := by
    intro n
    induction n with
    | zero => simpa using hx₀
    | succ k ih => rw [Function.iterate_succ_apply']; exact hmaps _ ih
  have hanti : Antitone (fun n => G^[n] x₀) := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    rw [Function.iterate_succ_apply']
    exact hle _ (hmem n)
  have hbdd : BddBelow (Set.range fun n => G^[n] x₀) :=
    ⟨a, by rintro y ⟨n, rfl⟩; exact (hmem n).1⟩
  set L := ⨅ n, G^[n] x₀ with hL
  have htend : Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 L) :=
    tendsto_atTop_ciInf hanti hbdd
  have hLmem : L ∈ Set.Icc a b :=
    isClosed_Icc.mem_of_tendsto htend (Filter.Eventually.of_forall hmem)
  have hshift : Filter.Tendsto (fun n => G^[n + 1] x₀) Filter.atTop (𝓝 L) :=
    htend.comp (Filter.tendsto_add_atTop_nat 1)
  have hGtend : Filter.Tendsto (fun n => G (G^[n] x₀)) Filter.atTop (𝓝 (G L)) :=
    ((hG_cont L hLmem).tendsto).comp
      (tendsto_nhdsWithin_iff.mpr ⟨htend, Filter.Eventually.of_forall hmem⟩)
  have hfixL : G L = L := by
    refine tendsto_nhds_unique hGtend ?_
    simpa [Function.iterate_succ_apply'] using hshift
  rcases eq_or_lt_of_le hLmem.1 with h | h
  · rw [← h] at htend; exact htend
  · exact absurd hfixL (ne_of_lt (hstrict L ⟨h, hLmem.2⟩))

/-- **Ratchet without monotonicity.** The mirror of
`strictBelow_basin_tendsto_of_lowerBound`: strict building throughout `[a,b)`
plus an upper bound at `b` drives every orbit up to `b`, with no order-preservation
assumed on `G`. -/
theorem strictAbove_basin_tendsto_of_upperBound
    {G : ℝ → ℝ} {a b : ℝ}
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (hfix_b : G b = b)
    (hstrict : ∀ x ∈ Set.Ico a b, x < G x)
    (hub : ∀ x ∈ Set.Icc a b, G x ≤ b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc a b) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 b) := by
  have hge : ∀ x ∈ Set.Icc a b, x ≤ G x := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with h | h
    · exact le_of_eq (by rw [h, hfix_b])
    · exact le_of_lt (hstrict x ⟨hx.1, h⟩)
  have hmaps : ∀ x ∈ Set.Icc a b, G x ∈ Set.Icc a b :=
    fun x hx => ⟨le_trans hx.1 (hge x hx), hub x hx⟩
  have hmem : ∀ n, G^[n] x₀ ∈ Set.Icc a b := by
    intro n
    induction n with
    | zero => simpa using hx₀
    | succ k ih => rw [Function.iterate_succ_apply']; exact hmaps _ ih
  have hmono : Monotone (fun n => G^[n] x₀) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [Function.iterate_succ_apply']
    exact hge _ (hmem n)
  have hbdd : BddAbove (Set.range fun n => G^[n] x₀) :=
    ⟨b, by rintro y ⟨n, rfl⟩; exact (hmem n).2⟩
  set L := ⨆ n, G^[n] x₀ with hL
  have htend : Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 L) :=
    tendsto_atTop_ciSup hmono hbdd
  have hLmem : L ∈ Set.Icc a b :=
    isClosed_Icc.mem_of_tendsto htend (Filter.Eventually.of_forall hmem)
  have hshift : Filter.Tendsto (fun n => G^[n + 1] x₀) Filter.atTop (𝓝 L) :=
    htend.comp (Filter.tendsto_add_atTop_nat 1)
  have hGtend : Filter.Tendsto (fun n => G (G^[n] x₀)) Filter.atTop (𝓝 (G L)) :=
    ((hG_cont L hLmem).tendsto).comp
      (tendsto_nhdsWithin_iff.mpr ⟨htend, Filter.Eventually.of_forall hmem⟩)
  have hfixL : G L = L := by
    refine tendsto_nhds_unique hGtend ?_
    simpa [Function.iterate_succ_apply'] using hshift
  rcases eq_or_lt_of_le hLmem.2 with h | h
  · rw [h] at htend; exact htend
  · exact absurd hfixL (ne_of_gt (hstrict L ⟨hLmem.1, h⟩))

/-- **Below the threshold, every path washes out — with no monotonicity.**

The monotonicity-free counterpart of `threshold_below_tendsto_left`. The strict
sign region `(a, t)` is a basin of `a`, and every start in `[a, t)` reaches `a`;
all that replaces order-preservation is the bound `a ≤ G x`, which feasibility
supplies. The threshold itself is a rest point and belongs to neither basin. -/
theorem threshold_below_tendsto_left_of_lowerBound
    {G : ℝ → ℝ} {a t : ℝ}
    (hG_cont : ContinuousOn G (Set.Icc a t))
    (hfix_a : G a = a)
    (hdown : ∀ x ∈ Set.Ioo a t, G x < x)
    (hlb : ∀ x ∈ Set.Icc a t, a ≤ G x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ico a t) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 a) := by
  have hsub : Set.Icc a x₀ ⊆ Set.Icc a t :=
    Set.Icc_subset_Icc le_rfl (le_of_lt hx₀.2)
  exact strictBelow_basin_tendsto_of_lowerBound (hG_cont.mono hsub) hfix_a
    (fun x hx => hdown x ⟨hx.1, lt_of_le_of_lt hx.2 hx₀.2⟩)
    (fun x hx => hlb x (hsub hx)) (Set.right_mem_Icc.mpr hx₀.1)

/-- **Above the threshold, every path ratchets — with no monotonicity.** The
mirror of `threshold_below_tendsto_left_of_lowerBound`. -/
theorem threshold_above_tendsto_right_of_upperBound
    {G : ℝ → ℝ} {t b : ℝ}
    (hG_cont : ContinuousOn G (Set.Icc t b))
    (hfix_b : G b = b)
    (hup : ∀ x ∈ Set.Ioo t b, x < G x)
    (hub : ∀ x ∈ Set.Icc t b, G x ≤ b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioc t b) :
    Filter.Tendsto (fun n => G^[n] x₀) Filter.atTop (𝓝 b) := by
  have hsub : Set.Icc x₀ b ⊆ Set.Icc t b :=
    Set.Icc_subset_Icc (le_of_lt hx₀.1) le_rfl
  exact strictAbove_basin_tendsto_of_upperBound (hG_cont.mono hsub) hfix_b
    (fun x hx => hup x ⟨lt_of_lt_of_le hx₀.1 hx.1, hx.2⟩)
    (fun x hx => hub x (hsub hx)) (Set.left_mem_Icc.mpr hx₀.2)

/-- The states of `[a,b]` at which the map is weakly **above** the diagonal —
where the state does not erode. -/
def weakAboveSet (G : ℝ → ℝ) (a b : ℝ) : Set ℝ := {x ∈ Set.Icc a b | x ≤ G x}

/-- The states of `[a,b]` at which the map is weakly **below** the diagonal —
where the state does not build. -/
def weakBelowSet (G : ℝ → ℝ) (a b : ℝ) : Set ℝ := {x ∈ Set.Icc a b | G x ≤ x}

/-- The non-erosion set is closed: it is the interval intersected with a closed
sublevel set of the continuous gap `G x − x`. -/
theorem weakAboveSet_isClosed {G : ℝ → ℝ} {a b : ℝ}
    (hG_cont : ContinuousOn G (Set.Icc a b)) : IsClosed (weakAboveSet G a b) := by
  have h : weakAboveSet G a b
      = Set.Icc a b ∩ (fun x => G x - x) ⁻¹' (Set.Ici 0) := by
    ext x
    simp only [weakAboveSet, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ici, sub_nonneg]
  rw [h]
  exact (hG_cont.sub continuousOn_id).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_Ici

/-- The non-building set is closed. Mirror of `weakAboveSet_isClosed`. -/
theorem weakBelowSet_isClosed {G : ℝ → ℝ} {a b : ℝ}
    (hG_cont : ContinuousOn G (Set.Icc a b)) : IsClosed (weakBelowSet G a b) := by
  have h : weakBelowSet G a b
      = Set.Icc a b ∩ (fun x => x - G x) ⁻¹' (Set.Ici 0) := by
    ext x
    simp only [weakBelowSet, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ici, sub_nonneg]
  rw [h]
  exact (continuousOn_id.sub hG_cont).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_Ici

/-- **The derived lower threshold.** The lowest state of `[a,b]` at which the map
stops eroding — a function of the map and the window, nothing else. -/
noncomputable def leastWeakAbove (G : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sInf (weakAboveSet G a b)

/-- **The derived upper threshold.** The highest state of `[a,b]` at which the map
stops building. -/
noncomputable def greatestWeakBelow (G : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sSup (weakBelowSet G a b)

/-- **The lower threshold is a rest point, and everything under it erodes.**

Read the hypotheses as two endpoint readings on the window: at the bottom the map
is strictly below the diagonal (`G a < a` — the state falls), at the top it is
weakly above (`b ≤ G b` — the state does not fall). Continuity in between is all
that is added. The conclusion says the threshold

* lies strictly inside above the bottom and weakly inside below the top;
* is a **rest point** of the map;
* has **strict erosion everywhere beneath it** — the sign region that
  `signFlip_is_fixedPoint` and `threshold_below_tendsto_left` take as a
  hypothesis is here a consequence;
* is the **least** rest point of the window.

Nothing is assumed about the sign anywhere between the two endpoints, and `G`
need not be monotone. This is the sense in which the threshold is *derived*: it
is `sInf` of a set defined from `G`, not a constant supplied from outside. -/
theorem leastWeakAbove_spec {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (ha : G a < a) (hb : b ≤ G b) :
    a < leastWeakAbove G a b ∧ leastWeakAbove G a b ≤ b ∧
      G (leastWeakAbove G a b) = leastWeakAbove G a b ∧
      (∀ x ∈ Set.Ico a (leastWeakAbove G a b), G x < x) ∧
      (∀ y ∈ Set.Icc a b, G y = y → leastWeakAbove G a b ≤ y) := by
  set S := weakAboveSet G a b with hS
  have hne : S.Nonempty := ⟨b, ⟨⟨hab, le_rfl⟩, hb⟩⟩
  have hbdd : BddBelow S := ⟨a, fun y hy => hy.1.1⟩
  set t := leastWeakAbove G a b with ht
  have htS : t ∈ S := (weakAboveSet_isClosed hG_cont).csInf_mem hne hbdd
  have hta : a ≤ t := htS.1.1
  have htb : t ≤ b := htS.1.2
  have hstrict : ∀ x ∈ Set.Ico a t, G x < x := by
    intro x hx
    by_contra hcon
    exact absurd (csInf_le hbdd
      (show x ∈ S from ⟨⟨hx.1, le_trans (le_of_lt hx.2) htb⟩, not_lt.mp hcon⟩))
      (not_le.mpr hx.2)
  have hat : a < t := by
    rcases lt_or_eq_of_le hta with h | h
    · exact h
    · exact absurd (h ▸ htS.2) (not_le.mpr ha)
  refine ⟨hat, htb, ?_, hstrict, fun y hy hfy => csInf_le hbdd ⟨hy, le_of_eq hfy.symm⟩⟩
  exact le_antisymm
    (apply_le_of_strictBelow_Ico hat
      (hG_cont.mono (Set.Icc_subset_Icc le_rfl htb)) hstrict) htS.2

/-- **The upper threshold is a rest point, and everything over it builds.**

Mirror of `leastWeakAbove_spec`: the endpoint readings are "the state does not
build at the bottom" (`G a ≤ a`) and "the state strictly builds at the top"
(`b < G b`), and the derived object is the greatest rest point of the window,
with strict building everywhere above it. -/
theorem greatestWeakBelow_spec {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (ha : G a ≤ a) (hb : b < G b) :
    a ≤ greatestWeakBelow G a b ∧ greatestWeakBelow G a b < b ∧
      G (greatestWeakBelow G a b) = greatestWeakBelow G a b ∧
      (∀ x ∈ Set.Ioc (greatestWeakBelow G a b) b, x < G x) ∧
      (∀ y ∈ Set.Icc a b, G y = y → y ≤ greatestWeakBelow G a b) := by
  set S := weakBelowSet G a b with hS
  have hne : S.Nonempty := ⟨a, ⟨⟨le_rfl, hab⟩, ha⟩⟩
  have hbdd : BddAbove S := ⟨b, fun y hy => hy.1.2⟩
  set t := greatestWeakBelow G a b with ht
  have htS : t ∈ S := (weakBelowSet_isClosed hG_cont).csSup_mem hne hbdd
  have hta : a ≤ t := htS.1.1
  have htb : t ≤ b := htS.1.2
  have hstrict : ∀ x ∈ Set.Ioc t b, x < G x := by
    intro x hx
    by_contra hcon
    exact absurd (le_csSup hbdd
      (show x ∈ S from ⟨⟨le_trans hta (le_of_lt hx.1), hx.2⟩, not_lt.mp hcon⟩))
      (not_le.mpr hx.1)
  have htb' : t < b := by
    rcases lt_or_eq_of_le htb with h | h
    · exact h
    · exact absurd (h ▸ htS.2) (not_le.mpr hb)
  refine ⟨hta, htb', ?_, hstrict, fun y hy hfy => le_csSup hbdd ⟨hy, le_of_eq hfy⟩⟩
  exact le_antisymm htS.2
    (le_apply_of_strictAbove_Ioc htb'
      (hG_cont.mono (Set.Icc_subset_Icc hta le_rfl)) hstrict)

/-- **The lower threshold never passes the upper one.** Both are rest points of
the same window, and each is extremal on its own side, so the wash-out region
ends no later than the ratchet region begins. -/
theorem leastWeakAbove_le_greatestWeakBelow
    {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (ha : G a < a) (hb : b < G b) :
    leastWeakAbove G a b ≤ greatestWeakBelow G a b := by
  obtain ⟨hta, htb, htfix, -, -⟩ := leastWeakAbove_spec hab hG_cont ha hb.le
  obtain ⟨-, -, -, -, hsgreat⟩ := greatestWeakBelow_spec hab hG_cont ha.le hb
  exact hsgreat _ ⟨hta.le, htb⟩ htfix

/-- **The two derived thresholds coincide exactly when the window holds one rest
point.**

This is the honest statement of what the construction delivers. When the map has
a single rest point in the window, wash-out below and ratchet above meet at one
state, and the interval splits cleanly into two basins with the dividing line
derived. When it has several, the two thresholds bracket the region where the
construction is silent — and by `attraction_iff_unique_fixedPoint` that silence
is not a defect of the method, since a common limit across a region holding two
rest points is false, not merely unproved. -/
theorem derivedThresholds_eq_iff_unique_fixedPoint
    {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hG_cont : ContinuousOn G (Set.Icc a b))
    (ha : G a < a) (hb : b < G b) :
    leastWeakAbove G a b = greatestWeakBelow G a b ↔
      ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b, G y = y → G z = z → y = z := by
  obtain ⟨hta, htb, htfix, -, htleast⟩ := leastWeakAbove_spec hab hG_cont ha hb.le
  obtain ⟨hsa, hsb, hsfix, -, hsgreat⟩ := greatestWeakBelow_spec hab hG_cont ha.le hb
  constructor
  · intro heq y hy z hz hfy hfz
    have h1 := htleast y hy hfy
    have h2 := hsgreat y hy hfy
    have h3 := htleast z hz hfz
    have h4 := hsgreat z hz hfz
    rw [heq] at h1 h3
    exact le_antisymm (le_trans h2 h3) (le_trans h4 h1)
  · intro huniq
    exact huniq _ ⟨hta.le, htb⟩ _ ⟨hsa, hsb.le⟩ htfix hsfix

/-- **Continuity cannot be dropped: without it there is no crossing at all.**

A map that jumps from `0` to `1` at the middle of the window reads exactly like a
crossing at its endpoints — strictly below the diagonal at the bottom, weakly
above at the top — and has no rest point anywhere in the window. So the endpoint
readings alone derive nothing; the content of `leastWeakAbove_spec` is carried by
continuity.

Rule-11 artifact: the continuity hypothesis is load-bearing, not decorative. -/
theorem derivedThreshold_needs_continuity :
    ¬ ∀ (G : ℝ → ℝ) (a b : ℝ), a ≤ b → G a < a → b ≤ G b →
        ∃ t ∈ Set.Icc a b, G t = t := by
  intro h
  obtain ⟨t, ht, hft⟩ := h (fun x => if x < 1 / 2 then 0 else 1) (1 / 4) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  by_cases hc : t < 1 / 2
  · rw [if_pos hc] at hft; linarith [ht.1, hft]
  · rw [if_neg hc] at hft; linarith [ht.2, hft]

/-- **The two derived thresholds really can differ.**

`x ↦ min x (2x) + max 0 (x−1)` is continuous, falls strictly at `−1`, rises
strictly at `2`, and fixes every point of `[0,1]`. Its lower threshold is `0` and
its upper is `1`, so the construction leaves the whole unit interval unclassified.

Rule-11 artifact: `leastWeakAbove_le_greatestWeakBelow` cannot be upgraded to an
equality, and the region between the two thresholds is a genuine gap in the
conclusion rather than an artefact of the proof. -/
theorem derivedThresholds_can_differ :
    ¬ ∀ (G : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn G (Set.Icc a b) →
        G a < a → b < G b → leastWeakAbove G a b = greatestWeakBelow G a b := by
  intro h
  set G : ℝ → ℝ := fun x => min x (2 * x) + max 0 (x - 1) with hG
  have hcont : ContinuousOn G (Set.Icc (-1 : ℝ) 2) :=
    Continuous.continuousOn (by fun_prop)
  have hkey := (derivedThresholds_eq_iff_unique_fixedPoint (G := G) (a := -1) (b := 2)
      (by norm_num) hcont (by norm_num [hG]) (by norm_num [hG])).mp
    (h G (-1) 2 (by norm_num) hcont (by norm_num [hG]) (by norm_num [hG]))
  have hbad : (0 : ℝ) = 1 :=
    hkey 0 (by norm_num) 1 (by norm_num) (by norm_num [hG]) (by norm_num [hG])
  norm_num at hbad

/-! ## Round L (doc 80, M8) — endpoint fixation is derived

`equilibriumTop_derived_dual_basins` takes `G lo = lo` and `G hi = hi` as
hypotheses. Neither is needed: a map continuous on `[lo, hi]` that never falls
below `lo` there and lies strictly below the diagonal on `(lo, xL]` for some
`xL > lo` fixes `lo`, because `G lo` is the limit of `G x < x` as `x ↓ lo`; the
mirror fixes `hi`. The reader's round-K validation package (2026-09-10,
document 03 §5) named the reduction; the sibling
`equilibriumTop_derived_dual_basins'` consumes these two lemmas. -/

/-- **A continuous map strictly below the diagonal just to the right of `lo`,
and never below `lo`, fixes `lo`.** -/
theorem fixed_left_of_continuousOn_strict_below {G : ℝ → ℝ} {lo xL hi : ℝ}
    (hlo : lo < xL) (hxh : xL ≤ hi)
    (hcont : ContinuousOn G (Set.Icc lo hi))
    (hstrict : ∀ x ∈ Set.Ioc lo xL, G x < x)
    (hlb : ∀ x ∈ Set.Icc lo hi, lo ≤ G x) : G lo = lo := by
  have hmem : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlo.le.trans hxh⟩
  refine le_antisymm ?_ (hlb lo hmem)
  have hsub : Set.Ioc lo xL ⊆ Set.Icc lo hi := fun x hx => ⟨hx.1.le, hx.2.trans hxh⟩
  have hG : Tendsto G (𝓝[Set.Ioc lo xL] lo) (𝓝 (G lo)) :=
    (hcont lo hmem).tendsto.mono_left (nhdsWithin_mono _ hsub)
  have hid : Tendsto (fun x : ℝ => x) (𝓝[Set.Ioc lo xL] lo) (𝓝 lo) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  haveI : (𝓝[Set.Ioc lo xL] lo).NeBot := by
    rw [nhdsWithin_Ioc_eq_nhdsGT hlo]; infer_instance
  exact le_of_tendsto_of_tendsto hG hid
    (eventually_nhdsWithin_of_forall fun x hx => (hstrict x hx).le)

/-- **A continuous map strictly above the diagonal just to the left of `hi`, and
never above `hi`, fixes `hi`.** The mirror of
`fixed_left_of_continuousOn_strict_below`. -/
theorem fixed_right_of_continuousOn_strict_above {G : ℝ → ℝ} {lo xH hi : ℝ}
    (hhi : xH < hi) (hlx : lo ≤ xH)
    (hcont : ContinuousOn G (Set.Icc lo hi))
    (hstrict : ∀ x ∈ Set.Ico xH hi, x < G x)
    (hub : ∀ x ∈ Set.Icc lo hi, G x ≤ hi) : G hi = hi := by
  have hmem : hi ∈ Set.Icc lo hi := ⟨hlx.trans hhi.le, le_rfl⟩
  refine le_antisymm (hub hi hmem) ?_
  have hsub : Set.Ico xH hi ⊆ Set.Icc lo hi := fun x hx => ⟨hlx.trans hx.1, hx.2.le⟩
  have hG : Tendsto G (𝓝[Set.Ico xH hi] hi) (𝓝 (G hi)) :=
    (hcont hi hmem).tendsto.mono_left (nhdsWithin_mono _ hsub)
  have hid : Tendsto (fun x : ℝ => x) (𝓝[Set.Ico xH hi] hi) (𝓝 hi) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  haveI : (𝓝[Set.Ico xH hi] hi).NeBot := by
    rw [nhdsWithin_Ico_eq_nhdsLT hhi]; infer_instance
  exact le_of_tendsto_of_tendsto hid hG
    (eventually_nhdsWithin_of_forall fun x hx => (hstrict x hx).le)

end MonotoneAttraction
end Sanctions
