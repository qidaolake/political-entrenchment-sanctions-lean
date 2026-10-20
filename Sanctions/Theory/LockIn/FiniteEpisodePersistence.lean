/-
Sanctions/Theory/LockIn/FiniteEpisodePersistence.lean

**A finite episode of implemented sanctions, then the resumed equilibrium: no
endogenous exit** (docs 58/59, deliverables S0 and S1).

## The statement

A confrontation may begin for reasons the model does not solve — an attempt
to make the other side back down, a signal, a bargaining delay. What the model
can say is what such an episode leaves behind. Fix a full top-selector
equilibrium `E` with realised Sender rule `R_E`. Let an *imposed* sanction
schedule `u` run for `T` periods from `x₀`, and let the equilibrium resume at
date `T` from the state the episode leaves. Then:

* **Splice identity** (`splicedPath_add`). The path after `T` is exactly the
  general-`F` equilibrium path `dynamicTopLockInPathF` restarted at the
  episode-end state `y_T`; the sanctions after `T` are exactly the equilibrium
  sanctions from `y_T`. This is what lets every stationary tail lemma apply.
* **Conditional non-exit** (`equilibriumTop_post_episode_nonexit_generalF`).
  If `y_T` lies in a region `[x̄, 1]` that the resumed rule preserves — a level
  floor `s̄ ≤ R_E` on `[x̄, 1]` with `x̄ ≤ F(x̄, s̄)` — then the state never
  leaves `[x̄, 1]`, the sanction never falls below `s̄`, and no relief cutoff
  strictly below `s̄` is ever reached. If the resumed rule is also weakly above
  the state on `[x̄, 1]` (the ratchet), the sanction stays above the inherited
  entry state, and with a monotone rule it is nondecreasing
  (`equilibriumTop_post_episode_no_relief_of_ratchet`; the joint-preference
  basin form `equilibriumTop_post_episode_no_relief_of_jointBasin` is its
  corollary, BH2.1).
* **A maximal episode is enough** (`equilibriumTop_fullShock_episode_nonexit_generalF`):
  under strict adjustment, every schedule `u ≡ 1` of length at least the
  canonical horizon `fullShockEntryHorizon x̄` ends in `[x̄, 1]` from every start.
  Full-sanction ascent on `[0, x̄]` is enough
  (`equilibriumTop_fullShock_episode_nonexit_generalF_of_preBasinAscent`).
* **So is a non-maximal one** (`equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent`):
  a schedule whose sanctions stay at or above a level `h` that strictly lifts
  every state of `[0, x̄]` (held-sanction ascent, which forces `x̄ < h`), for at
  least `highEpisodeHorizon h x̄ = ⌈x̄ / η_h(x̄)⌉` periods, ends in `[x̄, 1]`,
  where `η_h(x̄) = min_{[0,x̄]} (F(x, h) − x) > 0` is derived from continuity and
  that ascent. At `h = 1` this is the full-shock horizon by definition
  (`highEpisodeHorizon_one`). The strict-adjustment form
  `equilibriumTop_highEpisode_nonexit_generalF` is a corollary (BH2.3).

## What "no way back" means here, and does not (Rule 9A)

No endogenous exit along the resumed stationary equilibrium, under unchanged
primitives and the stated basin conditions. Relief stays feasible — the
transition erodes entrenchment under low sanctions, and `ReliefExit.lean`
gives a sufficient duration for an imposed relief episode — but the
equilibrium does not choose it. Nothing here says every equilibrium behaves
so, that an institution could not end the regime, or that the episode was
optimal for whoever imposed it.

## Rule 1

The episode is imposed: it is the transient-shock exception, and the theorems
say so in their names. From date `T` the sanction is `R_E`, the realised rule
of a full `FeedbackStackelbergEquilibriumTop`, whose fields certify Sender
optimality (`ρ_isMaxOn`) and Target optimality (`α_opt_top`) at every
post-episode state; `Theory/Equilibrium/TopLifetimeVerification.lean` verifies
the resumed continuation game against every Markov deviation. The proofs
below consume only `E.V_S` and `E.α`; the equilibrium object is what makes
the consumed rule an equilibrium rule.

## Rule 3

No new assumption. Every hypothesis is a theorem parameter already in use:
strict adjustment (F5), the weak-floor basin package of
`Theory/Basin/WeakFloorBasin.lean`, the joint-preference basin, and a
schedule bound. The horizon `highEpisodeHorizon` is derived, not supplied.
Since 2026-10-06 the episode theorems also come in localised forms: held-sanction
ascent on `[0, x̄]` (the ascent half of F5, read only below the basin; F5 with
`x̄ < h ≤ 1` implies it) in place of F5 (BH2.3), and the ratchet `x ≤ R_E x`
with a monotone rule in place of the joint basin (BH2.1). Each is implied by
the hypotheses it replaces, as the one-line corollaries record.

## Rule 11 — two refutations, in §5

* A floor *equal* to the pivot need not enter in finite time: under the affine
  law with rate in `(0, 1)`, sanction `h = x̄` from `0` stays strictly below `x̄`
  at every date. The strict inequality `x̄ < h` is substantive; in the localised
  form, ascent at `x̄` itself cannot be dropped.
* There is no uniformly small duration: for every `T` and pivot `b ∈ (0, 1]`
  there is an affine rate at which `T` periods of full sanction from `0` end
  below `b`. "Finite" means "long enough for the economy", never "a few".

## Rule 22

General in `F`: every successor is `p.F`, the drift is read off `F(·, h)`, and
the post-episode path is `dynamicTopLockInPathF`. The refutations in §5 use
`affineF` because they are refutations, which need one economy.
-/
import Sanctions.Theory.LockIn.LockIn
import Sanctions.Theory.LockIn.ReliefExit
import Sanctions.Theory.Basin.WeakFloorBasin
import Sanctions.Foundations.TransitionChords
import Sanctions.Foundations.ControlledRecursion

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 1. The imposed episode -/

/-- The state path under an imposed sanction schedule `u`, evolved by `p.F`:
`y₀ = x₀`, `y_{n+1} = F(y_n, u_n)`. -/
def episodePath (u : ℕ → ℝ) (x₀ : ℝ) : ℕ → ℝ :=
  ControlledRecursion.controlledPath p.F u x₀

@[simp] theorem episodePath_zero (u : ℕ → ℝ) (x₀ : ℝ) : p.episodePath u x₀ 0 = x₀ := rfl

@[simp] theorem episodePath_succ (u : ℕ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.episodePath u x₀ (n + 1) = p.F (p.episodePath u x₀ n) (u n) := rfl

/-- A feasible schedule from a feasible start keeps the state feasible. -/
theorem episodePath_mem {u : ℕ → ℝ} (hu : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n, p.episodePath u x₀ n ∈ Set.Icc (0 : ℝ) 1 :=
  ControlledRecursion.controlledPath_mem_Icc p.F_mem hu hx₀

/-- The maximal schedule is the full-shock path of `LockIn.lean`. -/
theorem episodePath_const_one (x₀ : ℝ) :
    ∀ n, p.episodePath (fun _ => 1) x₀ n = p.shockPathF x₀ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [episodePath_succ, shockPathF_succ, ih]; rfl

/-- The zero schedule is the full-relief path of `ReliefExit.lean`. -/
theorem episodePath_const_zero (x₀ : ℝ) :
    ∀ n, p.episodePath (fun _ => 0) x₀ n = p.reliefPathF x₀ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [episodePath_succ, reliefPathF_succ, ih]; rfl

/-! ## 2. The spliced path: imposed before `T`, the equilibrium rule from `T` -/

variable (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)

/-- The state path that follows the schedule `u` before date `T` and the
realised rule `dynamicTopRealizedRule V_S α` from date `T` on. Every successor
is `p.F`. -/
def splicedPath (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 =>
      p.F (splicedPath u T x₀ n)
        (if n < T then u n else p.dynamicTopRealizedRule V_S α (splicedPath u T x₀ n))

/-- The sanction at date `n` along the spliced path. -/
def splicedSanction (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ) (n : ℕ) : ℝ :=
  if n < T then u n else p.dynamicTopRealizedRule V_S α (p.splicedPath V_S α u T x₀ n)

@[simp] theorem splicedPath_zero (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ) :
    p.splicedPath V_S α u T x₀ 0 = x₀ := rfl

theorem splicedPath_succ (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ) (n : ℕ) :
    p.splicedPath V_S α u T x₀ (n + 1) =
      p.F (p.splicedPath V_S α u T x₀ n) (p.splicedSanction V_S α u T x₀ n) := rfl

theorem splicedSanction_of_lt {u : ℕ → ℝ} {T : ℕ} (x₀ : ℝ) {n : ℕ} (hn : n < T) :
    p.splicedSanction V_S α u T x₀ n = u n := if_pos hn

theorem splicedSanction_of_not_lt {u : ℕ → ℝ} {T : ℕ} (x₀ : ℝ) {n : ℕ} (hn : ¬ n < T) :
    p.splicedSanction V_S α u T x₀ n =
      p.dynamicTopRealizedRule V_S α (p.splicedPath V_S α u T x₀ n) := if_neg hn

/-- Before and at date `T` the spliced path is the episode path. -/
theorem splicedPath_eq_episode (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ) :
    ∀ n ≤ T, p.splicedPath V_S α u T x₀ n = p.episodePath u x₀ n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [splicedPath_succ, episodePath_succ, ih (Nat.le_of_succ_le hn),
      p.splicedSanction_of_lt V_S α x₀ (Nat.lt_of_succ_le hn)]

/-- **The splice identity.** From date `T` the spliced path is the general-`F`
equilibrium path restarted at the episode-end state. -/
theorem splicedPath_add (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ) :
    ∀ n, p.splicedPath V_S α u T x₀ (T + n) =
      p.dynamicTopLockInPathF V_S α (p.episodePath u x₀ T) n := by
  intro n
  induction n with
  | zero => simpa using p.splicedPath_eq_episode V_S α u T x₀ T le_rfl
  | succ n ih =>
    have hnot : ¬ (T + n < T) := Nat.not_lt.2 (Nat.le_add_right T n)
    change p.F (p.splicedPath V_S α u T x₀ (T + n)) (p.splicedSanction V_S α u T x₀ (T + n)) = _
    rw [p.splicedSanction_of_not_lt V_S α x₀ hnot, ih, dynamicTopLockInPathF_succ]
    rfl

/-- From date `T` the spliced sanctions are the general-`F` equilibrium
sanctions restarted at the episode-end state. -/
theorem splicedSanction_add (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ) :
    ∀ n, p.splicedSanction V_S α u T x₀ (T + n) =
      p.dynamicTopLockInSanctionsF V_S α (p.episodePath u x₀ T) n := by
  intro n
  rw [p.splicedSanction_of_not_lt V_S α x₀ (Nat.not_lt.2 (Nat.le_add_right T n)),
    p.splicedPath_add V_S α u T x₀ n]
  rfl

/-! ## 3. Conditional non-exit after the episode -/

/-- **No endogenous exit after a finite episode** (conditional, general in `F`).

Given a full equilibrium `E`, an imposed schedule `u` of length `T`, and a
region `[x̄, 1]` that the resumed rule preserves — a level floor `s̄` on the
rule over `[x̄, 1]` and the lower-edge condition `x̄ ≤ F(x̄, s̄)` (free when
`x̄ ≤ s̄`, by `corner_of_pivot_le_floor`) — if the episode ends inside `[x̄, 1]`
then along the resumed equilibrium the state stays in `[x̄, 1]`, the sanction
never falls below `s̄`, and no relief cutoff strictly below `s̄` is ever
reached. Nothing is said about the dates before `T`, at which the sanction is
imposed and not chosen.

No sign condition on `x̄`: the hypothesis `0 ≤ x̄` was dropped on 2026-10-06
(BG2.1). It was read only by the weak-floor invariance lemma, whose upper
basin edge now comes from `F_le_one_of_le` (on all of `ℝ`) instead of `F_mem`.
The region `[x̄, 1]` may therefore be any upper interval the resumed rule
preserves. -/
theorem equilibriumTop_post_episode_nonexit_generalF
    (E : p.FeedbackStackelbergEquilibriumTop) (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ)
    {xbar sbar : ℝ} (hCorner : xbar ≤ p.F xbar sbar)
    (hWeak : ∀ x ∈ Set.Icc xbar (1 : ℝ), sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    (hT : p.episodePath u x₀ T ∈ Set.Icc xbar 1) :
    (∀ n, p.splicedPath E.V_S E.α u T x₀ (T + n) ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.splicedSanction E.V_S E.α u T x₀ (T + n)) ∧
    (∀ q, q < sbar → ∀ n, ¬ p.splicedSanction E.V_S E.α u T x₀ (T + n) ≤ q) := by
  have hpath := p.weakFloor_dynamicTopPathF_mem_basin E.V_S E.α hCorner hWeak hT
  have hmem : ∀ n, p.splicedPath E.V_S E.α u T x₀ (T + n) ∈ Set.Icc xbar 1 := by
    intro n
    rw [p.splicedPath_add]
    exact hpath n
  have hfloor : ∀ n, sbar ≤ p.splicedSanction E.V_S E.α u T x₀ (T + n) := by
    intro n
    rw [p.splicedSanction_add]
    exact hWeak _ (hpath n)
  exact ⟨hmem, hfloor, fun q hq n hle => absurd (le_trans (hfloor n) hle) (not_le.2 hq)⟩

/-- **The inherited floor and no relief after the episode, from the ratchet
alone** (general in `F`; BH2.1, 2026-10-06). If the episode ends inside a basin
`[x̄, 1]` on which the resumed equilibrium rule is weakly above the state
(`x ≤ R_E x`), then along the resumed equilibrium the sanction stays at or
above the inherited level `max (y_T) x̄` and never reaches any cutoff strictly
below it. Nothing else about the basin is used: no `0 ≤ x̄`, no sanction floor,
no interval dominance (A1) and no Target sanction preference (P4). -/
theorem equilibriumTop_post_episode_floor_no_relief_of_ratchet
    (E : p.FeedbackStackelbergEquilibriumTop) (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ)
    {xbar q : ℝ}
    (h_ratchet : ∀ x ∈ Set.Icc xbar (1 : ℝ), x ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    (hT : p.episodePath u x₀ T ∈ Set.Icc xbar 1)
    (hq : q < max (p.episodePath u x₀ T) xbar) :
    (∀ n, max (p.episodePath u x₀ T) xbar ≤ p.splicedSanction E.V_S E.α u T x₀ (T + n)) ∧
    (∀ n, ¬ p.splicedSanction E.V_S E.α u T x₀ (T + n) ≤ q) := by
  have hfloor : ∀ n,
      max (p.episodePath u x₀ T) xbar ≤ p.splicedSanction E.V_S E.α u T x₀ (T + n) := by
    intro n
    rw [p.splicedSanction_add]
    exact p.dynamicTopLockInSanctionsF_ge_entry E.V_S E.α h_ratchet hT n
  exact ⟨hfloor, fun n hle => absurd (le_trans (hfloor n) hle) (not_le.2 hq)⟩

/-- **The stronger tail from the ratchet and a monotone rule** (general in `F`;
BH2.1, 2026-10-06). The conclusion of
`equilibriumTop_post_episode_no_relief_of_jointBasin`: the post-episode sanction
stays at or above the inherited episode-end level, is nondecreasing, and never
reaches any cutoff strictly below that level. Of the joint basin only two
consequences are read: the ratchet `x ≤ R_E x` (floor and no relief) and
monotonicity of `R_E` on the basin (the nondecreasing tail, P3). Dropped: the
other basin fields, among them `0 ≤ x̄`, Target-policy feasibility and
optimality (supplied by `E` itself) and the Target's sanction preference (P4). -/
theorem equilibriumTop_post_episode_no_relief_of_ratchet
    (E : p.FeedbackStackelbergEquilibriumTop) (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ)
    {xbar q : ℝ}
    (h_ratchet : ∀ x ∈ Set.Icc xbar (1 : ℝ), x ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    (h_mono : MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α) (Set.Icc xbar 1))
    (hT : p.episodePath u x₀ T ∈ Set.Icc xbar 1)
    (hq : q < max (p.episodePath u x₀ T) xbar) :
    (∀ n, max (p.episodePath u x₀ T) xbar ≤ p.splicedSanction E.V_S E.α u T x₀ (T + n)) ∧
    Monotone (fun n => p.splicedSanction E.V_S E.α u T x₀ (T + n)) ∧
    (∀ n, ¬ p.splicedSanction E.V_S E.α u T x₀ (T + n) ≤ q) := by
  obtain ⟨hfloor, hno⟩ :=
    p.equilibriumTop_post_episode_floor_no_relief_of_ratchet E u T x₀ h_ratchet hT hq
  refine ⟨hfloor, fun m n hmn => ?_, hno⟩
  simp only
  rw [p.splicedSanction_add, p.splicedSanction_add]
  exact p.dynamicTopLockInSanctionsF_mono E.V_S E.α
    (p.dynamicTopRealizedRule_level_of_ratchet E.V_S E.α h_ratchet) h_mono hT hmn

/-- **The stronger tail under the joint-preference basin.** With the full
basin package, the post-episode sanction stays at or above the inherited
episode-end state (and the pivot), is nondecreasing, and never reaches any
cutoff strictly below that inherited level. Since BH2.1 (2026-10-06) a one-line
corollary of `equilibriumTop_post_episode_no_relief_of_ratchet`: the basin is
read only through the ratchet and `top_rule_mono`. Statement unchanged. -/
theorem equilibriumTop_post_episode_no_relief_of_jointBasin
    (E : p.FeedbackStackelbergEquilibriumTop) (u : ℕ → ℝ) (T : ℕ) (x₀ : ℝ)
    {xbar sbar q : ℝ}
    (hB : p.JointPreferenceBasinTop E.V_T E.V_S E.α xbar sbar)
    (hT : p.episodePath u x₀ T ∈ Set.Icc xbar 1)
    (hq : q < max (p.episodePath u x₀ T) xbar) :
    (∀ n, max (p.episodePath u x₀ T) xbar ≤ p.splicedSanction E.V_S E.α u T x₀ (T + n)) ∧
    Monotone (fun n => p.splicedSanction E.V_S E.α u T x₀ (T + n)) ∧
    (∀ n, ¬ p.splicedSanction E.V_S E.α u T x₀ (T + n) ≤ q) :=
  p.equilibriumTop_post_episode_no_relief_of_ratchet E u T x₀
    (JointPreferenceBasinTop.ratchet_dyn_top p hB) hB.top_rule_mono hT hq

/-- **A maximal episode of the canonical length is enough.** Under strict
adjustment, from every feasible start, an imposed full-sanction schedule of
length `T ≥ fullShockEntryHorizon x̄` ends in `[x̄, 1]`; the conditional
non-exit then follows. The localised sibling
`equilibriumTop_fullShock_episode_nonexit_generalF_of_preBasinAscent` (§4,
BH2.3) replaces strict adjustment and `x̄ < 1` by full-sanction ascent on
`[0, x̄]` alone. -/
theorem equilibriumTop_fullShock_episode_nonexit_generalF
    (E : p.FeedbackStackelbergEquilibriumTop) (hAdj : p.StrictAdjustment)
    {xbar sbar : ℝ} (hxbar : xbar ∈ Set.Ico (0 : ℝ) 1) (hCorner : xbar ≤ p.F xbar sbar)
    (hWeak : ∀ x ∈ Set.Icc xbar (1 : ℝ), sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) {T : ℕ} (hT : p.fullShockEntryHorizon xbar ≤ T) :
    (∀ n, p.splicedPath E.V_S E.α (fun _ => 1) T x₀ (T + n) ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.splicedSanction E.V_S E.α (fun _ => 1) T x₀ (T + n)) ∧
    (∀ q, q < sbar → ∀ n, ¬ p.splicedSanction E.V_S E.α (fun _ => 1) T x₀ (T + n) ≤ q) := by
  have hend : p.episodePath (fun _ => 1) x₀ T ∈ Set.Icc xbar 1 := by
    rw [p.episodePath_const_one]
    exact p.shockPathF_uniform_fullShockEntryHorizon_of_strictAdjustment hAdj hxbar x₀ hx₀ T hT
  exact p.equilibriumTop_post_episode_nonexit_generalF E _ T x₀ hCorner hWeak hend

/-! ## 4. Non-maximal episodes: a sanction floor strictly above the pivot -/

/-- The one-period state gain under a sanction held at `h`. -/
def highEpisodeDrift (h x : ℝ) : ℝ := p.F x h - x

/-- `η_h(b)`: the minimum of `F(x, h) − x` over `[0, b]`. -/
def highEpisodeMinDrift (h b : ℝ) : ℝ :=
  sInf (p.highEpisodeDrift h '' Set.Icc (0 : ℝ) b)

/-- `N_h(b) = ⌈b / η_h(b)⌉`: the conservative sufficient duration for an
episode whose sanctions stay at or above `h`. -/
def highEpisodeHorizon (h b : ℝ) : ℕ :=
  Nat.ceil (b / p.highEpisodeMinDrift h b)

/-- At `h = 1` the objects are the full-shock objects of `LockIn.lean`, by
definition. -/
theorem highEpisodeDrift_one : p.highEpisodeDrift 1 = p.fullShockDrift := rfl

theorem highEpisodeMinDrift_one (b : ℝ) : p.highEpisodeMinDrift 1 b = p.fullShockMinDrift b := rfl

theorem highEpisodeHorizon_one (b : ℝ) :
    p.highEpisodeHorizon 1 b = p.fullShockEntryHorizon b := rfl

/-! ### Held-sanction ascent (BH2.3, 2026-10-06)

The episode theorems of this section used to take strict adjustment (F5, two
sided, on the whole feasible square) together with `b < h ≤ 1`. Their proofs
read F5 once, at the minimiser of the drift on `[0, b]`, and only its ascent
half: the held sanction strictly lifts the state. The siblings below take
exactly that,

  `hF_held_pre : ∀ x ∈ [0, b], x < F(x, h)`

("held-sanction ascent below the basin"). It forces `b < h` when `0 ≤ b`
(`lt_of_heldAscent`), F5 with `b < h ≤ 1` implies it
(`heldAscent_of_strictAdjustment`), and for `0 < b` it is also necessary for
entry at the canonical horizon (`heldAscent_of_uniform_highEpisodeHorizon_entry`).
At `h = 1` it is the pre-basin ascent `hF_top_pre` of
`LocalisedShockEntry.lean`. The interval is closed for the same reason as
there: on `[0, b)` the drift may have infimum zero. General in `F`. -/

/-- **A held sanction that lifts every state of `[0, b]` lies above `b`.** If
`0 ≤ b` and `x < F(x, h)` on `[0, b]`, then `b < h`. Otherwise `h ≤ b`, and the
successor `F(b, h)` lies between `h` and `b` (`F_mem_uIcc`, from monotonicity
and the diagonal), so `F(b, h) ≤ b`. Mirror of `lt_one_of_lt_F_one`. General
in `F`. -/
theorem lt_of_heldAscent {h b : ℝ} (hb0 : 0 ≤ b)
    (hF_held_pre : ∀ x ∈ Set.Icc (0 : ℝ) b, x < p.F x h) : b < h := by
  by_contra hle
  have hhb : h ≤ b := not_lt.mp hle
  have hmem := p.F_mem_uIcc b h
  rw [Set.uIcc_of_ge hhb] at hmem
  linarith [hmem.2, hF_held_pre b ⟨hb0, le_rfl⟩]

/-- **Strict adjustment implies held-sanction ascent** below any `b < h ≤ 1`:
the ascent half of F5, read on `[0, b]` only. This is the implication that
makes every `_of_heldAscent` theorem a weakening of its F5 sibling. General
in `F`. -/
theorem heldAscent_of_strictAdjustment (hAdj : p.StrictAdjustment) {h b : ℝ}
    (hbh : b < h) (hh1 : h ≤ 1) : ∀ x ∈ Set.Icc (0 : ℝ) b, x < p.F x h :=
  fun _ hx => hAdj.2 ⟨hx.1, hx.2.trans (hbh.le.trans hh1)⟩
    ⟨hx.1.trans (hx.2.trans hbh.le), hh1⟩ (hx.2.trans_lt hbh)

/-- **Positive attained drift below the pivot from held-sanction ascent.**
Continuity gives attainment on the compact `[0, b]`; ascent at the minimiser
gives positivity. Against `highEpisodeDrift_exists_pos_isMinOn`, strict
adjustment, `b < h` and `h ≤ 1` are replaced by ascent on `[0, b]`. General in
`F`. -/
theorem highEpisodeDrift_exists_pos_isMinOn_of_heldAscent
    {h b : ℝ} (hb0 : 0 ≤ b) (hF_held_pre : ∀ x ∈ Set.Icc (0 : ℝ) b, x < p.F x h) :
    ∃ η : ℝ, 0 < η ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) b, η = p.highEpisodeDrift h xmin) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) b, η ≤ p.highEpisodeDrift h x := by
  have hcont : Continuous (p.highEpisodeDrift h) := by
    have hpair : Continuous (fun x : ℝ => (x, h)) := by fun_prop
    exact (p.F_continuous.comp hpair).sub continuous_id
  obtain ⟨xmin, hxmin, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hb0) hcont.continuousOn
  refine ⟨p.highEpisodeDrift h xmin, ?_, ⟨xmin, hxmin, rfl⟩, fun x hx => hmin hx⟩
  have hlt := hF_held_pre xmin hxmin
  unfold highEpisodeDrift
  linarith

/-- **Positive attained drift below the pivot under a sanction strictly above
it.** Continuity gives attainment on the compact `[0, b]`; strict adjustment
gives positivity, since every `x ≤ b < h` satisfies `x < F(x, h)`. Since BH2.3
(2026-10-06) a one-line corollary of
`highEpisodeDrift_exists_pos_isMinOn_of_heldAscent`. Statement unchanged. -/
theorem highEpisodeDrift_exists_pos_isMinOn (hAdj : p.StrictAdjustment)
    {h b : ℝ} (hb0 : 0 ≤ b) (hbh : b < h) (hh1 : h ≤ 1) :
    ∃ η : ℝ, 0 < η ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) b, η = p.highEpisodeDrift h xmin) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) b, η ≤ p.highEpisodeDrift h x :=
  p.highEpisodeDrift_exists_pos_isMinOn_of_heldAscent hb0
    (p.heldAscent_of_strictAdjustment hAdj hbh hh1)

/-- **The canonical minimum drift is positive and attained, from held-sanction
ascent.** Against `highEpisodeMinDrift_pos_attains_isMinOn`, strict adjustment,
`b < h` and `h ≤ 1` are replaced by ascent on `[0, b]`. General in `F`. -/
theorem highEpisodeMinDrift_pos_attains_isMinOn_of_heldAscent
    {h b : ℝ} (hb0 : 0 ≤ b) (hF_held_pre : ∀ x ∈ Set.Icc (0 : ℝ) b, x < p.F x h) :
    0 < p.highEpisodeMinDrift h b ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) b, p.highEpisodeMinDrift h b = p.highEpisodeDrift h xmin) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) b, p.highEpisodeMinDrift h b ≤ p.highEpisodeDrift h x := by
  obtain ⟨η, hη_pos, ⟨xmin, hxmin, hη_eq⟩, hη_min⟩ :=
    p.highEpisodeDrift_exists_pos_isMinOn_of_heldAscent hb0 hF_held_pre
  have hne : (p.highEpisodeDrift h '' Set.Icc (0 : ℝ) b).Nonempty :=
    ⟨p.highEpisodeDrift h xmin, ⟨xmin, hxmin, rfl⟩⟩
  have hbdd : BddBelow (p.highEpisodeDrift h '' Set.Icc (0 : ℝ) b) := by
    refine ⟨η, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hη_min x hx
  have hle : p.highEpisodeMinDrift h b ≤ η :=
    csInf_le hbdd ⟨xmin, hxmin, hη_eq.symm⟩
  have hge : η ≤ p.highEpisodeMinDrift h b := by
    apply le_csInf hne
    rintro y ⟨x, hx, rfl⟩
    exact hη_min x hx
  have heq : p.highEpisodeMinDrift h b = η := le_antisymm hle hge
  refine ⟨heq ▸ hη_pos, ⟨xmin, hxmin, heq.trans hη_eq⟩, ?_⟩
  intro x hx
  rw [heq]
  exact hη_min x hx

/-- **The canonical minimum drift is positive and attained.** Since BH2.3
(2026-10-06) a one-line corollary of
`highEpisodeMinDrift_pos_attains_isMinOn_of_heldAscent`. Statement unchanged. -/
theorem highEpisodeMinDrift_pos_attains_isMinOn (hAdj : p.StrictAdjustment)
    {h b : ℝ} (hb0 : 0 ≤ b) (hbh : b < h) (hh1 : h ≤ 1) :
    0 < p.highEpisodeMinDrift h b ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) b, p.highEpisodeMinDrift h b = p.highEpisodeDrift h xmin) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) b, p.highEpisodeMinDrift h b ≤ p.highEpisodeDrift h x :=
  p.highEpisodeMinDrift_pos_attains_isMinOn_of_heldAscent hb0
    (p.heldAscent_of_strictAdjustment hAdj hbh hh1)

/-- **Entry from a drift floor.** A feasible schedule with sanctions at or
above `h` before `T`, a positive drift floor `η` on `[0, b]` under the held
sanction `h`, and `T ≥ ⌈b/η⌉` end in `[b, 1]` from every feasible start. The
driven path need not be monotone; the comparison is with the held path. -/
theorem episodePath_natCeil_entry_of_drift
    {u : ℕ → ℝ} {h b η : ℝ} {T : ℕ} (hh0 : 0 ≤ h) (hη_pos : 0 < η)
    (hη : ∀ x ∈ Set.Icc (0 : ℝ) b, η ≤ p.highEpisodeDrift h x)
    (hu_mem : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) (hu : ∀ n < T, h ≤ u n)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) (hT : Nat.ceil (b / η) ≤ T) :
    p.episodePath u x₀ T ∈ Set.Icc b 1 :=
  ⟨ControlledRecursion.controlledPath_ge_of_high_inputs p.F_mono_x p.F_mono_s p.F_diag
      hh0 hη_pos hη hu hx₀.1 T hT le_rfl,
    (p.episodePath_mem hu_mem hx₀ T).2⟩

/-- **The canonical horizon guarantees entry under held-sanction ascent** for
every feasible schedule held at or above `h` for at least
`highEpisodeHorizon h b` periods, from every feasible start. Against
`episodePath_uniform_highEpisodeHorizon_entry`, strict adjustment, `b < h` and
`h ≤ 1` are replaced by ascent on `[0, b]`; `0 ≤ h` comes from
`lt_of_heldAscent`. General in `F`. -/
theorem episodePath_uniform_highEpisodeHorizon_entry_of_heldAscent
    {h b : ℝ} (hb0 : 0 ≤ b) (hF_held_pre : ∀ x ∈ Set.Icc (0 : ℝ) b, x < p.F x h)
    {u : ℕ → ℝ} (hu_mem : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) {T : ℕ} (hu : ∀ n < T, h ≤ u n)
    (hT : p.highEpisodeHorizon h b ≤ T) {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    p.episodePath u x₀ T ∈ Set.Icc b 1 := by
  obtain ⟨hη_pos, _, hη_min⟩ :=
    p.highEpisodeMinDrift_pos_attains_isMinOn_of_heldAscent hb0 hF_held_pre
  exact p.episodePath_natCeil_entry_of_drift
    (le_trans hb0 (p.lt_of_heldAscent hb0 hF_held_pre).le) hη_pos hη_min hu_mem hu hx₀ hT

/-- **The canonical horizon guarantees entry** for every schedule held at or
above `h > b` for at least `highEpisodeHorizon h b` periods. Since BH2.3
(2026-10-06) a one-line corollary of
`episodePath_uniform_highEpisodeHorizon_entry_of_heldAscent`. Statement
unchanged. -/
theorem episodePath_uniform_highEpisodeHorizon_entry (hAdj : p.StrictAdjustment)
    {h b : ℝ} (hb0 : 0 ≤ b) (hbh : b < h) (hh1 : h ≤ 1)
    {u : ℕ → ℝ} (hu_mem : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) {T : ℕ} (hu : ∀ n < T, h ≤ u n)
    (hT : p.highEpisodeHorizon h b ≤ T) {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    p.episodePath u x₀ T ∈ Set.Icc b 1 :=
  p.episodePath_uniform_highEpisodeHorizon_entry_of_heldAscent hb0
    (p.heldAscent_of_strictAdjustment hAdj hbh hh1) hu_mem hu hT hx₀

/-- **Held-sanction ascent is necessary for entry at the canonical horizon**
(for `0 < b`). If every feasible schedule held at or above `h` for
`highEpisodeHorizon h b` or more periods ends in `[b, 1]` from every feasible
start, then `x < F(x, h)` on `[0, b]`. Otherwise some `x* ∈ [0, b]` has
`F(x*, h) ≤ x*`, the minimum drift is `≤ 0`, the horizon `⌈b / η⌉` collapses to
`0`, and the zero-length episode from `0` ends at `0 ∉ [b, 1]`. Together with
`episodePath_uniform_highEpisodeHorizon_entry_of_heldAscent` this makes held
ascent exactly the condition for the canonical horizon to work when `b > 0`.
General in `F` (BH2.3, 2026-10-06). -/
theorem heldAscent_of_uniform_highEpisodeHorizon_entry {h b : ℝ} (hb_pos : 0 < b)
    (hentry : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (0 : ℝ) 1) → ∀ T : ℕ,
      (∀ n < T, h ≤ u n) → p.highEpisodeHorizon h b ≤ T →
      ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, p.episodePath u x₀ T ∈ Set.Icc b 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) b, x < p.F x h := by
  intro xs hxs
  by_contra hnot
  have hFxs : p.F xs h ≤ xs := not_lt.mp hnot
  have hcont : Continuous (p.highEpisodeDrift h) := by
    have hpair : Continuous (fun x : ℝ => (x, h)) := by fun_prop
    exact (p.F_continuous.comp hpair).sub continuous_id
  have hbdd : BddBelow (p.highEpisodeDrift h '' Set.Icc (0 : ℝ) b) :=
    (isCompact_Icc.image hcont).bddBelow
  have hη_le : p.highEpisodeMinDrift h b ≤ 0 := by
    have hle : p.highEpisodeMinDrift h b ≤ p.highEpisodeDrift h xs :=
      csInf_le hbdd ⟨xs, hxs, rfl⟩
    have hdrift : p.highEpisodeDrift h xs ≤ 0 := by
      unfold highEpisodeDrift
      linarith
    exact hle.trans hdrift
  have hzero : p.highEpisodeHorizon h b = 0 := by
    unfold highEpisodeHorizon
    exact Nat.ceil_eq_zero.2 (div_nonpos_iff.2 (Or.inl ⟨hb_pos.le, hη_le⟩))
  have h0 := hentry (fun _ => 0) (fun _ => ⟨le_rfl, zero_le_one⟩) 0
    (fun n hn => absurd hn (Nat.not_lt_zero n)) hzero.le 0 ⟨le_rfl, zero_le_one⟩
  have hb_le : b ≤ 0 := h0.1
  linarith

/-- **A sufficiently long non-maximal episode, then no endogenous exit, under
held-sanction ascent** (general in `F`; BH2.3, 2026-10-06). Given a full
equilibrium `E`, a region `[x̄, 1]` with `0 ≤ x̄` that the resumed rule
preserves (`x̄ ≤ F(x̄, s̄)` and `s̄ ≤ R_E` on `[x̄, 1]`), and a held sanction `h`
that strictly lifts every state of `[0, x̄]`: every feasible schedule held at or
above `h` for at least `highEpisodeHorizon h x̄` periods ends in `[x̄, 1]`, after
which the resumed equilibrium keeps the state in `[x̄, 1]`, the sanction at or
above `s̄`, and never reaches a cutoff below `s̄`.

Against `equilibriumTop_highEpisode_nonexit_generalF`, strict adjustment (F5),
`x̄ < h` and `h ≤ 1` are replaced by ascent on `[0, x̄]`; `x̄ < h` is derived
(`lt_of_heldAscent`) and `h ≤ 1` was never used. So `thm:finite-episode` needs
no part of F5 beyond this local ascent. -/
theorem equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent
    (E : p.FeedbackStackelbergEquilibriumTop)
    {h xbar sbar : ℝ} (hxbar0 : 0 ≤ xbar)
    (hF_held_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x h)
    (hCorner : xbar ≤ p.F xbar sbar)
    (hWeak : ∀ x ∈ Set.Icc xbar (1 : ℝ), sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    {u : ℕ → ℝ} (hu_mem : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) {T : ℕ} (hu : ∀ n < T, h ≤ u n)
    (hT : p.highEpisodeHorizon h xbar ≤ T) {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n, p.splicedPath E.V_S E.α u T x₀ (T + n) ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.splicedSanction E.V_S E.α u T x₀ (T + n)) ∧
    (∀ q, q < sbar → ∀ n, ¬ p.splicedSanction E.V_S E.α u T x₀ (T + n) ≤ q) :=
  p.equilibriumTop_post_episode_nonexit_generalF E u T x₀ hCorner hWeak
    (p.episodePath_uniform_highEpisodeHorizon_entry_of_heldAscent hxbar0 hF_held_pre
      hu_mem hu hT hx₀)

/-- **A sufficiently long non-maximal episode, then no endogenous exit.** Since
BH2.3 (2026-10-06) a one-line corollary of
`equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent`, through
`heldAscent_of_strictAdjustment`. Statement unchanged. -/
theorem equilibriumTop_highEpisode_nonexit_generalF
    (E : p.FeedbackStackelbergEquilibriumTop) (hAdj : p.StrictAdjustment)
    {h xbar sbar : ℝ} (hxbar0 : 0 ≤ xbar) (hxh : xbar < h) (hh1 : h ≤ 1)
    (hCorner : xbar ≤ p.F xbar sbar)
    (hWeak : ∀ x ∈ Set.Icc xbar (1 : ℝ), sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    {u : ℕ → ℝ} (hu_mem : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) {T : ℕ} (hu : ∀ n < T, h ≤ u n)
    (hT : p.highEpisodeHorizon h xbar ≤ T) {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n, p.splicedPath E.V_S E.α u T x₀ (T + n) ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.splicedSanction E.V_S E.α u T x₀ (T + n)) ∧
    (∀ q, q < sbar → ∀ n, ¬ p.splicedSanction E.V_S E.α u T x₀ (T + n) ≤ q) :=
  p.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent E hxbar0
    (p.heldAscent_of_strictAdjustment hAdj hxh hh1) hCorner hWeak hu_mem hu hT hx₀

/-- **A maximal episode of the canonical length is enough, under pre-basin
ascent** (general in `F`; the `h = 1` sibling of
`equilibriumTop_fullShock_episode_nonexit_generalF`, BH2.3, 2026-10-06). If
`0 ≤ x̄` and a full sanction strictly lifts every state of `[0, x̄]`, an imposed
full-sanction schedule of length `T ≥ fullShockEntryHorizon x̄` ends in
`[x̄, 1]` from every feasible start, and the conditional non-exit follows.
Against the sibling, strict adjustment and `x̄ < 1` are replaced by this ascent
(`x̄ < 1` is derived). It is
`equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent` at `h = 1`, where
the canonical horizon is the full-shock horizon by definition
(`highEpisodeHorizon_one`); the hypothesis is `hF_top_pre` of
`LocalisedShockEntry.lean`. -/
theorem equilibriumTop_fullShock_episode_nonexit_generalF_of_preBasinAscent
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xbar sbar : ℝ} (hxbar0 : 0 ≤ xbar)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1)
    (hCorner : xbar ≤ p.F xbar sbar)
    (hWeak : ∀ x ∈ Set.Icc xbar (1 : ℝ), sbar ≤ p.dynamicTopRealizedRule E.V_S E.α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) {T : ℕ} (hT : p.fullShockEntryHorizon xbar ≤ T) :
    (∀ n, p.splicedPath E.V_S E.α (fun _ => 1) T x₀ (T + n) ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.splicedSanction E.V_S E.α (fun _ => 1) T x₀ (T + n)) ∧
    (∀ q, q < sbar → ∀ n, ¬ p.splicedSanction E.V_S E.α (fun _ => 1) T x₀ (T + n) ≤ q) :=
  p.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent E hxbar0 hF_top_pre hCorner hWeak
    (fun _ => ⟨zero_le_one, le_rfl⟩) (fun _ _ => le_rfl)
    (by rw [highEpisodeHorizon_one]; exact hT) hx₀

/-- **A chord certificate for the duration.** Where a lower sanction chord
`d > 0` is available, `F(x, h) − x ≥ d·(h − x) ≥ d·(h − b)` on `[0, b]`, so
`⌈b / (d(h − b))⌉` is an explicit sufficient duration. It is looser than the
canonical horizon and needs the chord; the canonical horizon needs only
held-sanction ascent on `[0, b]`
(`episodePath_uniform_highEpisodeHorizon_entry_of_heldAscent`). -/
theorem episodePath_entry_of_lowerChord
    {d : ℝ} (hlo : Sanctions.TransitionChords.SanctionLowerChord p.F d) (hd0 : 0 < d)
    {h b : ℝ} (hb0 : 0 ≤ b) (hbh : b < h) (hh1 : h ≤ 1)
    {u : ℕ → ℝ} (hu_mem : ∀ n, u n ∈ Set.Icc (0 : ℝ) 1) {T : ℕ} (hu : ∀ n < T, h ≤ u n)
    (hT : Nat.ceil (b / (d * (h - b))) ≤ T) {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc (0 : ℝ) 1) :
    p.episodePath u x₀ T ∈ Set.Icc b 1 := by
  have hη_pos : 0 < d * (h - b) := mul_pos hd0 (sub_pos.2 hbh)
  have hη : ∀ x ∈ Set.Icc (0 : ℝ) b, d * (h - b) ≤ p.highEpisodeDrift h x := by
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_trans hx.2 (le_trans hbh.le hh1)⟩
    have hhI : h ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hb0 hbh.le, hh1⟩
    have hchord := hlo hxI hxI hhI (le_trans hx.2 hbh.le)
    have hdiag : p.F x x = x := p.F_diag x
    have hmono : d * (h - b) ≤ d * (h - x) :=
      mul_le_mul_of_nonneg_left (by linarith [hx.2]) hd0.le
    unfold highEpisodeDrift
    linarith
  exact p.episodePath_natCeil_entry_of_drift (le_trans hb0 hbh.le) hη_pos hη hu_mem hu hx₀ hT

/-! ## 5. Rule 11 — two refutations that delimit the theorem -/

/-- **A floor equal to the pivot need not enter in finite time.** Under the
affine law with rate `δ < 1` (the economic case is `δ ∈ (0, 1)`; positivity is
not needed), a sanction held at `b > 0` from state `0` stays strictly below
`b` at every date. The strict inequality `x̄ < h` in
`equilibriumTop_highEpisode_nonexit_generalF` is therefore substantive. -/
theorem heldPath_affine_eq_pivot_never_enters_counterexample
    {δ b : ℝ} (hδ1 : δ < 1) (hb : 0 < b) :
    ∀ t, ControlledRecursion.heldPath (affineF δ) b 0 t < b := by
  intro t
  induction t with
  | zero => simpa using hb
  | succ t ih =>
    rw [ControlledRecursion.heldPath_succ]
    simp only [affineF]
    nlinarith [mul_pos (sub_pos.2 hδ1) (sub_pos.2 ih)]

/-- **There is no uniformly small duration.** For every `T` and every pivot
`b ∈ (0, 1]` there is an affine rate at which `T` periods of full sanction
from state `0` end strictly below `b`. "Finite" is "long enough for the
economy", never a preassigned number of periods. -/
theorem no_uniform_short_duration_counterexample (T : ℕ) {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ControlledRecursion.heldPath (affineF δ) 1 0 T < b := by
  have hden : (0 : ℝ) < 2 * ((T : ℝ) + 1) := by positivity
  set δ : ℝ := b / (2 * ((T : ℝ) + 1)) with hδ
  have hδ0 : 0 < δ := div_pos hb0 hden
  have hδ_le : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ hden]
    nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  have hbound : ∀ t : ℕ,
      0 ≤ ControlledRecursion.heldPath (affineF δ) 1 0 t ∧
      ControlledRecursion.heldPath (affineF δ) 1 0 t ≤ (t : ℝ) * δ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [ControlledRecursion.heldPath_succ]
      simp only [affineF]
      push_cast
      constructor
      · nlinarith [ih.1, ih.2, hδ0, hδ_le]
      · nlinarith [ih.1, ih.2, hδ0, hδ_le]
  refine ⟨δ, hδ0, by linarith, ?_⟩
  have hTδ : (T : ℝ) * δ < b := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ hden]
    nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  linarith [(hbound T).2]

/-! ## Rule 10 — axiom inventory -/

#print axioms Sanctions.AbstractGame.Params.splicedPath_add
#print axioms Sanctions.AbstractGame.Params.equilibriumTop_post_episode_nonexit_generalF
#print axioms Sanctions.AbstractGame.Params.equilibriumTop_post_episode_no_relief_of_jointBasin
#print axioms Sanctions.AbstractGame.Params.equilibriumTop_fullShock_episode_nonexit_generalF
#print axioms Sanctions.AbstractGame.Params.equilibriumTop_highEpisode_nonexit_generalF
#print axioms
  Sanctions.AbstractGame.Params.equilibriumTop_highEpisode_nonexit_generalF_of_heldAscent
#print axioms
  Sanctions.AbstractGame.Params.equilibriumTop_fullShock_episode_nonexit_generalF_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.heldAscent_of_uniform_highEpisodeHorizon_entry
#print axioms Sanctions.AbstractGame.Params.equilibriumTop_post_episode_no_relief_of_ratchet
#print axioms
  Sanctions.AbstractGame.Params.equilibriumTop_post_episode_floor_no_relief_of_ratchet
#print axioms Sanctions.AbstractGame.Params.episodePath_entry_of_lowerChord
#print axioms Sanctions.AbstractGame.Params.heldPath_affine_eq_pivot_never_enters_counterexample
#print axioms Sanctions.AbstractGame.Params.no_uniform_short_duration_counterexample

end Params
end AbstractGame

end

end Sanctions
