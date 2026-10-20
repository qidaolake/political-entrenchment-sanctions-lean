/-
Sanctions/Examples/AffineInstance/Kinematics.lean

**The affine transition as a worked instance: trajectory kinematics.**

Nothing here is new mathematics. Every declaration in this file was proved in
`Sanctions/Theory/` and moved out on 2026-08-20d, once the general-`F` route
had absorbed the content that used to need it. They are kept, not deleted,
because each is still worth *exhibiting*: the affine law is an admissible
instance of the transition (Rule 22 --- "affine is an instance, not the
model"), and these are the facts that instance buys.

Three kinds of thing live here.

* **Affine to general-`F` bridges.** `dynamicTopLockInStep`,
  `dynamicTopLockInPath`, `dynamicTopLockInSanctions`, `shockStep` and
  `shockPath` hard-code the affine law `(1-d)*x + d*s` and do **not** route
  through `p.F`. Under `hF : p.F = affineF p.d` each coincides with its
  general-`F` sibling, and these equalities are what let a result stated over
  one family be re-pointed at the other. A bridge is the one place an affine
  hypothesis genuinely belongs in a signature.
* **What the affine law makes sharp.** The one-step drift is exactly `d` times
  the escalation gap; the minimum full-sanction drift has the closed form
  `d*(1-xbar)`; the corner condition collapses to `xbar <= sbar`. The general
  transition gives inequalities where affineness gives identities, and these
  record the difference.
* **Numerically pinned comparative statics.** The quarter-versus-half
  adjustment-rate comparison exhibits the economic orientation of the abstract
  comparison at two concrete rates. Per Rule 9 it certifies existence and
  refutes universals --- nothing more.

**Why this is in `Examples/` and not `Theory/`.** Every declaration below
carries `hF` or a numeral, so under Rule 22 each is affine-restricted by
construction. Keeping them in `Theory/` made the theory layer look more affine
than it is: a reverse-dependency walk over the citation graph showed the affine
material fanning out through the certificate routes, when in fact none of it
was load-bearing for any general result. It is separated here so that
`Theory/` reads as what it is --- general in `F` --- while the instance stays
available to be raised as an example.

No general-`F` theorem depends on anything in this file; that was the
precondition for the move, checked declaration by declaration before it.
-/

import Sanctions.Theory.Basin.WeakFloorBasin
import Sanctions.Theory.LockIn.LockIn
import Sanctions.Theory.LockIn.EscalationGap
import Sanctions.Theory.LockIn.LockInComparativeStatics

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- For the **affine** transition the corner condition is *exactly*
"the floor clears the pivot": `xbar ≤ (1-δ)·xbar + δ·sbar ↔ xbar ≤ sbar`. -/
theorem affine_corner_iff {δ xbar sbar : ℝ} (hδ : 0 < δ) :
    xbar ≤ AbstractGame.affineF δ xbar sbar ↔ xbar ≤ sbar := by
  simp only [AbstractGame.affineF]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ## Part 7 — the affine path family

`dynamicTopLockInStep` / `dynamicTopLockInPath`
(`DynamicTopLockIn.lean:70,75`) hard-code the affine law
`(1-δ)·x + δ·rule` and do **not** route through `p.F`, so the general-`F`
results above do not cover them. Under `hF : p.F = affineF p.δ` the two
families coincide; without `hF`, the affine invariance is proved directly
from `xbar ≤ sbar`. -/

/-- Under `hF : p.F = affineF p.δ` the affine and general-`F` one-step
maps coincide. -/
theorem dynamicTopLockInStep_eq_stepF_of_affine
    (hF : p.F = AbstractGame.affineF p.δ)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x : ℝ) :
    p.dynamicTopLockInStep V_S α x = p.dynamicTopLockInStepF V_S α x := by
  unfold dynamicTopLockInStep dynamicTopLockInStepF
  rw [hF]
  simp only [AbstractGame.affineF]

/-- Under `hF : p.F = affineF p.δ` the affine and general-`F` state paths
coincide. -/
theorem dynamicTopLockInPath_eq_pathF_of_affine
    (hF : p.F = AbstractGame.affineF p.δ)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.dynamicTopLockInPath V_S α x₀ n = p.dynamicTopLockInPathF V_S α x₀ n := by
  have hstep : (fun x => p.dynamicTopLockInStep V_S α x)
      = (fun x => p.dynamicTopLockInStepF V_S α x) :=
    funext (fun x => p.dynamicTopLockInStep_eq_stepF_of_affine hF V_S α x)
  unfold dynamicTopLockInPath dynamicTopLockInPathF
  rw [hstep]

/-- **Affine → general bridge.** Under `hF : p.F = affineF p.δ` the affine
and general-`F` realized sanction sequences coincide at every horizon. The
selector `dynamicTopRealizedRule` is already general in `F`, so the whole
content is that the two state paths agree. -/
theorem dynamicTopLockInSanctions_eq_sanctionsF_of_affine
    (hF : p.F = AbstractGame.affineF p.δ)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) (n : ℕ) :
    p.dynamicTopLockInSanctions V_S α x₀ n
      = p.dynamicTopLockInSanctionsF V_S α x₀ n := by
  unfold dynamicTopLockInSanctions dynamicTopLockInSanctionsF
  rw [p.dynamicTopLockInPath_eq_pathF_of_affine hF V_S α x₀ n]

/-- The sanctions bridge in **function form**. Re-pointing a `Monotone
(p.dynamicTopLockInSanctions V_S α x₀)` conclusion needs an equality of
*functions*; the pointwise lemma above will not rewrite under `Monotone`. -/
theorem dynamicTopLockInSanctions_eq_sanctionsF_funext_of_affine
    (hF : p.F = AbstractGame.affineF p.δ)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (x₀ : ℝ) :
    p.dynamicTopLockInSanctions V_S α x₀
      = p.dynamicTopLockInSanctionsF V_S α x₀ :=
  funext (fun n => p.dynamicTopLockInSanctions_eq_sanctionsF_of_affine hF V_S α x₀ n)

/-- **Weak-floor affine invariance, proved directly** (no `hF` needed):
`xbar ≤ sbar` plus the weak floor keeps `[xbar, 1]` invariant under the
hard-coded affine step. -/
theorem weakFloor_dynamicTopStep_mem_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hPivot : xbar ≤ sbar)
    (hWeak : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x : ℝ} (hx : x ∈ Set.Icc xbar 1) :
    p.dynamicTopLockInStep V_S α x ∈ Set.Icc xbar 1 := by
  refine ⟨?_, p.dynamicTopLockInStep_le_one V_S α hx⟩
  have hδ0 : 0 < p.δ := p.δ_mem.1
  have hδ1 : p.δ < 1 := p.δ_mem.2
  have hs : sbar ≤ p.dynamicTopRealizedRule V_S α x := hWeak x hx
  unfold dynamicTopLockInStep
  nlinarith [hx.1]

theorem weakFloor_dynamicTopPath_mem_basin
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {xbar sbar : ℝ}
    (hPivot : xbar ≤ sbar)
    (hWeak : ∀ x ∈ Set.Icc xbar (1 : ℝ),
                sbar ≤ p.dynamicTopRealizedRule V_S α x)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    ∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc xbar 1 := by
  intro n
  induction n with
  | zero => simpa using hx₀
  | succ n ih =>
    simp only [dynamicTopLockInPath_succ]
    exact p.weakFloor_dynamicTopStep_mem_basin V_S α hPivot hWeak ih

/-- Structure-level affine invariance: from `WeakFloorBasinTop` plus
`xbar ≤ sbar`. For an affine transition `corner_holds` and `xbar ≤ sbar`
are equivalent (`affine_corner_iff`), so this costs nothing there. -/
theorem WeakFloorBasinTop.path_mem_basin_affine
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar)
    (hPivot : xbar ≤ sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1) :
    (∀ n, p.dynamicTopLockInPath V_S α x₀ n ∈ Set.Icc xbar 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n) ∧
    (∀ n, xbar ≤ p.dynamicTopLockInSanctions V_S α x₀ n) := by
  have hWeak := WeakFloorBasinTop.level_dyn_top_weak p hB
  have hpath := p.weakFloor_dynamicTopPath_mem_basin V_S α hPivot hWeak hx₀
  refine ⟨hpath, ?_, ?_⟩
  · intro n; exact hWeak _ (hpath n)
  · intro n; exact le_trans hPivot (hWeak _ (hpath n))

/-- **Weak-floor affine Goal 3.** The exogenous shock-entry step
(`shockPath_eventually_in_basin`) is floor-independent, so the affine
post-shock basin conjunct survives the weakening. -/
theorem weakFloorBasinTop_affine_temporary_shock_permanent_floor
    {V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ}
    {α : ℝ → ℝ} {xbar sbar x₀ : ℝ}
    (hB : p.WeakFloorBasinTop V_T V_S α xbar sbar)
    (hPivot : xbar ≤ sbar)
    (hxbar_lt_one : xbar < 1)
    (hsbar_pos : 0 < sbar)
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath V_S α (p.shockPath x₀ N) n
              ∈ Set.Icc xbar 1) ∧
      (∀ n, sbar ≤ p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions V_S α (p.shockPath x₀ N) n) := by
  obtain ⟨N, hN⟩ := p.shockPath_eventually_in_basin hx₀_nn hx₀_le hxbar_lt_one
  have h_N_in : p.shockPath x₀ N ∈ Set.Icc xbar 1 := hN N (le_refl _)
  obtain ⟨hpath, hfloor, _⟩ :=
    WeakFloorBasinTop.path_mem_basin_affine p hB hPivot h_N_in
  exact ⟨N, hpath, hfloor, fun n => lt_of_lt_of_le hsbar_pos (hfloor n)⟩


/-! ### Affine → general-`F` bridges for the shock phase

`shockStep` and `shockPath` are axis-2 affine (Rule 22): they hard-code
`x' = (1 − δ)·x + δ·1` instead of routing through `p.F`. These two lemmas
are the equalities that let a result stated over the affine shock objects
be re-pointed at the general-`F` siblings whenever the economy happens to
satisfy `hF : p.F = affineF p.δ`. They are the shock-phase analogues of
`dynamicTopLockInStep_eq_stepF_of_affine` / `dynamicTopLockInPath_eq_pathF_of_affine`
earlier in this file.

Both carry `hF` and are therefore affine-restricted **by design** — a
bridge is the one place the affine law belongs in a signature. -/

/-- **Affine → general bridge.** Under `hF : p.F = affineF p.δ` the
hard-coded affine shock step and the general-`F` shock step `p.F x 1`
coincide. -/
theorem shockStep_eq_shockStepF_of_affine
    (hF : p.F = AbstractGame.affineF p.δ) (x : ℝ) :
    p.shockStep x = p.shockStepF x := by
  unfold shockStep shockStepF
  rw [hF]
  simp only [AbstractGame.affineF]

/-- **Affine → general bridge.** Under `hF : p.F = affineF p.δ` the affine
and general-`F` shock state paths coincide at every horizon. -/
theorem shockPath_eq_shockPathF_of_affine
    (hF : p.F = AbstractGame.affineF p.δ) (x₀ : ℝ) (n : ℕ) :
    p.shockPath x₀ n = p.shockPathF x₀ n := by
  have hstep : (fun x => p.shockStep x) = (fun x => p.shockStepF x) :=
    funext (fun x => p.shockStep_eq_shockStepF_of_affine hF x)
  unfold shockPath shockPathF
  rw [hstep]

/-- The same bridge in **function form**. A pointwise equality is not
enough for a conclusion that quantifies over the path itself — `Monotone
(p.shockPath x₀)` is a statement *about the function*, so re-pointing it
needs this `funext` version, not `shockPath_eq_shockPathF_of_affine`. -/
theorem shockPath_eq_shockPathF_funext_of_affine
    (hF : p.F = AbstractGame.affineF p.δ) (x₀ : ℝ) :
    p.shockPath x₀ = p.shockPathF x₀ :=
  funext (fun n => p.shockPath_eq_shockPathF_of_affine hF x₀ n)

/-! ## Part 2 — the affine transition: drift is `δ` times the escalation gap -/

/-- Under the affine transition the one-step drift is exactly `δ` times the
amount by which the realised sanction exceeds the current state. -/
theorem dynamicTopLockInStepF_sub_self_of_affine
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ)
    (hF : p.F = AbstractGame.affineF p.δ) (x : ℝ) :
    p.dynamicTopLockInStepF V_S α x - x
      = p.δ * (p.dynamicTopRealizedRule V_S α x - x) := by
  unfold dynamicTopLockInStepF
  rw [hF]
  unfold AbstractGame.affineF
  ring

/-- **The escalation gap cannot be uniformly positive** (affine transition).
If the realised sanction exceeds the state by at least `ε > 0` everywhere on a
forward-invariant `[a,b)`, that is contradictory. -/
theorem dynamicTopLockInPathF_escape_of_uniform_gap_affine
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) {a b ε x₀ : ℝ}
    (hF : p.F = AbstractGame.affineF p.δ) (hε : 0 < ε)
    (hgap : ∀ x ∈ Set.Ico a b, x + ε ≤ p.dynamicTopRealizedRule V_S α x)
    (hinv : ∀ x ∈ Set.Ico a b, p.dynamicTopLockInStepF V_S α x ∈ Set.Ico a b)
    (hx₀ : x₀ ∈ Set.Ico a b) : False := by
  refine p.dynamicTopLockInPathF_escape_of_uniform_drift V_S α
    (η := p.δ * ε) (mul_pos p.δ_mem.1 hε) (fun x hx => ?_) hinv hx₀
  have hid := p.dynamicTopLockInStepF_sub_self_of_affine V_S α hF x
  have hg := hgap x hx
  nlinarith [p.δ_mem.1]

end Params

/-- **Closed form of the affine minimum-drift bound.** Under the
affine transition, full-sanction drift is `δ * (1 - x)`, so its
minimum on `[0, xbar]` is attained at `xbar` and equals
`δ * (1 - xbar)`. Consequently

`⌈xbar / (δ * (1 - xbar))⌉₊`

is a valid uniform shock-entry duration. This is the affine
specialization of the general minimum-drift bound, not the sharper
logarithmic duration obtained from the exact affine trajectory. -/
theorem affine_fullShockDrift_minimum_closed_form
    (p : Sanctions.AbstractGame.Params)
    {δ xbar : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hF : p.F = Sanctions.AbstractGame.affineF δ)
    (hxbar : xbar ∈ Set.Ico (0 : ℝ) 1) :
    0 < δ * (1 - xbar) ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) xbar,
        δ * (1 - xbar) = p.fullShockDrift xmin) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar,
        δ * (1 - xbar) ≤ p.fullShockDrift x) ∧
      ∀ x₀ ∈ Set.Icc (0 : ℝ) 1,
        ∀ n ≥ Nat.ceil (xbar / (δ * (1 - xbar))),
          p.shockPathF x₀ n ∈ Set.Icc xbar 1 := by
  have hη_pos : 0 < δ * (1 - xbar) :=
    mul_pos hδ.1 (sub_pos.mpr hxbar.2)
  have hη_attains : ∃ xmin ∈ Set.Icc (0 : ℝ) xbar,
      δ * (1 - xbar) = p.fullShockDrift xmin := by
    refine ⟨xbar, ⟨hxbar.1, le_rfl⟩, ?_⟩
    unfold Params.fullShockDrift
    rw [hF]
    unfold affineF
    ring
  have hη_min : ∀ x ∈ Set.Icc (0 : ℝ) xbar,
      δ * (1 - xbar) ≤ p.fullShockDrift x := by
    intro x hx
    unfold Params.fullShockDrift
    rw [hF]
    unfold affineF
    nlinarith [mul_nonneg hδ.1.le (sub_nonneg.mpr hx.2)]
  exact ⟨hη_pos, hη_attains, hη_min,
    p.shockPathF_uniform_natCeil_entry_of_drift hη_pos hη_min⟩

/-- **The canonical general-`F` drift reduces to the familiar affine
formula.** If `F(x,s) = (1-δ)x + δs`, then
`fullShockMinDrift xbar = δ(1-xbar)`. -/
theorem affine_fullShockMinDrift_eq
    (p : Sanctions.AbstractGame.Params)
    {δ xbar : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hF : p.F = Sanctions.AbstractGame.affineF δ)
    (hxbar : xbar ∈ Set.Ico (0 : ℝ) 1) :
    p.fullShockMinDrift xbar = δ * (1 - xbar) := by
  obtain ⟨_, ⟨xmin, hxmin, hmin_eq⟩, hmin⟩ :=
    p.fullShockMinDrift_pos_attains_isMinOn
      (strictAdjustment_of_F_eq_affineF p hδ hF) hxbar
  obtain ⟨_, _, haff_min, _⟩ :=
    affine_fullShockDrift_minimum_closed_form p hδ hF hxbar
  have hxbar_drift : p.fullShockDrift xbar = δ * (1 - xbar) := by
    unfold Params.fullShockDrift
    rw [hF]
    unfold affineF
    ring
  apply le_antisymm
  · exact (hmin xbar ⟨hxbar.1, le_rfl⟩).trans_eq hxbar_drift
  · exact (haff_min xmin hxmin).trans_eq hmin_eq.symm

/-- **The affine ceiling formula is exactly the specialization of the
canonical general-`F` horizon.** It is therefore an appendix benchmark,
not a separate transition assumption. -/
theorem affine_fullShockEntryHorizon_eq
    (p : Sanctions.AbstractGame.Params)
    {δ xbar : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hF : p.F = Sanctions.AbstractGame.affineF δ)
    (hxbar : xbar ∈ Set.Ico (0 : ℝ) 1) :
    p.fullShockEntryHorizon xbar =
      Nat.ceil (xbar / (δ * (1 - xbar))) := by
  unfold Params.fullShockEntryHorizon
  rw [affine_fullShockMinDrift_eq p hδ hF hxbar]

/-- **Affine adjustment-speed comparative static.** For affine
transitions, a larger adjustment rate raises the full-sanction
transition at every pre-basin state. Thus `δ₁ ≤ δ₂` raises the
minimum drift and weakly lowers its ceiling shock bound.

Affine-restricted (Rule 22). Since BG2.4 (2026-10-06) the general theorem
needs pre-basin ascent of the slower law only, so the range condition on the
faster rate, `δ₂ ∈ (0,1)`, was dropped: the dominance `δ₁ ≤ δ₂` alone passes
the slower law's positive drift on to the faster law. -/
theorem affine_fullShockDrift_minima_horizon_mono_of_delta_le
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    {δ₁ δ₂ xbar : ℝ}
    (hδ₁ : δ₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ_le : δ₁ ≤ δ₂)
    (hF₁ : p₁.F = Sanctions.AbstractGame.affineF δ₁)
    (hF₂ : p₂.F = Sanctions.AbstractGame.affineF δ₂)
    (hxbar : xbar ∈ Set.Ico (0 : ℝ) 1) :
    ∃ η₁ η₂ : ℝ,
      0 < η₁ ∧ 0 < η₂ ∧
      (∃ xmin₁ ∈ Set.Icc (0 : ℝ) xbar,
        η₁ = p₁.fullShockDrift xmin₁) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar,
        η₁ ≤ p₁.fullShockDrift x) ∧
      (∃ xmin₂ ∈ Set.Icc (0 : ℝ) xbar,
        η₂ = p₂.fullShockDrift xmin₂) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar,
        η₂ ≤ p₂.fullShockDrift x) ∧
      η₁ ≤ η₂ ∧
      Nat.ceil (xbar / η₂) ≤ Nat.ceil (xbar / η₁) := by
  -- Since BG2.4 the general theorem asks only pre-basin ascent of `p₁`,
  -- which the affine law's strict adjustment supplies.
  apply fullShockDrift_minima_horizon_mono_of_top_transition_le p₁ p₂ hxbar.1
    (p₁.preBasinAscent_of_strictAdjustment
      (strictAdjustment_of_F_eq_affineF p₁ hδ₁ hF₁) hxbar.2)
  intro x hx
  rw [hF₁, hF₂]
  unfold affineF
  have hx_one : 0 ≤ 1 - x := by linarith [hx.2, hxbar.2]
  nlinarith [mul_le_mul_of_nonneg_right hδ_le hx_one]

/-- **Directional witness for the adjustment-speed comparison.**
At the distinct affine rates `δ₁ = 1/4` and `δ₂ = 1/2`, the minimum
full-sanction drift is strictly larger at `1/2`, while the quantitative
integer shock bound is weakly smaller. This pins the economic
orientation of the abstract comparison. -/
theorem affine_quarter_half_fullShockDrift_minima_horizon_strict
    (p₁ p₂ : Sanctions.AbstractGame.Params)
    (hF₁ : p₁.F = Sanctions.AbstractGame.affineF (1 / 4 : ℝ))
    (hF₂ : p₂.F = Sanctions.AbstractGame.affineF (1 / 2 : ℝ))
    {xbar : ℝ} (hxbar : xbar ∈ Set.Ico (0 : ℝ) 1) :
    ∃ η₁ η₂ : ℝ,
      0 < η₁ ∧ 0 < η₂ ∧
      (∃ xmin₁ ∈ Set.Icc (0 : ℝ) xbar,
        η₁ = p₁.fullShockDrift xmin₁) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar,
        η₁ ≤ p₁.fullShockDrift x) ∧
      (∃ xmin₂ ∈ Set.Icc (0 : ℝ) xbar,
        η₂ = p₂.fullShockDrift xmin₂) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar,
        η₂ ≤ p₂.fullShockDrift x) ∧
      η₁ < η₂ ∧
      Nat.ceil (xbar / η₂) ≤ Nat.ceil (xbar / η₁) := by
  apply fullShockDrift_minima_horizon_strict_of_top_transition_lt p₁ p₂ hxbar.1
    (p₁.preBasinAscent_of_strictAdjustment
      (strictAdjustment_of_F_eq_affineF p₁ (by norm_num) hF₁) hxbar.2)
  intro x hx
  rw [hF₁, hF₂]
  unfold affineF
  nlinarith [hx.2, hxbar.2]

/-! ## Axiom hygiene (Rule 10) -/

#print axioms Sanctions.AbstractGame.Params.affine_corner_iff
#print axioms Sanctions.AbstractGame.Params.dynamicTopLockInPath_eq_pathF_of_affine
#print axioms Sanctions.AbstractGame.Params.dynamicTopLockInSanctions_eq_sanctionsF_funext_of_affine
#print axioms Sanctions.AbstractGame.Params.weakFloorBasinTop_affine_temporary_shock_permanent_floor
#print axioms Sanctions.AbstractGame.Params.shockPath_eq_shockPathF_funext_of_affine
#print axioms Sanctions.AbstractGame.Params.dynamicTopLockInStepF_sub_self_of_affine
#print axioms Sanctions.AbstractGame.Params.dynamicTopLockInPathF_escape_of_uniform_gap_affine
#print axioms Sanctions.AbstractGame.affine_fullShockEntryHorizon_eq
#print axioms Sanctions.AbstractGame.affine_quarter_half_fullShockDrift_minima_horizon_strict

end AbstractGame

end

end Sanctions
