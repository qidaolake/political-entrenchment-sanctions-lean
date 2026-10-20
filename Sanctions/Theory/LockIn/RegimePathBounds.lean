/-
Sanctions/Theory/LockIn/RegimePathBounds.lean

**Path bounds under a realised sanction rule, general in `F`** (Rung 5, docs
53/55).

Four statements about the general-`F` natural path `rulePathF R x₀` — the
closed loop `x ↦ F(x, R x)` iterated from `x₀` — each needing only the order
structure of the transition and a lower sanction chord:

1. **Wash-out.** Under a rule that is zero on `[0,1]`, the state loses at least
   the fraction `d` of itself each period: `x_t ≤ (1 − d)^t·x₀ → 0`. The
   chord between sanctions `0` and `x` at state `x`, with the diagonal, gives
   `F(x, 0) ≤ (1 − d)·x`.
2. **Wash-in.** Under a rule that is at least `b` on `[0,1]`, the state
   dominates `b·(1 − (1 − d)^t)` and is eventually above every level below
   `b`. The comparison recursion uses the affine minorant of `F(·, b)` only
   at `y ≤ b`, where the chord gives it; no monotonicity of the rule is used.
3. **Strict dominance over the zero rule** from a common start, at every
   positive date, when the rule is positive.
4. **Convergence** under a rule that is monotone and continuous on `[0,1]`, to
   a fixed point of the closed loop, at which the sanction equals the state
   whenever the lower chord is positive.

The rule is a hypothesis here. Rule 1 is satisfied where these are consumed:
on the chord economy the rule is the equilibrium response
(`Examples/PlacableSenderRegimes`), derived, not posited.
-/
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Foundations.TransitionChords
import Sanctions.Foundations.GeometricApproach
import Sanctions.Foundations.MonotoneAttraction

namespace Sanctions

open Set Filter Topology Sanctions.TransitionChords Sanctions.GeometricApproach

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## 0. Two consequences of a lower sanction chord -/

/-- A lower sanction chord rate is at most one: at state `0`, the chord between
sanctions `0` and `1` is `F(0,1) − F(0,0) = F(0,1) ≤ 1`. -/
theorem sanctionLowerChord_le_one {d : ℝ} (hlo : SanctionLowerChord p.F d) : d ≤ 1 := by
  have h := hlo (x := 0) (s₁ := 0) (s₂ := 1) ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, zero_le_one⟩
    ⟨zero_le_one, le_rfl⟩ zero_le_one
  have h1 : p.F 0 1 ≤ 1 := (p.F_mem 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩).2
  have h0 : p.F 0 0 = 0 := p.F_diag 0
  linarith

/-- Zero sanctions erode the state by at least the chord fraction:
`F(x, 0) ≤ (1 − d)·x`. -/
theorem F_zero_le_of_lowerChord {d : ℝ} (hlo : SanctionLowerChord p.F d) {x : ℝ}
    (hx : x ∈ Sanctions.I) : p.F x 0 ≤ (1 - d) * x := by
  have h := hlo hx ⟨le_rfl, zero_le_one⟩ hx hx.1
  have hd : p.F x x = x := p.F_diag x
  linarith

/-- Sanction `b` from a state `y ≤ b` closes at least the fraction `d` of the
gap: `F(y, b) ≥ y + d·(b − y)`. -/
theorem F_ge_of_lowerChord_below {d : ℝ} (hlo : SanctionLowerChord p.F d) {y b : ℝ}
    (hy : y ∈ Sanctions.I) (hb : b ∈ Sanctions.I) (hyb : y ≤ b) :
    y + d * (b - y) ≤ p.F y b := by
  have h := hlo hy hy hb hyb
  have hd : p.F y y = y := p.F_diag y
  linarith

/-- Two rules that agree on `[0,1]` and preserve it generate the same path from
a feasible start. -/
theorem rulePathF_congr_on {R₁ R₂ : ℝ → ℝ}
    (hR₁_mem : ∀ x ∈ Sanctions.I, R₁ x ∈ Sanctions.I)
    (hR : ∀ x ∈ Sanctions.I, R₁ x = R₂ x) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, p.rulePathF R₁ x₀ t = p.rulePathF R₂ x₀ t := by
  have hmem := p.rulePathF_mem_I hR₁_mem hx₀
  intro t
  induction t with
  | zero => rfl
  | succ k ih =>
    rw [rulePathF_succ, rulePathF_succ, ← ih]
    unfold ruleStepF
    rw [hR _ (hmem k)]

/-! ## 1. Wash-out under the zero rule -/

theorem rulePathF_le_geom_of_zero_rule {d : ℝ} (hlo : SanctionLowerChord p.F d)
    {R : ℝ → ℝ} (hR : ∀ x ∈ Sanctions.I, R x = 0) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, p.rulePathF R x₀ t ≤ (1 - d) ^ t * x₀ := by
  have hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I := fun x hx => by
    rw [hR x hx]; exact ⟨le_rfl, zero_le_one⟩
  have hmem := p.rulePathF_mem_I hR_mem hx₀
  have hstep : ∀ t, p.rulePathF R x₀ (t + 1) ≤ (1 - d) * p.rulePathF R x₀ t := by
    intro t
    rw [rulePathF_succ]
    unfold ruleStepF
    rw [hR _ (hmem t)]
    exact p.F_zero_le_of_lowerChord hlo (hmem t)
  have h := le_geom_of_step (p.sanctionLowerChord_le_one hlo) hstep
  simpa using h

/-- **Wash-out.** Under the zero rule the state tends to zero. -/
theorem rulePathF_tendsto_zero_of_zero_rule {d : ℝ} (hd0 : 0 < d)
    (hlo : SanctionLowerChord p.F d)
    {R : ℝ → ℝ} (hR : ∀ x ∈ Sanctions.I, R x = 0) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    Tendsto (p.rulePathF R x₀) atTop (𝓝 0) := by
  have hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I := fun x hx => by
    rw [hR x hx]; exact ⟨le_rfl, zero_le_one⟩
  have hmem := p.rulePathF_mem_I hR_mem hx₀
  have hstep : ∀ t, p.rulePathF R x₀ (t + 1) ≤ (1 - d) * p.rulePathF R x₀ t := by
    intro t
    rw [rulePathF_succ]
    unfold ruleStepF
    rw [hR _ (hmem t)]
    exact p.F_zero_le_of_lowerChord hlo (hmem t)
  exact tendsto_zero_of_step hd0 (p.sanctionLowerChord_le_one hlo) (fun t => (hmem t).1) hstep

/-! ## 2. Wash-in under a rule bounded below -/

/-- **Wash-in.** Under a rule at least `b` on `[0,1]`, the state dominates the
geometric approach `b·(1 − (1 − d)^t)` from any feasible start. -/
theorem rulePathF_ge_approach_of_rule_ge {d : ℝ} (hd0 : 0 ≤ d)
    (hlo : SanctionLowerChord p.F d) {b : ℝ} (hb : b ∈ Sanctions.I)
    {R : ℝ → ℝ} (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hRb : ∀ x ∈ Sanctions.I, b ≤ R x) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, approach b d t ≤ p.rulePathF R x₀ t := by
  have hd1 := p.sanctionLowerChord_le_one hlo
  have hmem := p.rulePathF_mem_I hR_mem hx₀
  apply ge_of_step_ge
  · simpa using hx₀.1
  · intro t ht
    rw [rulePathF_succ, approach_succ]
    unfold ruleStepF
    set y := approach b d t with hy
    have hy_mem : y ∈ Sanctions.I :=
      ⟨approach_nonneg hb.1 hd0 hd1 t, (approach_le hb.1 hd1 t).trans hb.2⟩
    have hyb : y ≤ b := approach_le hb.1 hd1 t
    calc y + d * (b - y) ≤ p.F y b := p.F_ge_of_lowerChord_below hlo hy_mem hb hyb
      _ ≤ p.F y (R (p.rulePathF R x₀ t)) := p.F_mono_s y (hRb _ (hmem t))
      _ ≤ p.F (p.rulePathF R x₀ t) (R (p.rulePathF R x₀ t)) := p.F_mono_x _ ht

/-- **Eventual lower bound.** Under a rule at least `b`, the state is eventually
above every level below `b`. -/
theorem rulePathF_eventually_ge_of_rule_ge {d : ℝ} (hd0 : 0 < d)
    (hlo : SanctionLowerChord p.F d) {b : ℝ} (hb : b ∈ Sanctions.I)
    {R : ℝ → ℝ} (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hRb : ∀ x ∈ Sanctions.I, b ≤ R x) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, b - ε ≤ p.rulePathF R x₀ t :=
  eventually_ge_of_ge_approach hd0 (p.sanctionLowerChord_le_one hlo)
    (p.rulePathF_ge_approach_of_rule_ge hd0.le hlo hb hR_mem hRb hx₀) hε

/-! ## 3. Strict dominance over the zero rule -/

/-- **A positive rule strictly dominates the zero rule** from a common feasible
start, at every positive date. No monotonicity of the rule is used: the
step compares `F(x, R x) ≥ F(x, 0) ≥ F(x', 0)` and the lower chord makes the
first inequality strict. -/
theorem rulePathF_gt_zero_rule_of_pos {d : ℝ} (hd0 : 0 < d)
    (hlo : SanctionLowerChord p.F d)
    {R : ℝ → ℝ} (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hRpos : ∀ x ∈ Sanctions.I, 0 < R x) {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∀ t, p.rulePathF (fun _ => 0) x₀ t ≤ p.rulePathF R x₀ t
      ∧ (1 ≤ t → p.rulePathF (fun _ => 0) x₀ t < p.rulePathF R x₀ t) := by
  have hmem := p.rulePathF_mem_I hR_mem hx₀
  have hmem0 := p.rulePathF_mem_I (R := fun _ => 0)
    (fun _ _ => ⟨le_rfl, zero_le_one⟩) hx₀
  intro t
  induction t with
  | zero => exact ⟨le_rfl, fun h => absurd h (by norm_num)⟩
  | succ k ih =>
    obtain ⟨hle, _⟩ := ih
    rw [rulePathF_succ, rulePathF_succ]
    unfold ruleStepF
    set xR := p.rulePathF R x₀ k
    set x0 := p.rulePathF (fun _ => 0) x₀ k
    have hstrict : p.F xR 0 < p.F xR (R xR) := by
      have h := hlo (hmem k) ⟨le_rfl, zero_le_one⟩ (hR_mem _ (hmem k)) (hRpos _ (hmem k)).le
      have : 0 < d * (R xR - 0) := mul_pos hd0 (by linarith [hRpos _ (hmem k)])
      linarith
    have hmono : p.F x0 0 ≤ p.F xR 0 := p.F_mono_x 0 hle
    exact ⟨hmono.trans hstrict.le, fun _ => lt_of_le_of_lt hmono hstrict⟩

/-! ## 4. Convergence under a monotone continuous rule -/

/-- **Convergence of the closed loop.** Under a rule monotone and continuous on
`[0,1]`, every feasible start converges to a fixed point of `x ↦ F(x, R x)`. -/
theorem rulePathF_tendsto_fixedPoint_of_monotoneOn
    {R : ℝ → ℝ} (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR_mono : MonotoneOn R Sanctions.I) (hR_cont : ContinuousOn R Sanctions.I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ z ∈ Sanctions.I, p.F z (R z) = z ∧ Tendsto (p.rulePathF R x₀) atTop (𝓝 z) := by
  set G : ℝ → ℝ := fun x => p.F x (R x) with hG
  have hG_mono : MonotoneOn G (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    calc G x = p.F x (R x) := rfl
      _ ≤ p.F y (R x) := p.F_mono_x _ hxy
      _ ≤ p.F y (R y) := p.F_mono_s _ (hR_mono hx hy hxy)
  have hG_cont : ContinuousOn G (Icc (0 : ℝ) 1) := by
    have h : ContinuousOn (fun x : ℝ => (x, R x)) (Icc (0 : ℝ) 1) :=
      continuousOn_id.prodMk hR_cont
    exact p.F_continuous.comp_continuousOn h
  have hG_maps : ∀ x ∈ Icc (0 : ℝ) 1, G x ∈ Icc (0 : ℝ) 1 :=
    fun x hx => p.F_mem _ _ hx (hR_mem x hx)
  obtain ⟨z, hz, hfix, htend⟩ :=
    Sanctions.MonotoneAttraction.monotoneOn_orbit_converges zero_le_one hG_mono hG_cont
      hG_maps hx₀
  refine ⟨z, hz, hfix, ?_⟩
  have heq : p.rulePathF R x₀ = fun n => G^[n] x₀ := by
    funext n; rfl
  rw [heq]
  exact htend

/-- **At a fixed point of the closed loop the sanction equals the state**, when
the lower sanction chord is positive: `F(x, s) = x` forces `s = x`. -/
theorem rule_eq_self_of_closedLoop_fixed {d : ℝ} (hd0 : 0 < d)
    (hlo : SanctionLowerChord p.F d) {R : ℝ → ℝ} {x : ℝ} (hx : x ∈ Sanctions.I)
    (hR : R x ∈ Sanctions.I) (hfix : p.F x (R x) = x) : R x = x := by
  have hd : p.F x x = x := p.F_diag x
  rcases le_total (R x) x with h | h
  · have hc := hlo hx hR hx h
    rw [hd, hfix] at hc
    have : d * (x - R x) ≤ 0 := by linarith
    have : x - R x ≤ 0 := by
      by_contra hcon
      have hcon := lt_of_not_ge hcon
      have := mul_pos hd0 hcon; linarith
    linarith
  · have hc := hlo hx hx hR h
    rw [hd, hfix] at hc
    have : R x - x ≤ 0 := by
      by_contra hcon
      have hcon := lt_of_not_ge hcon
      have := mul_pos hd0 hcon; linarith
    linarith

end Params
end AbstractGame

end

end Sanctions
