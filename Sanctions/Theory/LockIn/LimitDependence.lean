/-
Sanctions/Theory/LockIn/LimitDependence.lean

**Dependence on initial conditions forces a strictly positive limiting sanction
from at least one start** (round AJ, 2026-09-22; doc 98 B5, on the user's word).

The manuscript keeps two notions apart: *persistence* (a positive sanction that
does not wash out) and *dependence on initial conditions* (two starts with
different long-run states). The introduction says they are distinct
possibilities; this file proves that they are **ordered**. Under zero-sanction
descent — a zero sanction erodes any positive entrenchment, `0 < x ⇒ F(x,0) < x`
on `[0,1]` (the binder `hD0`; it is the erosion half of
`Params.StrictAdjustment` read at `s = 0` only, and since BG2.2 (2026-10-06) it
replaces the two-sided condition) — any realised rule `R`, continuous on the
state interval, whose natural paths
from two feasible starts converge to *different* limits has a strictly
positive limiting sanction from at least one of them
(`exists_pos_limit_sanction_of_limit_dependence`). The reason is short: a
limit `L` of the path is a fixed point of the step `x ↦ F(x, R(x))`; if the
limiting sanction `R(L)` were zero then `F(L, 0) = L`, which erosion forbids
unless `L = 0`; two distinct limits cannot both be zero.

The converse fails: at the affine member of the placable family the defiance
equilibrium's closed loop has one globally attracting steady state with a
positive sanction, so every start converges to the same state
(`placableAffine_unique_attracting_state` in
`Examples/PlacableSenderWitnesses.lean`; the affine threshold family that
carried `persistence_without_limit_dependence` was retired in round AS). So dependence on initial
conditions is the stronger of the two notions.

Zero-sanction descent cannot be weakened at any single state:
`limit_dependence_sharp_of_zero_sanction_fixed` shows both conclusions fail for
the zero rule as soon as `F(L,0) = L` at some `L ∈ (0,1]`. The two-sided
versions survive as `_of_strictAdjustment` corollaries.

Rule 22: general in the transition; only zero-sanction descent and continuity
are read. Rule 1: the rule is arbitrary here — the statement is
about the closed loop of whatever rule an equilibrium realises, and it is
consumed at equilibrium rules downstream.
-/
import Sanctions.Theory.LockIn.DifferentPolicyComparator

namespace Sanctions
namespace AbstractGame
namespace Params

open Set Filter Topology

variable (p : Params)

/-- The natural step `x ↦ F(x, R(x))` is continuous on the state interval when
the rule is. -/
theorem ruleStepF_continuousOn {R : ℝ → ℝ} (hR : ContinuousOn R Sanctions.I) :
    ContinuousOn (p.ruleStepF R) Sanctions.I := by
  have h : ContinuousOn (fun x : ℝ => (x, R x)) Sanctions.I := continuousOn_id.prodMk hR
  exact p.F_continuous.comp_continuousOn h

/-- The limit of a feasible natural path is feasible. -/
theorem rulePathF_limit_mem {R : ℝ → ℝ} (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    {x₀ L : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    (hL : Tendsto (p.rulePathF R x₀) atTop (𝓝 L)) : L ∈ Sanctions.I :=
  isClosed_Icc.mem_of_tendsto hL (Eventually.of_forall (p.rulePathF_mem_I hR_mem hx₀))

/-- **The limit of a natural path is a fixed point of the step**: `F(L, R(L)) = L`. -/
theorem rulePathF_limit_isFixed {R : ℝ → ℝ} (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR : ContinuousOn R Sanctions.I) {x₀ L : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    (hL : Tendsto (p.rulePathF R x₀) atTop (𝓝 L)) : p.F L (R L) = L := by
  have hLmem := p.rulePathF_limit_mem hR_mem hx₀ hL
  have hmem := p.rulePathF_mem_I hR_mem hx₀
  have hwithin : Tendsto (p.rulePathF R x₀) atTop (𝓝[Sanctions.I] L) :=
    tendsto_nhdsWithin_iff.mpr ⟨hL, Eventually.of_forall hmem⟩
  have hstep : Tendsto (fun n => p.ruleStepF R (p.rulePathF R x₀ n)) atTop
      (𝓝 (p.ruleStepF R L)) :=
    ((p.ruleStepF_continuousOn hR L hLmem).tendsto).comp hwithin
  have hshift : Tendsto (fun n => p.ruleStepF R (p.rulePathF R x₀ n)) atTop (𝓝 L) := by
    have := hL.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp [Function.comp, rulePathF_succ]
  exact tendsto_nhds_unique hstep hshift

/-- The limiting sanction along a convergent natural path is `R(L)`. -/
theorem ruleSanctionsF_tendsto {R : ℝ → ℝ} (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR : ContinuousOn R Sanctions.I) {x₀ L : ℝ} (hx₀ : x₀ ∈ Sanctions.I)
    (hL : Tendsto (p.rulePathF R x₀) atTop (𝓝 L)) :
    Tendsto (p.ruleSanctionsF R x₀) atTop (𝓝 (R L)) := by
  have hLmem := p.rulePathF_limit_mem hR_mem hx₀ hL
  have hwithin : Tendsto (p.rulePathF R x₀) atTop (𝓝[Sanctions.I] L) :=
    tendsto_nhdsWithin_iff.mpr ⟨hL, Eventually.of_forall (p.rulePathF_mem_I hR_mem hx₀)⟩
  exact ((hR L hLmem).tendsto).comp hwithin

/-- **A zero limiting sanction forces the limit state to zero**, under
zero-sanction descent. If a continuous feasible rule's natural path converges
to `L` and the rule levies nothing at `L`, then `L` is a rest point of the
zero-sanction transition, `F(L,0) = L`, which descent forbids unless `L = 0`.

General in `F`. Since BG2.2 (2026-10-06) the hypothesis is `hD0` (a zero
sanction strictly lowers every positive feasible state) in place of the
two-sided `StrictAdjustment`: the proof reads that condition once, at
`s = 0`. The old form is
`limit_eq_zero_of_limit_sanction_zero_of_strictAdjustment`. -/
theorem limit_eq_zero_of_limit_sanction_zero
    (hD0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < x → p.F x 0 < x) {R : ℝ → ℝ}
    (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I) (hR : ContinuousOn R Sanctions.I)
    {x₀ L : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (hL : Tendsto (p.rulePathF R x₀) atTop (𝓝 L))
    (h0 : R L = 0) : L = 0 := by
  have hLmem := p.rulePathF_limit_mem hR_mem hx₀ hL
  have hfix := p.rulePathF_limit_isFixed hR_mem hR hx₀ hL
  rw [h0] at hfix
  by_contra hne
  have hpos : 0 < L := lt_of_le_of_ne hLmem.1 (Ne.symm hne)
  have := hD0 L hLmem hpos
  linarith

/-- The two-sided form of `limit_eq_zero_of_limit_sanction_zero`: strict
adjustment (F5) supplies zero-sanction descent through its erosion half
(`StrictAdjustment.F_zero_lt_self`). General in `F`; kept for callers that hold
F5 (BG2.2). -/
theorem limit_eq_zero_of_limit_sanction_zero_of_strictAdjustment
    (hstrict : p.StrictAdjustment) {R : ℝ → ℝ}
    (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I) (hR : ContinuousOn R Sanctions.I)
    {x₀ L : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (hL : Tendsto (p.rulePathF R x₀) atTop (𝓝 L))
    (h0 : R L = 0) : L = 0 :=
  p.limit_eq_zero_of_limit_sanction_zero
    (fun _ hx hx0 => hstrict.F_zero_lt_self hx hx0) hR_mem hR hx₀ hL h0

/-- **Dependence on initial conditions implies a strictly positive limiting
sanction from at least one start.** If the natural paths of a continuous
feasible rule from two feasible starts converge to different limits, then from
one of the two starts the limiting sanction is strictly positive.

General in `F`. Since BG2.2 (2026-10-06) the transition hypothesis is only
zero-sanction descent `hD0`, not the two-sided `StrictAdjustment`; the old form
is `exists_pos_limit_sanction_of_limit_dependence_of_strictAdjustment`, and
`limit_dependence_sharp_of_zero_sanction_fixed` shows `hD0` cannot be relaxed
at any positive state. -/
theorem exists_pos_limit_sanction_of_limit_dependence
    (hD0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < x → p.F x 0 < x)
    {R : ℝ → ℝ} (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR : ContinuousOn R Sanctions.I) {x₁ x₂ L₁ L₂ : ℝ}
    (hx₁ : x₁ ∈ Sanctions.I) (hx₂ : x₂ ∈ Sanctions.I)
    (h₁ : Tendsto (p.rulePathF R x₁) atTop (𝓝 L₁))
    (h₂ : Tendsto (p.rulePathF R x₂) atTop (𝓝 L₂)) (hne : L₁ ≠ L₂) :
    (0 < R L₁ ∧ Tendsto (p.ruleSanctionsF R x₁) atTop (𝓝 (R L₁))) ∨
    (0 < R L₂ ∧ Tendsto (p.ruleSanctionsF R x₂) atTop (𝓝 (R L₂))) := by
  have hL₁ := p.rulePathF_limit_mem hR_mem hx₁ h₁
  have hL₂ := p.rulePathF_limit_mem hR_mem hx₂ h₂
  have hR₁ := (hR_mem L₁ hL₁).1
  have hR₂ := (hR_mem L₂ hL₂).1
  by_cases hz : R L₁ = 0
  · have hz₁ := p.limit_eq_zero_of_limit_sanction_zero hD0 hR_mem hR hx₁ h₁ hz
    right
    refine ⟨?_, p.ruleSanctionsF_tendsto hR_mem hR hx₂ h₂⟩
    rcases eq_or_lt_of_le hR₂ with h | h
    · have hz₂ := p.limit_eq_zero_of_limit_sanction_zero hD0 hR_mem hR hx₂ h₂ h.symm
      exact absurd (hz₁.trans hz₂.symm) hne
    · exact h
  · left
    exact ⟨lt_of_le_of_ne hR₁ (Ne.symm hz), p.ruleSanctionsF_tendsto hR_mem hR hx₁ h₁⟩

/-- The two-sided form of `exists_pos_limit_sanction_of_limit_dependence`:
strict adjustment (F5) supplies zero-sanction descent through its erosion half.
General in `F`; kept for callers that hold F5 (BG2.2). -/
theorem exists_pos_limit_sanction_of_limit_dependence_of_strictAdjustment
    (hstrict : p.StrictAdjustment)
    {R : ℝ → ℝ} (hR_mem : ∀ x ∈ Sanctions.I, R x ∈ Sanctions.I)
    (hR : ContinuousOn R Sanctions.I) {x₁ x₂ L₁ L₂ : ℝ}
    (hx₁ : x₁ ∈ Sanctions.I) (hx₂ : x₂ ∈ Sanctions.I)
    (h₁ : Tendsto (p.rulePathF R x₁) atTop (𝓝 L₁))
    (h₂ : Tendsto (p.rulePathF R x₂) atTop (𝓝 L₂)) (hne : L₁ ≠ L₂) :
    (0 < R L₁ ∧ Tendsto (p.ruleSanctionsF R x₁) atTop (𝓝 (R L₁))) ∨
    (0 < R L₂ ∧ Tendsto (p.ruleSanctionsF R x₂) atTop (𝓝 (R L₂))) :=
  p.exists_pos_limit_sanction_of_limit_dependence
    (fun _ hx hx0 => hstrict.F_zero_lt_self hx hx0) hR_mem hR hx₁ hx₂ h₁ h₂ hne

/-- **Sharpness of zero-sanction descent.** If the zero-sanction transition has
a rest point `F(L,0) = L` at some `L ∈ (0,1]` — that is, `hD0` fails at `L` —
then both conclusions above fail for the zero rule `R ≡ 0`, which is feasible
and continuous:

* from the start `L` the path stays at `L`, so it converges to `L ≠ 0` while
  the limiting sanction is `0`, refuting `limit_eq_zero_of_limit_sanction_zero`;
* from the starts `0` and `L` the paths converge to the different limits `0`
  and `L` (`F(0,0) = 0` by `F_diag`), yet the limiting sanction is `0` from
  both, refuting `exists_pos_limit_sanction_of_limit_dependence`.

Economically: if some positive level of entrenchment survives a complete lifting
of sanctions, long-run dependence on the starting state no longer requires any
sanction at all. Since `F(x,0) ≤ x` always holds (`F_mono_s` and `F_diag`),
`hD0` fails at `L` exactly when `F(L,0) = L`, so the hypothesis is pointwise
necessary. General in `F` (BG2.2, Rule 11). -/
theorem limit_dependence_sharp_of_zero_sanction_fixed {L : ℝ}
    (hL : L ∈ Set.Ioc (0 : ℝ) 1) (hfix : p.F L 0 = L) :
    (¬ ∀ (R : ℝ → ℝ), (∀ x ∈ Sanctions.I, R x ∈ Sanctions.I) →
        ContinuousOn R Sanctions.I → ∀ x₀ L' : ℝ, x₀ ∈ Sanctions.I →
        Tendsto (p.rulePathF R x₀) atTop (𝓝 L') → R L' = 0 → L' = 0)
    ∧ (¬ ∀ (R : ℝ → ℝ), (∀ x ∈ Sanctions.I, R x ∈ Sanctions.I) →
        ContinuousOn R Sanctions.I → ∀ x₁ x₂ L₁ L₂ : ℝ,
        x₁ ∈ Sanctions.I → x₂ ∈ Sanctions.I →
        Tendsto (p.rulePathF R x₁) atTop (𝓝 L₁) →
        Tendsto (p.rulePathF R x₂) atTop (𝓝 L₂) → L₁ ≠ L₂ →
        0 < R L₁ ∨ 0 < R L₂) := by
  -- From a rest point of the zero-sanction transition, the zero rule's path
  -- is constant.
  have hconst : ∀ y, p.F y 0 = y → ∀ n, p.rulePathF (fun _ => (0 : ℝ)) y n = y := by
    intro y hy n
    induction n with
    | zero => rfl
    | succ k ih => rw [rulePathF_succ, ih]; exact hy
  have htend : ∀ y, p.F y 0 = y →
      Tendsto (p.rulePathF (fun _ => (0 : ℝ)) y) atTop (𝓝 y) := by
    intro y hy
    have hfun : p.rulePathF (fun _ => (0 : ℝ)) y = fun _ => y := funext (hconst y hy)
    rw [hfun]
    exact tendsto_const_nhds
  have hfeas : ∀ x ∈ Sanctions.I, (fun _ : ℝ => (0 : ℝ)) x ∈ Sanctions.I :=
    fun _ _ => ⟨le_rfl, zero_le_one⟩
  have hcont : ContinuousOn (fun _ : ℝ => (0 : ℝ)) Sanctions.I := continuousOn_const
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have hLI : L ∈ Sanctions.I := ⟨hL.1.le, hL.2⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hL.1.ne' (h (fun _ => 0) hfeas hcont L L hLI (htend L hfix) rfl)
  · rcases h (fun _ => 0) hfeas hcont 0 L 0 L h0I hLI (htend 0 (p.F_diag 0))
      (htend L hfix) hL.1.ne with h1 | h1
    · exact lt_irrefl (0 : ℝ) h1
    · exact lt_irrefl (0 : ℝ) h1

end Params
end AbstractGame
end Sanctions

#print axioms Sanctions.AbstractGame.Params.rulePathF_limit_isFixed
#print axioms Sanctions.AbstractGame.Params.exists_pos_limit_sanction_of_limit_dependence
#print axioms Sanctions.AbstractGame.Params.limit_dependence_sharp_of_zero_sanction_fixed
