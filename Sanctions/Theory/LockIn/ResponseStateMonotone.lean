/-
Sanctions/Theory/LockIn/ResponseStateMonotone.lean

**The Sender's upper dynamic response is monotone in the political state under
interval dominance — in particular single crossing — at the value.**

The state-side sibling of `σ_dyn_top_antitoneOn_a_of_SenderActionDD`. That
theorem moves the *compliance* argument and needs decreasing differences of the
stage payoff alone, because the continuation does not depend on compliance.
Moving the *state* is different: the continuation `β_S·V_S(F x s)` depends on
the state through the transition, so the single-crossing condition here is on
the whole dynamic objective at the value, not on the stage payoff. Economically
it says the inherited hardline state and the marginal sanction are net
complements for the forward-looking Sender — the stage rally effect covering
the saturation of the continuation and the cross-effectiveness of the
transition. No functional form of `F` enters (Rule 22).

Nothing here is assumed of the model. The lead result is
`σ_dyn_top_monotoneOn_x_of_IDO` (round I): interval dominance of the dynamic
objective in (sanction; state) at the value orders the *greatest* response,
with no uniqueness hypothesis; `σ_dyn_top_monotoneOn_x_of_singleCrossing'` is
its single-crossing corollary. The older
`σ_dyn_top_monotoneOn_x_of_singleCrossing` (headline row 34) adds state-local
uniqueness and keeps its statement as the pinned compatibility form. All are
discharged in `Examples/` for the placable-Sender family from chord conditions
on the transition (`Foundations/CrossDifferenceSemiconvex`), and vacuously
under the affine law.

The successor corollary `F_σ_dyn_top_monotoneOn_of_monotoneOn` is the
`hsucc_mono` shape that `joint_T_integrand_lowerSlope_of_joint_chord` consumes,
so the general Target-side slope preservation needs nothing further. A weaker
sufficient condition — the response may *fall*, provided no faster than the
state's own persistence `glo/dhi` per unit of state — would also give it and is
not pursued here.
-/
import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Theory.Equilibrium.SelectionRobust
import Sanctions.Foundations.SingleCrossingOfIncreasingDifferences

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Monotone response in the state from single crossing at the value.** If the
Sender's dynamic objective `U_S x a s + β_S·V_S(F x s)` satisfies single
crossing in `(sanction; state)` and the dynamic argmax is unique at every
state, then the upper dynamic response is nondecreasing in the state. Topkis
through the lattice form: the lower of the two responses maximises at the lower
state, and uniqueness there identifies it with that state's response. -/
theorem σ_dyn_top_monotoneOn_x_of_singleCrossing
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (a : ℝ)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn Sanctions.I Sanctions.S
      (fun s x => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s))))
    (h_unique : p.DynamicArgmaxUnique V_S) :
    MonotoneOn (fun x => p.σ_dyn_top V_S x a) Sanctions.S := by
  intro x hx y hy hxy
  simp only
  have hmx := p.σ_dyn_top_isMaxOn V_S x a
  have hmy := p.σ_dyn_top_isMaxOn V_S y a
  have hρx := p.σ_dyn_top_mem_I V_S x a
  have hρy := p.σ_dyn_top_mem_I V_S y a
  obtain ⟨hmin, -⟩ := Sanctions.MilgromShannon.monotone_argmax_of_singleCrossingOn hSC hxy hx hy
    hρx hρy (fun z hz => isMaxOn_iff.mp hmx z hz) (fun z hz => isMaxOn_iff.mp hmy z hz)
  rcases le_total (p.σ_dyn_top V_S x a) (p.σ_dyn_top V_S y a) with h | h
  · exact h
  · rw [min_eq_right h] at hmin
    have hmax_y_at_x : IsMaxOn (fun s' => p.U_S x a s'
        + p.β_S * V_S (Sanctions.clipS' (p.F x s'))) Sanctions.I (p.σ_dyn_top V_S y a) :=
      isMaxOn_iff.mpr hmin
    exact le_of_eq (h_unique x hx a _ _ hρx hρy hmx hmax_y_at_x)

/-! ## Without uniqueness (round I, doc 75 R2)

The uniqueness binder above is consumed by that proof and is unnecessary for
the conclusion. The greatest maximiser is monotone on its own: for `x ≤ y`,
`max(σ(x), σ(y))` maximises at `y` (Quah–Strulovici 2009, Theorem 1, formalised
as `monotone_argmax_of_IDOFamilyOn`), and `σ(y)` is the supremum of the argmax
at `y`, so `σ(x) ≤ max(σ(x), σ(y)) ≤ σ(y)`. Interval dominance of the family is
the natural hypothesis; single crossing implies it
(`IDOFamilyOn.of_singleCrossingOn`). Nothing here says an *arbitrary* selection
among tied maximisers is monotone (a constant objective refutes that), nor that
the greatest selector is continuous. -/

/-- **Monotone greatest response in the state from interval dominance alone.** -/
theorem σ_dyn_top_monotoneOn_x_of_IDO
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (a : ℝ)
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn Sanctions.I Sanctions.S
      (fun s x => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s)))) :
    MonotoneOn (fun x => p.σ_dyn_top V_S x a) Sanctions.S := by
  intro x hx y hy hxy
  simp only
  have hmx := p.σ_dyn_top_isMaxOn V_S x a
  have hmy := p.σ_dyn_top_isMaxOn V_S y a
  have hρx := p.σ_dyn_top_mem_I V_S x a
  have hρy := p.σ_dyn_top_mem_I V_S y a
  have hmax : IsMaxOn (fun s' => p.U_S y a s' + p.β_S * V_S (Sanctions.clipS' (p.F y s')))
      Sanctions.I (max (p.σ_dyn_top V_S x a) (p.σ_dyn_top V_S y a)) :=
    Sanctions.IntervalDominanceOrder.monotone_argmax_of_IDOFamilyOn (convex_Icc 0 1) hIDO
      hx hy hxy hρx hρy hmx hmy
  have hmem : max (p.σ_dyn_top V_S x a) (p.σ_dyn_top V_S y a)
      ∈ p.dynamicArgmaxSet V_S y a :=
    ⟨⟨le_max_of_le_left hρx.1, max_le hρx.2 hρy.2⟩, hmax⟩
  exact le_trans (le_max_left _ _) (le_csSup (p.dynamicArgmaxSet_bddAbove V_S y a) hmem)

/-- **Monotone greatest response in the state from single crossing alone**: the
conclusion of `σ_dyn_top_monotoneOn_x_of_singleCrossing` without its
uniqueness binder, through the single-crossing ⇒ interval-dominance bridge. -/
theorem σ_dyn_top_monotoneOn_x_of_singleCrossing'
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (a : ℝ)
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn Sanctions.I Sanctions.S
      (fun s x => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s)))) :
    MonotoneOn (fun x => p.σ_dyn_top V_S x a) Sanctions.S :=
  p.σ_dyn_top_monotoneOn_x_of_IDO V_S a
    (Sanctions.IntervalDominanceOrder.IDOFamilyOn.of_singleCrossingOn hSC)

/-- The cardinal form: increasing differences of the dynamic objective in
`(sanction; state)` give the same conclusion, through the bridge in
`Foundations/SingleCrossingOfIncreasingDifferences`. (Its uniqueness binder is
likewise unnecessary; see `σ_dyn_top_monotoneOn_x_of_singleCrossing'`.) -/
theorem σ_dyn_top_monotoneOn_x_of_increasingDifferences
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (a : ℝ)
    (hID : Sanctions.MilgromShannon.IncreasingDifferencesOn Sanctions.I Sanctions.S
      (fun s x => p.U_S x a s + p.β_S * V_S (Sanctions.clipS' (p.F x s))))
    (h_unique : p.DynamicArgmaxUnique V_S) :
    MonotoneOn (fun x => p.σ_dyn_top V_S x a) Sanctions.S :=
  p.σ_dyn_top_monotoneOn_x_of_singleCrossing V_S a
    (Sanctions.MilgromShannon.singleCrossingOn_of_increasingDifferencesOn hID) h_unique

/-- **A monotone response gives a monotone realised successor.** Both arguments
of the transition rise with the state, so the closed-loop successor
`x ↦ F x (σ_dyn_top V_S x a)` is nondecreasing. This is the `hsucc_mono`
hypothesis of `joint_T_integrand_lowerSlope_of_joint_chord`. -/
theorem F_σ_dyn_top_monotoneOn_of_monotoneOn
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (a : ℝ)
    (hmono : MonotoneOn (fun x => p.σ_dyn_top V_S x a) Sanctions.S) :
    MonotoneOn (fun x => p.F x (p.σ_dyn_top V_S x a)) Sanctions.S := by
  intro x hx y hy hxy
  simp only
  calc p.F x (p.σ_dyn_top V_S x a) ≤ p.F y (p.σ_dyn_top V_S x a) := p.F_mono_x _ hxy
    _ ≤ p.F y (p.σ_dyn_top V_S y a) := p.F_mono_s _ (hmono hx hy hxy)

end Params
end AbstractGame
end Sanctions
