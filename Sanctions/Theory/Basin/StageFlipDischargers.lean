/-
Sanctions/Theory/Basin/StageFlipDischargers.lean

**Rounds B3-B6 (post-sweep): four dischargers composing the stage-flip
primitives with the E-arc machinery.**

1. **B3 — next-state monotonicity** (`nextStateTop_mono_of_stageID_chordConcave`):
   reparametrizing the Sender's choice by the NEXT STATE
   `y = F(x,s) = (1−δ)x + δs` makes the continuation `V_S(y)` a
   function of the choice alone — it cancels identically from every
   increasing-differences check, with NO condition on `V_S`. The
   remaining stage term has ID in `(y; x)` from `SenderStageID` plus
   weak chord concavity of `U_S` in `s`
   (`SenderChordConcaveInS` — the derivative-free consequence of the
   R44 uniform strict concavity, recorded here as a route extension
   of that approved assumption, not a new primitive). Conclusion: the
   greatest next-state selector `x ↦ F(x, σ_top(x,a))` is monotone
   per fixed action. Anchor: Amir 1996 / Hopenhayn-Prescott 1992;
   change-of-variables pattern per Acemoglu-Jensen 2013 §4.1.1.
   Caveats (recorded): delivers the TRANSFORMED single crossing;
   realized-sanction monotonicity would additionally need a
   `y`-chord-slope ≥ `1−δ` comparison, and the realized (α-composed)
   version needs α-antitonicity (E4).

2. **B4 — diagonal residual discharger**
   (`h_diag_of_pivot_action_frontier`): the stage-flip certificate's
   above-floor diagonal input (chords on `[s̄, x]` at the equilibrium
   action clearing the wedge, for every basin state and carrier pair)
   is derived from: α-antitonicity on the basin (E4, under
   `SubstitutedTargetDD`), the R28 action-complementarity sign
   (`SenderActionDD`), `SenderStageID`, and a single **pivot-action
   frontier condition** — wedge-level chords at the FIXED pivot
   action `α(x̂_S)` along the diagonal frontier states
   `max(s₂, x̂_S)`. Chain: frontier at the pivot action ⇒ propagate
   UP in the state (`SenderStageID`) ⇒ propagate DOWN in the action
   from `α(x̂_S)` to `α(x) ≤ α(x̂_S)` (`SenderActionDD` + antitone α).
   This retires the per-basin-state quantification of the previous
   `h_diag` input in favour of a one-action one-parameter family.

3. **B5 — myopic-ceiling discharger**
   (`hMyoCeiling_of_stage_strictAntiOn_above_floor`): the
   certificate's myopic-ceiling field (the stage best response at the
   myopic action stays at or below the dynamic floor) is derived from
   a stage-level condition: the Sender stage payoff is strictly
   decreasing in the sanction above the floor AT the myopic action —
   "at the myopic (more compliant) action, the state has not crossed
   the diagonal flip above the floor", which is exactly coherent with
   the compliance-placates frontier. The σ-difference bridge to fully
   primitive form remains open (recorded).

4. **B6 — selector-robust monotonicity of the myopic response**
   (`σ_mono_in_x_of_strictID`): under the STRICT Sender stage
   complementarity (`SenderStageIDStrict`, the recorded E3
   strengthening), the stage best response `σ(·, a)` is monotone in
   the state — for EVERY selection, not only extremal ones
   (Topkis 2.8.4-5 flavour via
   `argmax_selections_mono_of_strict_ID`).

## Rule compliance

**Rule 3** — `SenderChordConcaveInS` is the chord-form consequence of
the R44 user-approved uniform strict concavity of `U_S` in `s`,
consumed here on the stage-flip route (route extension recorded; no
new primitive); the B4 frontier condition is a strict subset of the
previous `h_diag` input; B5's condition replaces an
equilibrium-object field by a stage-level condition; B6 consumes the
recorded E3 strengthening. **Rule 5** ✓ parametric. **Rule 19** ✓ —
generic selection lemmas live in `Foundations/MonotoneThreshold.lean`.
-/

import Sanctions.Theory.Basin.StageFlipCertificate
import Sanctions.Theory.Certificates.SubstitutedTargetMCS

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## B3 — next-state coordinates -/

/-- **Weak chord concavity of `U_S` in the sanction.** Equal-length
sanction increments weakly rise when both endpoints shift down — the
derivative-free consequence of the R44 uniform strict concavity
(`∂²U_S/∂s² ≤ −c_σ < 0`), recorded as a route extension of that
approved assumption. -/
def SenderChordConcaveInS : Prop :=
  ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I, ∀ s₁ s₂ c : ℝ,
    0 ≤ c → 0 ≤ s₁ - c → s₁ ≤ s₂ → s₂ ≤ 1 →
    p.U_S x a s₂ - p.U_S x a s₁
      ≤ p.U_S x a (s₂ - c) - p.U_S x a (s₁ - c)


/-- **The certificate's diagonal input from a pivot-action frontier
condition (Round B4).** Inputs: `SenderStageID`, the R28 sign
(`SenderActionDD`), α-antitonicity on the basin (available from E4's
`α_on_antitoneOn_of_substitutedDD` under `SubstitutedTargetDD`), and
the wedge-level frontier condition at the SINGLE pivot action
`α(x̂_S)` along the diagonal states `max(s₂, x̂_S)`. Output: the
`h_diag` input of
`StandardComplianceLocalCoreCertificate.of_stage_flip` — a strict
reduction of its quantification. -/
theorem h_diag_of_pivot_action_frontier
    (D : p.ValueClass2) {sbar mS : ℝ}
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hID_S : p.SenderStageID)
    (hDD_a : p.SenderActionDD)
    (hpivot_mem : p.senderFlipPivot sbar mS ∈ Sanctions.I)
    (hanti : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      AntitoneOn (D.α_on V_T V_S)
        (Set.Icc (p.senderFlipPivot sbar mS) 1))
    (hfrontier : ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ s₁ s₂ : ℝ, sbar ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
        mS * (s₂ - s₁) ≤
          p.U_S (max s₂ (p.senderFlipPivot sbar mS))
            (D.α_on V_T V_S (p.senderFlipPivot sbar mS)) s₂
          - p.U_S (max s₂ (p.senderFlipPivot sbar mS))
              (D.α_on V_T V_S (p.senderFlipPivot sbar mS)) s₁) :
    ∀ (V_T : D.CarrierT) (V_S : D.CarrierS),
      ∀ x ∈ Set.Icc (p.senderFlipPivot sbar mS) (1 : ℝ), sbar < x →
        LowerSlopeOn (fun s => p.U_S x (D.α_on V_T V_S x) s)
          (Set.Icc sbar x) mS := by
  intro V_T V_S x hx _hsx s₁ hs₁ s₂ hs₂ hs
  have hpiv_in : p.senderFlipPivot sbar mS
      ∈ Set.Icc (p.senderFlipPivot sbar mS) (1 : ℝ) :=
    ⟨le_refl _, hpivot_mem.2⟩
  have hα_le : D.α_on V_T V_S x
      ≤ D.α_on V_T V_S (p.senderFlipPivot sbar mS) :=
    hanti V_T V_S hpiv_in hx hx.1
  have hs₁I : s₁ ∈ Sanctions.I :=
    ⟨le_trans hsbar_mem.1 hs₁.1, le_trans hs₁.2 hx.2⟩
  have hs₂I : s₂ ∈ Sanctions.I :=
    ⟨le_trans hsbar_mem.1 hs₂.1, le_trans hs₂.2 hx.2⟩
  have hxI : x ∈ Sanctions.I := ⟨le_trans hpivot_mem.1 hx.1, hx.2⟩
  have hax_mem := D.α_on_mem V_T V_S x
  have ha₀_mem := D.α_on_mem V_T V_S (p.senderFlipPivot sbar mS)
  -- Action propagation: chord at α(x) ≥ chord at the pivot action.
  have hDD := hDD_a x hxI hs₁I hs₂I hs hax_mem ha₀_mem hα_le
  -- State propagation: chord at x ≥ chord at the diagonal state.
  have hxp_le : max s₂ (p.senderFlipPivot sbar mS) ≤ x :=
    max_le hs₂.2 hx.1
  have hxpI : max s₂ (p.senderFlipPivot sbar mS) ∈ Sanctions.I :=
    ⟨le_trans hpivot_mem.1 (le_max_right _ _),
     max_le hs₂I.2 hpivot_mem.2⟩
  have hIDx := hID_S (D.α_on V_T V_S (p.senderFlipPivot sbar mS))
    ha₀_mem hs₁I hs₂I hs hxpI hxI hxp_le
  have hfr := hfrontier V_T V_S s₁ s₂ hs₁.1 hs hs₂I.2
  simp only at hDD hIDx ⊢
  linarith

/-! ## B5 — myopic ceiling from stage strict antitonicity above the floor -/

/-- **Any stage maximizer sits at or below a strict-decrease
threshold.** If the Sender stage payoff is strictly decreasing in the
sanction on `[t, 1]`, the stage best response is at most `t`. -/
theorem σ_le_of_stage_strictAntiOn_above
    {x a t : ℝ} (ht_mem : t ∈ Sanctions.I)
    (hanti : StrictAntiOn (fun s => p.U_S x a s) (Set.Icc t 1)) :
    p.σ x a ≤ t := by
  by_contra h
  have hlt : t < p.σ x a := lt_of_not_ge h
  have hσI := p.σ_mem x a
  have h1 : p.U_S x a (p.σ x a) < p.U_S x a t :=
    hanti ⟨le_refl t, ht_mem.2⟩ ⟨le_of_lt hlt, hσI.2⟩ hlt
  have h2 : p.U_S x a t ≤ p.U_S x a (p.σ x a) :=
    p.σ_isMaxOn_U_S x a ⟨ht_mem.1, ht_mem.2⟩
  linarith

/-- **Myopic-ceiling discharger (Round B5).** The certificate field
`hMyoCeiling` — the myopic stage response stays at or below the
dynamic floor on the basin — follows from a stage-level condition:
the Sender stage payoff is strictly decreasing above the floor AT
the myopic equilibrium action ("the myopic action is on the
un-flipped side of the diagonal above the floor"). -/
theorem hMyoCeiling_of_stage_strictAntiOn_above_floor
    (M : p.MyopicFeedbackEquilibrium) {xbar sbar : ℝ}
    (hxbar_nn : 0 ≤ xbar) (hsbar_mem : sbar ∈ Sanctions.I)
    (h : ∀ x ∈ Set.Icc xbar (1 : ℝ),
      StrictAntiOn (fun s => p.U_S x (M.α x) s)
        (Set.Icc (max x sbar) 1)) :
    ∀ x ∈ Set.Icc xbar (1 : ℝ), p.σ x (M.α x) ≤ max x sbar := by
  intro x hx
  have hfloor_mem : max x sbar ∈ Sanctions.I :=
    ⟨le_trans hxbar_nn (le_max_of_le_left hx.1),
     max_le hx.2 hsbar_mem.2⟩
  exact p.σ_le_of_stage_strictAntiOn_above hfloor_mem (h x hx)

/-! ## B6 — selector-robust monotonicity of the myopic response -/

/-- **The stage best response is monotone in the state under strict
complementarity (Round B6).** Under `SenderStageIDStrict`, EVERY
selection of the stage argmax — in particular the primitive `σ` —
is monotone in the state at any fixed action. Selector-robust:
no greatest-selector convention is used. -/
theorem σ_mono_in_x_of_strictID {a : ℝ} (ha : a ∈ Sanctions.I)
    (hID : p.SenderStageIDStrict) :
    MonotoneOn (fun x => p.σ x a) Sanctions.I := by
  intro x hx x' hx' hxx'
  rcases eq_or_lt_of_le hxx' with rfl | hlt
  · exact le_refl _
  exact Sanctions.MonotoneThreshold.argmax_selections_mono_of_strict_ID
    (f := fun s t => p.U_S t a s) (S := Sanctions.I)
    hlt (p.σ_mem x a) (p.σ_mem x' a)
    (fun z hz => p.σ_isMaxOn_U_S x a hz)
    (fun z hz => p.σ_isMaxOn_U_S x' a hz)
    (fun s₁ s₂ h₁ h₂ hslt => hID a ha s₁ h₁ s₂ h₂ hslt hx hx' hlt)

end Params
end AbstractGame

end

end Sanctions
