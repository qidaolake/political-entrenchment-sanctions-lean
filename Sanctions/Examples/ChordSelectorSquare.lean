/-
Sanctions/Examples/ChordSelectorSquare.lean

**On the feasible states the chord class already makes the static Sender selector continuous.**

Plain words. In a chord economy the Sender's stage payoff is strongly concave in the sanction
(S4) and jointly continuous, so the Sender's one-period best response varies continuously with
the political state and the Target's compliance, at every state in `[0,1]` and every compliance
level. `ChordEconomy.σ_continuousOn_square` proves that from those two properties alone, through
the parametric Berge selector (`Foundations/Berge.lean`), without reading the class's field
`σ_continuous`.

What it does not do. The field asks for continuity on all of `ℝ × ℝ`, including states outside
`[0,1]`, where the class assumes nothing; that extension is not derivable, so the field stays
for now (author's decision, 2026-10-12: the field is kept this round, and restating the class
on the square, with the consumers that quantify over every real state, is a later round). This
file records that on the economically meaningful states the field adds nothing.

Moved from the audit's scratch proof (`suggestions/2026-10-10-jet-submission/audit-2026-10-11/
lean/H_Selector.lean.txt`, checked clean on 2026-10-11 against the HPC-built tree; axioms
`propext`, `Classical.choice`, `Quot.sound`). No new hypothesis (Rule 3); general in `F`.
-/
import Sanctions.Examples.ChordEconomy

namespace Sanctions
namespace Examples

open Set Filter Topology

noncomputable section

/-- The parameter set of the square: a state in `[0,1]` and any real compliance level. -/
abbrev SqParam : Type := {xa : ℝ × ℝ // xa.1 ∈ Icc (0 : ℝ) 1}

namespace ChordEconomy

variable (E : ChordEconomy)

/-- **The static selector is continuous on `[0,1] × ℝ`, from (S4) and payoff continuity.** -/
theorem σ_continuousOn_square :
    ContinuousOn (fun xa : ℝ × ℝ => E.σ xa.1 xa.2) (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  let f : SqParam → ℝ → ℝ := fun θ s => E.U_S θ.1.1 θ.1.2 s
  have hK : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  have hKne : (Icc (0 : ℝ) 1).Nonempty := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
  have hv : Continuous (fun θa : SqParam × ℝ => (θa.1 : ℝ × ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hg : Continuous (fun θa : SqParam × ℝ => ((θa.1 : ℝ × ℝ).1, (θa.1 : ℝ × ℝ).2, θa.2)) :=
    hv.fst.prodMk (hv.snd.prodMk continuous_snd)
  have hjoint : Continuous (fun θa : SqParam × ℝ => f θa.1 θa.2) := E.U_S_continuous.comp hg
  have hfc : ∀ θ : SqParam, ContinuousOn (f θ) (Icc (0 : ℝ) 1) := fun θ =>
    (hjoint.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hconc : ∀ θ : SqParam, StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (f θ) := fun θ =>
    E.stage_strictConcaveOn θ.2 θ.1.2
  have hcont := Sanctions.Foundations.Berge.argmax_continuous hK hKne hfc hconc hjoint
  have heq : ∀ θ : SqParam,
      E.σ θ.1.1 θ.1.2 = Sanctions.Foundations.Berge.argmax hK hKne hfc hconc θ := fun θ =>
    Sanctions.Foundations.Berge.argmax_eq_of_isMaxOn hK hKne hfc hconc θ (E.σ_mem _ _)
      (E.σ_isMaxOn_U_S _ _)
  rw [continuousOn_iff_continuous_restrict]
  have hψ : Continuous (fun p : ↥(Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) =>
      (⟨p.1, (Set.mem_prod.1 p.2).1⟩ : SqParam)) :=
    continuous_subtype_val.subtype_mk _
  have hfun : (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)).restrict (fun xa : ℝ × ℝ => E.σ xa.1 xa.2)
      = (Sanctions.Foundations.Berge.argmax hK hKne hfc hconc) ∘
        (fun p : ↥(Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) =>
          (⟨p.1, (Set.mem_prod.1 p.2).1⟩ : SqParam)) := by
    funext p
    exact heq ⟨p.1, (Set.mem_prod.1 p.2).1⟩
  rw [hfun]
  exact hcont.comp hψ

/-- In particular the stage response at defiance is continuous on `[0,1]` without the field. -/
theorem stageResp_continuousOn_of_concave :
    ContinuousOn (fun x : ℝ => E.σ x 0) (Icc (0 : ℝ) 1) := by
  have h := E.σ_continuousOn_square
  refine h.comp (by fun_prop : Continuous (fun x : ℝ => (x, (0 : ℝ)))).continuousOn ?_
  intro x hx
  exact ⟨hx, mem_univ _⟩

end ChordEconomy

end


end Examples
end Sanctions
