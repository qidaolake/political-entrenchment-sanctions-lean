/-
Sanctions/Postulates/ParamsOfCube.lean

**A formal economy from data given only on the cube** (doc 54 §5, doc 60 §2 P1;
closes the "constructor from cube data" item left open on 2026-09-04).

`Params` maintains its transition monotone on all of `ℝ` and its payoffs and
stage selector continuous on all of `ℝ³` / `ℝ²`, because global hypotheses are
easier to carry through the order arguments. The manuscript claims this costs
no generality. `Foundations/TransitionExtension` proved it for the transition;
this file proves it for the whole economy:

* `CubeData` collects exactly the cube-defined data — payoffs continuous on
  the cube, a stage selector feasible, continuous and argmax on the square, a
  transition continuous, coordinatewise monotone and diagonal-fixing on the
  square, and the two discount factors `β_T`, `β_S`. Feasibility of the
  transition on the square is derived (`CubeData.F_mem`), not a field (round
  BC, 2026-09-29). The slot `δ` is not data either (round BJ5.2, 2026-10-07):
  it is the inert affine-rate slot of `Params`, which only the affine family
  `affineF δ` reads, and the transition built here is the extension of `F` and
  never reads it, so `toParams` fills it with `1/2`.
* `CubeData.toParams` builds a `Params` from it: payoffs and selector are
  composed with the clip, the transition is `TransitionExtension.extend`.
  The selector's continuity on the square supplies the instance
  `D.toParams.StaticSelectorContinuous` (round BJ5.1: no longer a `Params`
  field).
* `toParams_U_S_on_cube`, `toParams_U_T_on_cube`, `toParams_σ_on_square`,
  `toParams_F_on_square` say the constructed economy **agrees with the data**
  on the cube and square, so every theorem stated over `Params` applies to
  every cube-defined economy, evaluated where the economy is defined.

Rule 3: no assumption — the fields of `CubeData` are the cube restrictions of
the fields of `Params`, nothing more. Rule 22: the transition is extended, not
given a form. Rule 19: the generic clip and extension lemmas are in
`Foundations`; this file only assembles a `Params`.
-/
import Sanctions.Postulates.AbstractGame
import Sanctions.Foundations.TransitionExtension

namespace Sanctions
namespace AbstractGame

open Set

/-- The data of an economy on the cube `[0,1]³` and the square `[0,1]²`. -/
structure CubeData where
  β_T : ℝ
  β_T_mem : β_T ∈ Ico (0 : ℝ) 1
  β_S : ℝ
  β_S_mem : β_S ∈ Ico (0 : ℝ) 1
  /-- Target stage payoff on the cube. -/
  U_T : ℝ → ℝ → ℝ → ℝ
  /-- Sender stage payoff on the cube. -/
  U_S : ℝ → ℝ → ℝ → ℝ
  /-- Stage Sender selector on the square. -/
  σ : ℝ → ℝ → ℝ
  σ_mem : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, σ x a ∈ Icc (0 : ℝ) 1
  σ_continuousOn :
    ContinuousOn (fun xa : ℝ × ℝ => σ xa.1 xa.2) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  σ_isMaxOn_U_S : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
    IsMaxOn (fun s => U_S x a s) (Icc (0 : ℝ) 1) (σ x a)
  U_T_continuousOn :
    ContinuousOn (fun xas : ℝ × ℝ × ℝ => U_T xas.1 xas.2.1 xas.2.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  U_S_continuousOn :
    ContinuousOn (fun xas : ℝ × ℝ × ℝ => U_S xas.1 xas.2.1 xas.2.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  /-- Transition on the square. -/
  F : ℝ → ℝ → ℝ
  F_continuousOn :
    ContinuousOn (fun xs : ℝ × ℝ => F xs.1 xs.2) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  F_mono_x : ∀ s ∈ Icc (0 : ℝ) 1, MonotoneOn (fun x => F x s) (Icc (0 : ℝ) 1)
  F_mono_s : ∀ x ∈ Icc (0 : ℝ) 1, MonotoneOn (fun s => F x s) (Icc (0 : ℝ) 1)
  F_diag : ∀ t ∈ Icc (0 : ℝ) 1, F t t = t

namespace CubeData

/-- A three-argument function composed with the clip in each argument. -/
def clipCube3 (U : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun x a s => U (clipS x) (clipS a) (clipS s)

theorem clipCube3_continuous {U : ℝ → ℝ → ℝ → ℝ}
    (hU : ContinuousOn (fun xas : ℝ × ℝ × ℝ => U xas.1 xas.2.1 xas.2.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :
    Continuous (fun xas : ℝ × ℝ × ℝ => clipCube3 U xas.1 xas.2.1 xas.2.2) := by
  have hc : Continuous (fun xas : ℝ × ℝ × ℝ => (clipS xas.1, clipS xas.2.1, clipS xas.2.2)) :=
    (clipS_continuous.comp continuous_fst).prodMk
      ((clipS_continuous.comp (continuous_fst.comp continuous_snd)).prodMk
        (clipS_continuous.comp (continuous_snd.comp continuous_snd)))
  exact hU.comp_continuous hc (fun xas => ⟨clipS_mem _, clipS_mem _, clipS_mem _⟩)

theorem clipCube3_eq_on_cube (U : ℝ → ℝ → ℝ → ℝ) {x a s : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    clipCube3 U x a s = U x a s := by
  unfold clipCube3
  rw [TransitionExtension.clipS_of_mem hx, TransitionExtension.clipS_of_mem ha,
    TransitionExtension.clipS_of_mem hs]

variable (D : CubeData)

/-- **Feasibility on the square is derived.** The transition sends the square
into `[0,1]`: coordinatewise monotonicity and the fixed diagonal put `F x s`
between `x` and `s`. A field until round BC (2026-09-29, doc 110 R1a); now a
theorem with the field's statement. -/
theorem F_mem : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, D.F x s ∈ Icc (0 : ℝ) 1 := by
  intro x hx s hs
  rcases le_total x s with h | h
  · have h1 : D.F x x ≤ D.F x s := D.F_mono_s x hx hx hs h
    have h2 : D.F x s ≤ D.F s s := D.F_mono_x s hs hx hs h
    rw [D.F_diag x hx] at h1
    rw [D.F_diag s hs] at h2
    exact ⟨hx.1.trans h1, h2.trans hs.2⟩
  · have h1 : D.F x s ≤ D.F x x := D.F_mono_s x hx hs hx h
    have h2 : D.F s s ≤ D.F x s := D.F_mono_x s hs hs hx h
    rw [D.F_diag x hx] at h1
    rw [D.F_diag s hs] at h2
    exact ⟨hs.1.trans h2, h1.trans hx.2⟩

/-- **The formal economy built from cube data.** General in `F` (the transition
is the extension of the data's `F`). The affine-rate slot `δ` is filled with
`1/2` (round BJ5.2, 2026-10-07): no theorem about a cube-built economy reads it,
since its transition is not `affineF δ`, so `CubeData` no longer asks for it.
(`noncomputable` because real division is.) -/
noncomputable def toParams : Params where
  δ := 1 / 2
  δ_mem := by norm_num
  β_T := D.β_T
  β_T_mem := D.β_T_mem
  β_S := D.β_S
  β_S_mem := D.β_S_mem
  U_T := clipCube3 D.U_T
  U_S := clipCube3 D.U_S
  σ := fun x a => D.σ (clipS x) (clipS a)
  σ_mem := fun x a => D.σ_mem _ (clipS_mem x) _ (clipS_mem a)
  σ_isMaxOn_U_S := by
    intro x a
    have h := D.σ_isMaxOn_U_S _ (clipS_mem x) _ (clipS_mem a)
    rw [isMaxOn_iff] at h ⊢
    intro s hs
    simp only [clipCube3]
    rw [TransitionExtension.clipS_of_mem hs,
      TransitionExtension.clipS_of_mem (D.σ_mem _ (clipS_mem x) _ (clipS_mem a))]
    exact h s hs
  U_T_continuous := clipCube3_continuous D.U_T_continuousOn
  U_S_continuous := clipCube3_continuous D.U_S_continuousOn
  F := TransitionExtension.extend D.F
  F_continuous := TransitionExtension.extend_continuous D.F D.F_continuousOn
  F_mono_x := TransitionExtension.extend_mono_x D.F D.F_mono_x
  F_mono_s := TransitionExtension.extend_mono_s D.F D.F_mono_s
  F_diag := TransitionExtension.extend_diag D.F D.F_diag

/-- **The cube-built economy's static selector is continuous.** The data's
selector is continuous on the square, and `toParams` composes it with the clip,
so the built selector is jointly continuous on `ℝ × ℝ`. General in `F`. Until
round BJ5.1 (2026-10-07) this was the `σ_continuous` field of `toParams`; it is
now the instance the myopic-comparator and static-Sender results read, and every
cube-built economy carries it with no further assumption. -/
instance toParams_staticSelectorContinuous : D.toParams.StaticSelectorContinuous where
  σ_continuous := by
    have hc : Continuous (fun xa : ℝ × ℝ => (clipS xa.1, clipS xa.2)) :=
      (clipS_continuous.comp continuous_fst).prodMk (clipS_continuous.comp continuous_snd)
    exact D.σ_continuousOn.comp_continuous hc (fun xa => ⟨clipS_mem _, clipS_mem _⟩)

/-! ## Agreement with the data where the economy is defined -/

theorem toParams_U_S_on_cube {x a s : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    D.toParams.U_S x a s = D.U_S x a s :=
  clipCube3_eq_on_cube D.U_S hx ha hs

theorem toParams_U_T_on_cube {x a s : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    D.toParams.U_T x a s = D.U_T x a s :=
  clipCube3_eq_on_cube D.U_T hx ha hs

theorem toParams_σ_on_square {x a : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (0 : ℝ) 1) :
    D.toParams.σ x a = D.σ x a := by
  change D.σ (clipS x) (clipS a) = D.σ x a
  rw [TransitionExtension.clipS_of_mem hx, TransitionExtension.clipS_of_mem ha]

theorem toParams_F_on_square {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    D.toParams.F x s = D.F x s :=
  TransitionExtension.extend_eq_on_square D.F hx hs

theorem toParams_β_T : D.toParams.β_T = D.β_T := rfl
theorem toParams_β_S : D.toParams.β_S = D.β_S := rfl

/-- **Strict adjustment transfers from the square.** If the data satisfies the
ordinal condition (F5) on the square, so does the constructed economy. -/
theorem toParams_strictAdjustment
    (hlt : ∀ ⦃x s : ℝ⦄, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → s < x → D.F x s < x)
    (hgt : ∀ ⦃x s : ℝ⦄, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → x < s → x < D.F x s) :
    D.toParams.StrictAdjustment := by
  refine ⟨fun x s hx hs h => ?_, fun x s hx hs h => ?_⟩
  · rw [D.toParams_F_on_square hx hs]; exact hlt hx hs h
  · rw [D.toParams_F_on_square hx hs]; exact hgt hx hs h

end CubeData

end AbstractGame

/-! ## Rule 10 -/

#print axioms Sanctions.AbstractGame.CubeData.toParams
#print axioms Sanctions.AbstractGame.CubeData.toParams_staticSelectorContinuous
#print axioms Sanctions.AbstractGame.CubeData.toParams_U_S_on_cube
#print axioms Sanctions.AbstractGame.CubeData.toParams_strictAdjustment

end Sanctions
