/-
Sanctions/Examples/Counterexamples/TiedStageMaximizers.lean

**A chord at a non-greatest stage maximiser does not put every dynamic maximiser
above every stage maximiser** (doc 68, L1′; the reader's finding C).

The strict Sender comparison `sender_dynamic_sanctions_gt_myopic_at_same_action`
orders the *supplied* stage maximiser below every forward-looking maximiser. The
manuscript once read it as ordering *every* stage maximiser. That reading is
false, and this file is the refutation, embedded in a full economy so that no
action is posited: the stage payoff `(3/2)x − 1/2 − s²(1−s)²` has stage
maximisers `{0, 1}` in the sanction; with the affine transition at rate `1/2`
and the Sender value `2y`, the continuation wedge at state `0` is `W(s) = s`,
strictly increasing; the chord holds at the stage maximiser `0` with `s' = 1/2`
(`1/16 < 1/4`); and the forward-looking objective `−s²(1−s)² + s/2 − 1/2` has
the unique maximiser `1`, which is *not* strictly above the stage maximiser `1`.

Rule 9: this refutes one universal and licenses nothing else. Rule 22:
affine-restricted and marked so.
-/
import Sanctions.Examples.PlacableSenderWitnesses
import Sanctions.Theory.LockIn.SenderInvestment

namespace Sanctions
namespace Examples

open Set AbstractGame BoundedContinuousFunction

noncomputable section

/-- The tied stage payoff: `(3/2)x − 1/2 − s²(1−s)²`. -/
def tiedU_S (x _a s : ℝ) : ℝ := (3 / 2) * x - 1 / 2 + (-(s ^ 2) * (1 - s) ^ 2)

theorem tiedU_S_continuous :
    Continuous (fun xas : ℝ × ℝ × ℝ => tiedU_S xas.1 xas.2.1 xas.2.2) := by
  unfold tiedU_S; fun_prop

theorem tiedU_S_le (x a : ℝ) {s : ℝ} : tiedU_S x a s ≤ tiedU_S x a 1 := by
  unfold tiedU_S
  nlinarith [sq_nonneg (s * (1 - s))]

/-- The economy: the affine member's transition and discounts, the tied stage
payoff, and the constant stage selector `1` (a stage argmax). -/
def tiedParams : Params :=
  { placableAffine.toParams with
    U_S := tiedU_S
    U_S_continuous := tiedU_S_continuous
    σ := fun _ _ => 1
    σ_mem := fun _ _ => ⟨zero_le_one, le_rfl⟩
    σ_isMaxOn_U_S := fun x a s _ => tiedU_S_le x a }

/-- **`tiedParams` has a continuous static Sender selector.** Affine-restricted: a
concrete member with the affine transition `affineF (1/2)`; the selector itself does not
read the transition. The proof is the one that was the economy's `σ_continuous` field
until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance tiedParams_staticSelectorContinuous :
    tiedParams.StaticSelectorContinuous where
  σ_continuous := continuous_const

theorem tiedParams_U_S : tiedParams.U_S = tiedU_S := rfl
theorem tiedParams_β_S : tiedParams.β_S = 1 / 2 := rfl
theorem tiedParams_F : tiedParams.F = affineF (1 / 2) := rfl

/-- The Sender value `2y`. -/
def tiedV : ChordEconomy.Val := ChordEconomy.affBCF 2 0

/-- The continuation wedge at state `0` is `s` itself. -/
theorem tied_wedge {s : ℝ} (hs : s ∈ Sanctions.I) :
    tiedParams.senderSanctionContinuation tiedV 0 s = s := by
  unfold Params.senderSanctionContinuation tiedV
  rw [tiedParams_F]
  have hmem : affineF (1 / 2) 0 s ∈ (Sanctions.S : Set ℝ) := by
    unfold affineF; constructor <;> nlinarith [hs.1, hs.2]
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem hmem]
  unfold affineF; ring

/-- **The refutation.** At state `0` and compliance `0`: the wedge is strictly
increasing, the chord holds at the stage maximiser `0`, and yet the
all-stage-maximiser conclusion fails, because `1` is both a stage maximiser and
the forward-looking maximiser. -/
theorem tied_stage_maximizers_counterexample :
    ∃ (p : Params) (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a s' : ℝ),
      x ∈ Sanctions.I ∧ a ∈ Sanctions.I ∧ s' ∈ Sanctions.I ∧ 0 < p.β_S ∧
      (∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
        p.senderSanctionContinuation V_S x s₁ < p.senderSanctionContinuation V_S x s₂) ∧
      (∃ sM ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I sM ∧
        p.U_S x a sM - p.U_S x a s'
          < p.β_S * (p.senderSanctionContinuation V_S x s'
                      - p.senderSanctionContinuation V_S x sM)) ∧
      ¬ (∀ t ∈ Sanctions.I, IsMaxOn (fun s => p.U_S x a s) Sanctions.I t →
          ∀ d ∈ Sanctions.I,
            IsMaxOn (fun s => p.U_S x a s + p.β_S * p.senderSanctionContinuation V_S x s)
              Sanctions.I d → t < d) := by
  refine ⟨tiedParams, tiedV, 0, 0, 1 / 2, ⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩,
    ⟨by norm_num, by norm_num⟩, by rw [tiedParams_β_S]; norm_num, ?_, ?_, ?_⟩
  · intro s₁ hs₁ s₂ hs₂ h
    rw [tied_wedge hs₁, tied_wedge hs₂]; exact h
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
    · intro s _
      show tiedParams.U_S 0 0 s ≤ tiedParams.U_S 0 0 0
      rw [tiedParams_U_S]; unfold tiedU_S
      nlinarith [sq_nonneg (s * (1 - s))]
    · rw [tied_wedge ⟨by norm_num, by norm_num⟩, tied_wedge ⟨le_rfl, zero_le_one⟩,
        tiedParams_β_S, tiedParams_U_S]
      unfold tiedU_S; norm_num
  · intro hall
    have h1max : IsMaxOn (fun s => tiedParams.U_S 0 0 s) Sanctions.I 1 := by
      intro s _
      show tiedParams.U_S 0 0 s ≤ tiedParams.U_S 0 0 1
      rw [tiedParams_U_S]; exact tiedU_S_le 0 0
    have h1dyn : IsMaxOn
        (fun s => tiedParams.U_S 0 0 s + tiedParams.β_S * tiedParams.senderSanctionContinuation tiedV 0 s)
        Sanctions.I 1 := by
      intro s hs
      show tiedParams.U_S 0 0 s + tiedParams.β_S * tiedParams.senderSanctionContinuation tiedV 0 s
        ≤ tiedParams.U_S 0 0 1 + tiedParams.β_S * tiedParams.senderSanctionContinuation tiedV 0 1
      rw [tied_wedge hs, tied_wedge ⟨zero_le_one, le_rfl⟩, tiedParams_β_S, tiedParams_U_S]
      unfold tiedU_S
      nlinarith [sq_nonneg (s * (1 - s)), hs.2]
    have := hall 1 ⟨zero_le_one, le_rfl⟩ h1max 1 ⟨zero_le_one, le_rfl⟩ h1dyn
    exact lt_irrefl _ this

end

#print axioms Sanctions.Examples.tied_stage_maximizers_counterexample

end Examples
end Sanctions
