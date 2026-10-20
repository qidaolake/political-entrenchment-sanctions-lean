/-
Sanctions/Theory/Mechanism/ZeroDiscountSelector.lean

**The selector identity at zero Sender discount, under a unique stage argmax.**

`RegimeSelectorBridge` proves that at `β_S = 0` the Sender's forward-looking
argmax *set* is the stage argmax set, and records why that is not yet a
*selector* identity: two maximisers of the same set-valued problem need not be
the same point. This file adds the one hypothesis that closes the gap — the
stage argmax is a singleton — and delivers `σ_dyn_top V_S x a = p.σ x a` and
`σ_dyn V_S x a = p.σ x a`, for every continuation value `V_S`.

The hypothesis is stated as a theorem input over `Params` (Rule 3: no new
field). On the chord economy it is a theorem: the Sender's stage payoff is
strongly concave in the sanction at every compliance level (S4), so the stage
argmax is the selector `σ` and nothing else (on the quadratic–linear family,
the clipped vertex). That discharge is what makes the fully myopic equilibrium
inhabit `RegimeEquilibrium p00` (`Examples/PlacableSenderRegimes`).
-/
import Sanctions.Theory.Mechanism.RegimeSelectorBridge
import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Foundations.Berge

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Selector identity at `β_S = 0` (top selector).** If the stage argmax at
`(x, a)` is a singleton, the greatest forward-looking selector is the
primitive stage selector, whatever the continuation value. -/
theorem σ_dyn_top_eq_σ_of_βS_zero (hβ : p.β_S = 0)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ)
    (huniq : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I,
      IsMaxOn (fun s => p.U_S x a s) Sanctions.I s₁ →
      IsMaxOn (fun s => p.U_S x a s) Sanctions.I s₂ → s₁ = s₂) :
    p.σ_dyn_top V_S x a = p.σ x a := by
  have hmax : IsMaxOn (fun s' => p.senderDynObjective V_S x a s') Sanctions.I
      (p.σ_dyn_top V_S x a) := p.σ_dyn_top_isMaxOn V_S x a
  have hstage := (p.isMaxOn_senderDyn_iff_stage_of_βS_zero hβ V_S x a _).mp hmax
  exact huniq _ (p.σ_dyn_top_mem_I V_S x a) _ (p.σ_mem x a) hstage (p.σ_isMaxOn_U_S x a)

/-- **Selector identity at `β_S = 0` (choice selector).** -/
theorem σ_dyn_eq_σ_of_βS_zero (hβ : p.β_S = 0)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ)
    (huniq : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I,
      IsMaxOn (fun s => p.U_S x a s) Sanctions.I s₁ →
      IsMaxOn (fun s => p.U_S x a s) Sanctions.I s₂ → s₁ = s₂) :
    p.σ_dyn V_S x a = p.σ x a := by
  have hmax : IsMaxOn (fun s' => p.senderDynObjective V_S x a s') Sanctions.I
      (p.σ_dyn V_S x a) := p.σ_dyn_isMaxOn V_S x a
  have hstage := (p.isMaxOn_senderDyn_iff_stage_of_βS_zero hβ V_S x a _).mp hmax
  exact huniq _ (p.σ_dyn_mem V_S x a) _ (p.σ_mem x a) hstage (p.σ_isMaxOn_U_S x a)

/-- **From strict stage concavity.** A strictly concave stage payoff in the
sanction has a unique maximiser on `[0,1]`, so both selector identities hold. -/
theorem σ_dyn_top_eq_σ_of_βS_zero_of_strictConcaveOn (hβ : p.β_S = 0)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ)
    (hsc : StrictConcaveOn ℝ Sanctions.I (fun s => p.U_S x a s)) :
    p.σ_dyn_top V_S x a = p.σ x a :=
  p.σ_dyn_top_eq_σ_of_βS_zero hβ V_S x a
    (fun _ hs₁ _ hs₂ h₁ h₂ =>
      Sanctions.Foundations.Berge.isMaxOn_unique_of_strictConcaveOn hsc hs₁ hs₂ h₁ h₂)

theorem σ_dyn_eq_σ_of_βS_zero_of_strictConcaveOn (hβ : p.β_S = 0)
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x a : ℝ)
    (hsc : StrictConcaveOn ℝ Sanctions.I (fun s => p.U_S x a s)) :
    p.σ_dyn V_S x a = p.σ x a :=
  p.σ_dyn_eq_σ_of_βS_zero hβ V_S x a
    (fun _ hs₁ _ hs₂ h₁ h₂ =>
      Sanctions.Foundations.Berge.isMaxOn_unique_of_strictConcaveOn hsc hs₁ hs₂ h₁ h₂)

end Params
end AbstractGame

end

end Sanctions
