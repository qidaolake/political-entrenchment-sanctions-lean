/-
Sanctions/Theory/Basin/RelevantActionRegion.lean

**Audit-49 Item 3: relevant-action-region Sender slope discharger.**

The audit-49 critique (Step 4) observed that the existing
`h_stage_sender_α` field of `RegularEconomyCertificateComplianceCore`
takes the form

```
∀ E : FeedbackStackelbergEquilibriumTop, ∀ x ∈ Icc xS 1,
  LowerSlopeOn (fun s => p.U_S x (E.α x) s) (Icc 0 (max x sbar)) mS
```

i.e. the Sender stage payoff has positive marginal sanction benefit
at the Target action `E.α x` *whatever that action is*. Under literal
compliance this is economically strong: a national-welfare Sender
might not want more sanctions when the Target is already highly
compliant (`E.α x ≈ 1`).

This file introduces the **relevant-action-region** form:

* A cutoff function `abar : ℝ → ℝ` (the Sender's "relevant action
  region" — typically the low-compliance / hardline-action band).
* A region-restricted slope condition: positive marginal sanction
  benefit holds only when `E.α x ≤ abar x`.
* A cooperation hypothesis `hα_region : ∀ x ∈ basin, E.α x ≤ abar x`
  ensuring the equilibrium selector lies in the relevant region.

The two together discharge the uniform-in-`a` `LowerSlopeOn` at
`E.α x` — but only for the produced equilibrium and only on the basin
range, which is what the Goal-1/Goal-2/Goal-3 proofs actually need.

This file provides:

* `RelevantActionRegion p xS sbar abar mS` — a Prop bundling the
  region-restricted Sender slope condition.
* `stage_sender_slope_at_equilibrium_from_relevant_action_region` —
  the discharger: from the region-restricted slope and the region
  cooperation hypothesis, recover the per-E
  `LowerSlopeOn (fun s => p.U_S x (E.α x) s) …` form.

## Rule compliance

* **Rule 1.** No strategy changes — the cooperation hypothesis is
  evaluated at the equilibrium-derived `E.α`, not at any hand-chosen
  policy.
* **Rule 3.** Cat-(2) weakening: a uniform-in-`a` `LowerSlopeOn`
  hypothesis is replaced by a region-restricted version. Strictly
  weaker assumption surface. Pre-confirmed by user directive
  "Yes, do all the rule 3 deferred ones".
* **Rule 5.** Fully parametric over `p, abar, xS, sbar, mS`.
-/

import Sanctions.Theory.Certificates.TargetSanctionLossOffset

namespace Sanctions

open Set BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Relevant-action-region Sender slope

The audit-49 Step 4 weaker form of `h_stage_sender_α`. -/

/-- **Region-restricted Sender stage slope.** For every state
`x ∈ [xS, 1]` and every Target action `a ∈ I` *in the relevant
region* `[0, abar x]` (i.e. low-compliance / hardline actions), the
Sender stage payoff has minimum upward slope `mS` in sanctions on
`[0, max x sbar]`. -/
def RelevantActionRegionSenderSlope
    (xS sbar mS : ℝ) (abar : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc xS (1 : ℝ), ∀ a ∈ Sanctions.I,
    a ≤ abar x →
      LowerSlopeOn (fun s => p.U_S x a s)
        (Set.Icc (0 : ℝ) (max x sbar)) mS

/-- **Audit-49 Item 3 discharger.** If the region-restricted Sender
slope holds at all relevant actions, and the equilibrium selector
satisfies `E.α x ≤ abar x` on the basin, then the per-E
`LowerSlopeOn (fun s => p.U_S x (E.α x) s) …` form holds. -/
theorem stage_sender_slope_at_equilibrium_from_relevant_action_region
    {xS sbar mS : ℝ} {abar : ℝ → ℝ}
    (hxS_mem : xS ∈ Sanctions.I)
    (E : p.FeedbackStackelbergEquilibriumTop)
    (h_region : p.RelevantActionRegionSenderSlope xS sbar mS abar)
    (hα_region : ∀ x ∈ Set.Icc xS (1 : ℝ), E.α x ≤ abar x) :
    ∀ x ∈ Set.Icc xS (1 : ℝ),
      LowerSlopeOn
        (fun s => p.U_S x (E.α x) s)
        (Set.Icc (0 : ℝ) (max x sbar)) mS := by
  intro x hx
  have hα_feas : E.α x ∈ Sanctions.I := by
    apply E.α_mem
    refine ⟨?_, hx.2⟩
    -- From xS ∈ I we have 0 ≤ xS; combined with hx.1 : xS ≤ x gives 0 ≤ x.
    linarith [hxS_mem.1, hx.1]
  exact h_region x hx (E.α x) hα_feas (hα_region x hx)

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
