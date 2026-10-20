/-
Sanctions/Theory/Certificates/StandardComplianceBridges.lean

**Audit-49 follow-up Phase-C cleanup (Item 9 version): canonical
sign-correct loss-offset bridges, holding the actual proof bodies.**

This file owns the **actual proof bodies** of the two sign-correct
loss-offset bridges used by the canonical standard-compliance route.
`JETBridge.lean` retains compatibility aliases (`jet_*_lossOffset_on`)
that simply re-export the theorems below.

The motivation: in audit-49 Phase C the canonical names were
introduced as one-line aliases of the `jet_*` versions, but that left
the preferred local certificate depending on the legacy `JETBridge`
namespace via `StandardComplianceBridges → JETBridge`. The audit-49
follow-up Item-9 cleanup inverts the dependency: the proofs live
here, and `JETBridge` imports this file to re-export them under the
legacy `jet_*` names.

Imports needed for the proofs:

* `TargetSanctionLossOffset` — for `OneSidedSanctionPreferenceThresholds`
  and the sign-correct loss-offset discharger
  `of_stage_lowerSlopes_compliance_target_on`.
* `DifferentPolicyComparator` — for
  `dynamicTopRealizedRule_mono_of_singleCrossingOn`.
* `JointPreferenceBasin` — for
  `equilibriumTop_oneSidedThresholds_long_run_nonDecreasing` and
  `equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high`.

## Rule compliance

* **Rule 1** ✓ — no strategy changes; the proofs route through the
  same sign-correct chain as before.
* **Rule 3** — pure code move (proof bodies relocated from
  `JETBridge.lean` to here). No new assumption surface, no new
  Props or fields. Cat-(1) scaffolding.
* **Rule 5** ✓ — fully parametric.
-/

import Sanctions.Theory.Certificates.TargetSanctionLossOffset
import Sanctions.Theory.LockIn.DifferentPolicyComparator
import Sanctions.Theory.Basin.JointPreferenceBasin

namespace Sanctions

open Set

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Canonical sign-correct loss-offset bridges -/


/-- **Round 1.9 — Goal-1 persistence bridge in Milgrom-Shannon form.**

Sibling of
`persistence_at_equilibriumTop_from_target_combined_chord_on`
consuming a strict-monotonicity hypothesis on the stage Sender payoff
instead of the `LowerSlopeOn ... mS` form. No `m_S`, no `K_S`, no
contraction-margin numeric input — just qualitative
strict-monotonicity of `U_S(x, α(x), ·)` on the low sanction range,
plus monotonicity of `V_S`.

This is the Milgrom-Shannon ordinal form of Assumption 1: the Sender
stage payoff is strictly increasing in `s` on the relevant range, at
the equilibrium Target action, for every basin state. The
Lipschitz-strict-chord form (Round 37) was a cardinal sufficient
condition; this is the canonical ordinal one.

The dynamic-objective hypothesis is the Quah–Strulovici (2007)
interval-dominance-order family condition (`hIDO`), strictly weaker
than Milgrom–Shannon single crossing; any SCP discharge upcasts
freely via `IDOFamilyOn.of_singleCrossingOn`. -/
theorem persistence_at_equilibriumTop_from_target_combined_chord_MS_form
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT xS sbar x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hV_S_mono : Monotone E.V_S)
    (h_stage_sender_strictMono :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_target_combined :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        ∀ s₁ ∈ Set.Icc (max x sbar) (1 : ℝ),
        ∀ s₂ ∈ Set.Icc (max x sbar) (1 : ℝ),
        s₁ ≤ s₂ →
          p.U_T x (E.α x) s₁
              + p.β_T * E.V_T
                  (Sanctions.clipS' (p.F x s₁))
            ≤ p.U_T x (E.α x) s₂
              + p.β_T * E.V_T
                  (Sanctions.clipS' (p.F x s₂)))
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn
            Sanctions.I (Set.Icc (max xT xS) 1)
            (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀ : x₀ ∈ Set.Icc (max xT xS) 1) :
    (∀ n, p.dynamicTopLockInPath E.V_S E.α x₀ n
            ∈ Set.Icc (max xT xS) 1) ∧
    (∀ n, sbar ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    (∀ n, max xT xS ≤ p.dynamicTopLockInSanctions E.V_S E.α x₀ n) ∧
    Monotone (p.dynamicTopLockInSanctions E.V_S E.α x₀) ∧
    (∀ n, IsMaxOn
      (fun a => p.joint_T_top_integrand E.V_T E.V_S
                  (p.dynamicTopLockInPath E.V_S E.α x₀ n) a)
      Sanctions.I (E.α (p.dynamicTopLockInPath E.V_S E.α x₀ n))) := by
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α xT xS sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_sender_and_target_combined_chord
      p hV_S_mono hxT_mem hxS_mem hsbar_mem
      h_stage_sender_strictMono h_target_combined
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO
  exact equilibriumTop_oneSidedThresholds_long_run_nonDecreasing E
    hOne hTopMono hx₀

/-- **Round 1.11 — Goal-3 shock-hysteresis bridge in Milgrom-Shannon
form.** Sibling of `shock_at_equilibriumTop_from_lossOffset_on`
consuming MS-form inputs (the same set used by
`persistence_at_equilibriumTop_from_target_combined_chord_MS_form`).
Drops 5 hypotheses (`mS, KS, hKS_nonneg, hS_margin, hV_S_lip`),
adds 2 (`hV_S_mono, h_stage_sender_strictMono`); net -3.

Routes through the existing
`OneSidedSanctionPreferenceThresholds.of_stage_sender_and_target_combined_chord`
plus `equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high`.
The dynamic-objective hypothesis is the interval-dominance-order
family condition (`hIDO`), strictly weaker than Milgrom–Shannon
single crossing; SCP upcasts freely via
`IDOFamilyOn.of_singleCrossingOn`.

## Rule compliance
* **Rule 1** ✓ no strategies.
* **Rule 3** ✓ no new structural primitives; hypothesis form is the
  ordinal MS-strict-mono companion to the wedge-form bridge.
* **Rule 5** ✓ parametric. -/
theorem shock_at_equilibriumTop_from_target_combined_chord_MS_form
    (E : p.FeedbackStackelbergEquilibriumTop)
    {xT xS sbar x₀ : ℝ}
    (hxT_mem : xT ∈ Sanctions.I)
    (hxS_mem : xS ∈ Sanctions.I)
    (hsbar_mem : sbar ∈ Sanctions.I)
    (hsbar_pos : 0 < sbar)
    (hjoint_lt : max xT xS < 1)
    (hV_S_mono : Monotone E.V_S)
    (h_stage_sender_strictMono :
      ∀ x ∈ Set.Icc xS (1 : ℝ),
        StrictMonoOn (fun s => p.U_S x (E.α x) s)
          (Set.Icc (0 : ℝ) (max x sbar)))
    (h_target_combined :
      ∀ x ∈ Set.Icc xT (1 : ℝ),
        ∀ s₁ ∈ Set.Icc (max x sbar) (1 : ℝ),
        ∀ s₂ ∈ Set.Icc (max x sbar) (1 : ℝ),
        s₁ ≤ s₂ →
          p.U_T x (E.α x) s₁
              + p.β_T * E.V_T
                  (Sanctions.clipS' (p.F x s₁))
            ≤ p.U_T x (E.α x) s₂
              + p.β_T * E.V_T
                  (Sanctions.clipS' (p.F x s₂)))
    (hIDO : Sanctions.IntervalDominanceOrder.IDOFamilyOn
            Sanctions.I (Set.Icc (max xT xS) 1)
            (fun s x => p.senderDynObjective E.V_S x (E.α x) s))
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n
              ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, sbar
              ≤ p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      (∀ n, max xT xS
              ≤ p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      (∀ n, 0 < p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctions E.V_S E.α
                  (p.shockPath x₀ N)) ∧
      (∀ n, MonotoneOn
        (fun s => p.targetSanctionObjective E.V_T
          (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
          (E.α (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n))
          s)
        (Set.Icc
          (max (p.dynamicTopLockInPath E.V_S E.α (p.shockPath x₀ N) n)
            sbar) 1)) := by
  have hOne : p.OneSidedSanctionPreferenceThresholds
                E.V_T E.V_S E.α xT xS sbar :=
    OneSidedSanctionPreferenceThresholds.of_stage_sender_and_target_combined_chord
      p hV_S_mono hxT_mem hxS_mem hsbar_mem
      h_stage_sender_strictMono h_target_combined
  have hTopMono :
      MonotoneOn (p.dynamicTopRealizedRule E.V_S E.α)
        (Set.Icc (max xT xS) 1) :=
    p.dynamicTopRealizedRule_mono_of_IDOFamilyOn hIDO
  exact equilibriumTop_oneSidedThresholds_temporary_shock_permanent_high
    E hOne hsbar_pos hjoint_lt hTopMono hx₀_nn hx₀_le

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
