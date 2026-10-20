/-
Sanctions/Examples/CoupledRoute/LowDeltaWindowWitness.lean

**The P1a′ low-δ route-A window witness: the first economy where the
kernel-width window is provably NONEMPTY.**

The interior shocked-existence theorem
(`shockedFeedbackStackelbergTop_interior_discharged_canonical`,
`Theory/Shocked/ShockedLeaderLipschitz.lean`) consumes the leader-regularity
primitive `h_obj_diff` — the Stackelberg-coupling estimate saying the leader
objective-*difference* is action-Lipschitz with constant `L_lead · dist V W` —
as an accepted open assumption (register § "Shock interior-existence assumption
surface"). The 2026-07-04 kernel-width audit proved that the route-A C²-kernel
(double-box smear) derivation of `h_obj_diff` is quantitatively IMPOSSIBLE at
the P3 mechanism economy (`mechanismWitnessParams`, δ = 1/5): the
admissible-width window is empty there. That closure is FINAL and this file
does not touch it. The same audit showed the window OPENS at low δ.

This file formalizes the audit's verified design point (`docs/archive/workflow-scratch/w1a_p1a_spec.md`,
adversarially confirmed 2026-07-11): the **δ-only-modified P3 economy**

  U_S(x,a,s) = a − (3/5)s² − s(1/10 + a/2 − (27/20)x) + (2/5)x   (unchanged)
  U_T(x,a,s) = −a² + 2xa − a − s(1/2 − a/2 − x)                  (unchanged)
  β_S = 1/2, β_T = 9/10, basin [1/2, 77/100]                     (unchanged)
  δ = 1/100  (was 1/5),   box-kernel half-width h = 1/10,

at which ALL FOUR route-A window inequalities hold simultaneously with exact
rational margins:

  (C1) geometric window `4h < 1`                          margin 3/20;
  (C2) realized-state no-clip on the basin: for every basin state and every
       sanction level, the ±2h double-box window around the realized next
       state stays inside [0,1]                           margins 59/200, 277/10000;
  (C3) smeared Sender concavity `c_S(h) = c_S_stage − β_S·δ²·M_S/h²
       = 37877/32000 > 0` (the stage concavity 6/5 survives the worst-case
       curvature the smeared continuation can subtract);
  (C4) leader contraction `L_lead = T1 + T2 + T3
       = 1115314143680/7762983835019 ≈ 0.1437 < 1/2`, i.e. the contraction
       margin `β_S + L_Ua·(2·L_lead/c_T) < 1` holds       slack ≈ 0.3563,
       and it is ROBUST to the audit's flagged chain-form ambiguity (the
       repo factor-2 argmax-core κ_a doubles T2: L_lead ≈ 0.2400, still < 1/2).

Consequence, after the 2026-07-25 repair: the actual witness
`lowDeltaShocked` still uses the one-box moving average.  The new general
one-box semiconcavity theorem is already enough to prove the complete Sender
objective's carrier-uniform strong concavity and the unique selector's
continuity (`coupled_sender_strongConcave` and
`coupled_sigmaDynTop_continuous_subtype`).  It is **not** enough to discharge
the two-sided `h_obj_diff`: the advertised carrier-uniform all-actions
Sender-value channel is formally refuted by
`not_coupledLeaderObj_sender_uniform_advertised`.  The narrower
realised-leader-only premise would require control of how the selector's
action slope changes with the continuation value, while one-box smoothing
supplies a Lipschitz first derivative but no uniform second derivative.
Thus (C1)--(C4) remain valid arithmetic for the separately designed
double-box route, but they are not advertised as an instantiated proof for
the present one-box economy.  Carrier invariance is independently refuted on
the Target side at the endogenous zero continuation pair by
`coupledZeroPair_target_image_not_mem`.  On the Sender side,
`coupledSteepPolicy_sender_image_not_mem` proves only that continuity and
feasibility do not imply invariance; selected-policy Sender invariance remains
unresolved.

Chain provenance (each factor's Lean anchor):
* `Lσ = 2·β_S·Lκ·LF/c` — `sigma_top_lipschitz_in_V`
  (`ShockedLeaderLipschitz.lean`), with `Lκ = 1/h` the box-kernel creation
  bound `movAvg_lipschitz` (`Foundations/MovingAverage.lean`) and `LF = δ`
  the affine-transition action-Lipschitz constant;
* `L_VT = (L_UT + β_T·L_smVT·LF)·Lσ/(1−β_T)` — `VTdyn_shock_lipschitz`
  (`ShockedLeaderLipschitz.lean`), with `L_smVT = M_T/h` the closed form
  `movAvgShockedParams_smear_lipschitz` (`MovingAverageShock.lean`);
* contraction-margin form `β_S + L_Ua·(2·L_lead/c_T) < 1` —
  `shockedFeedbackStackelbergTop_interior_discharged(_canonical)`, consumed
  at `c_T = 2`, `L_Ua = 1` exactly as at P3
  (`MechanismWitnessShocked.lean`);
* `κ_a`, `K_S`, `G`, `T1..T3` — spec algebra only (no Lean-side constant
  exists yet); stated at the explicit exact rationals with docstrings tying
  each to the chain (`docs/archive/workflow-scratch/w1a_p1a_spec.md` § Design algebra).

Carrier norms behind the constants (δ-independent vertex/corner exhaustion,
certified in the spec): `‖U_S‖ = 523/320`, `‖U_T‖ = 2`, hence invariant-ball
radii `M_S = ‖U_S‖/(1−β_S) = 523/160` and `M_T = ‖U_T‖/(1−β_T) = 20`; stage
constants `c_S_stage = 6/5`, `|∂²U_S/∂s∂a| = |∂²U_T/∂a∂s| = 1/2`, `L_UT = 1`,
`L_Ux = 7/4`, `c_T = 2`, `L_Ua = 1`.

**Standing prohibition honored**: nothing here re-derives or perturbs the P3
economy at δ = 1/5; `lowDeltaParams` is the modified economy the audit itself
said would open.
-/

import Sanctions.Theory.Shocked.ShockedLeaderLipschitz
import Sanctions.Theory.Shocked.MovingAverageShock
import Sanctions.Examples.MechanismWitness

namespace Sanctions
namespace Examples

open AbstractGame
open scoped NNReal
open BoundedContinuousFunction

/-! ## The economy: P3 stage payoffs, δ = 1/100 -/

/-- **The low-δ window economy (P1a′).** The P3 mechanism-witness stage payoffs
`mwU_S`/`mwU_T`, static selector `mwσ`, and discount factors `β_S = 1/2`,
`β_T = 9/10` — all UNCHANGED from `mechanismWitnessParams` — with only the
transition speed lowered to `δ = 1/100` (from P3's `1/5`). This is the
δ-only modification at which the 2026-07-04 kernel-width audit's route-A
window opens. All Rule-1 optimality couplings (`mwσ_isMaxOn`) are inherited
verbatim because the stage payoffs are δ-independent. -/
noncomputable def lowDeltaParams : Sanctions.AbstractGame.Params where
  δ := 1 / 100
  δ_mem := by constructor <;> norm_num
  β_T := 9 / 10
  β_T_mem := by constructor <;> norm_num
  β_S := 1 / 2
  β_S_mem := by constructor <;> norm_num
  U_T := mwU_T
  U_S := mwU_S
  σ := mwσ
  σ_mem := mwσ_mem
  σ_isMaxOn_U_S := mwσ_isMaxOn
  U_T_continuous := mwU_T_continuous
  U_S_continuous := mwU_S_continuous
  F := Sanctions.AbstractGame.affineF (1 / 100)
  F_continuous := Sanctions.AbstractGame.affineF_continuous _
  F_mono_x := Sanctions.AbstractGame.affineF_mono_x (by constructor <;> norm_num)
  F_mono_s := Sanctions.AbstractGame.affineF_mono_s (by constructor <;> norm_num)
  F_diag := Sanctions.AbstractGame.affineF_diag _

/-- **`lowDeltaParams` has a continuous static Sender selector.** Affine-restricted: a
concrete member with the affine transition `affineF (1/100)`; the selector itself does not
read the transition. The proof is the one that was the economy's `σ_continuous` field
until round BJ5.1 (2026-10-07), when the condition left `Params` for the class
`Params.StaticSelectorContinuous`; the myopic-comparator and static-Sender results can use it
at this economy. -/
instance lowDeltaParams_staticSelectorContinuous :
    lowDeltaParams.StaticSelectorContinuous where
  σ_continuous := mwσ_continuous

@[simp] theorem lowDeltaParams_U_S : lowDeltaParams.U_S = mwU_S := rfl
@[simp] theorem lowDeltaParams_U_T : lowDeltaParams.U_T = mwU_T := rfl
@[simp] theorem lowDeltaParams_δ : lowDeltaParams.δ = 1 / 100 := rfl
@[simp] theorem lowDeltaParams_β_S : lowDeltaParams.β_S = 1 / 2 := rfl
@[simp] theorem lowDeltaParams_β_T : lowDeltaParams.β_T = 9 / 10 := rfl
@[simp] theorem lowDeltaParams_F :
    lowDeltaParams.F = Sanctions.AbstractGame.affineF (1 / 100) := rfl

/-! ## Kernel wiring: the box shock at half-width h = 1/10 -/

/-- Positivity of the design kernel half-width `h = 1/10`. -/
theorem lowDeltaH_pos : (0 : ℝ) < 1 / 10 := by norm_num

/-- **The shocked low-δ economy**: `lowDeltaParams` under the uniform box
(moving-average) kernel of half-width `h = 1/10`, realised as a genuine
`ShockedParams` via the parametric wiring layer `movAvgShockedParams`
(exactly the `eatonEngersMovAvgShock` / `mwShocked` pattern, pinned at the
audited design width). -/
noncomputable def lowDeltaShocked : AbstractGame.ShockedParams :=
  AbstractGame.movAvgShockedParams lowDeltaParams lowDeltaH_pos

@[simp] theorem lowDeltaShocked_toParams :
    lowDeltaShocked.toParams = lowDeltaParams := rfl

@[simp] theorem lowDeltaShocked_smear :
    lowDeltaShocked.smear = Sanctions.movAvgBCF lowDeltaH_pos := rfl

/-- **`L_smVT` at the design point**: the box smear of the shocked low-δ
economy is state-Lipschitz with the closed-form constant `‖V‖/h = 10‖V‖`
(instantiating `movAvgShockedParams_smear_lipschitz`; on the Target
invariant ball `‖V‖ ≤ M_T = 20` this is the chain value `M_T/h = 200`). -/
theorem lowDeltaShocked_smear_lipschitz (V : SBCF)
    (z z' : ↥(Sanctions.S : Set ℝ)) :
    |lowDeltaShocked.smear V z - lowDeltaShocked.smear V z'|
      ≤ (‖V‖ / (1 / 10)) * dist z z' :=
  AbstractGame.movAvgShockedParams_smear_lipschitz lowDeltaParams lowDeltaH_pos V z z'

/-! ## The window certificate

The four inequalities the 2026-07-04 kernel-width audit requires for the
route-A (C²-kernel) discharge of `h_obj_diff`, certified at the exact design
rationals `(δ, h) = (1/100, 1/10)`. At P3 (δ = 1/5) this system is provably
infeasible; here every inequality closes by `norm_num` with the exact margins
recorded in the spec. -/

/-- **(C1) Geometric window: `4h < 1`.** The double-box support `±2h` fits
inside the unit state space with room to translate (margin `1/4 − h = 3/20`). -/
theorem lowDelta_window_C1 : 4 * ((1 : ℝ) / 10) < 1 := by norm_num

/-- (C1) margin: `1/4 − h = 3/20`. -/
theorem lowDelta_window_C1_margin : (1 : ℝ) / 4 - 1 / 10 = 3 / 20 := by norm_num

/-- **(C2) Basin no-clip, single-window form.** For every basin state
`x ∈ [1/2, 77/100]` and every sanction level `s ∈ [0,1]`, the realized next
state `F(x,s) = (1−δ)x + δs` stays in `[2h, 1−2h]` — so the ±2h double-box
kernel window around it never reaches the clip boundary. -/
theorem lowDelta_window_C2 :
    ∀ x ∈ Set.Icc (1 / 2 : ℝ) (77 / 100), ∀ s ∈ Set.Icc (0 : ℝ) 1,
      lowDeltaParams.F x s ∈ Set.Icc (2 * (1 / 10) : ℝ) (1 - 2 * (1 / 10)) := by
  intro x hx s hs
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hs1, hs2⟩ := hs
  simp only [lowDeltaParams_F, Sanctions.AbstractGame.affineF, Set.mem_Icc]
  constructor <;> linarith

/-- **(C2) Basin no-clip, translated-window form.** Every point of the ±2h
window around the realized next state lies in `[0,1]`: for basin `x`, any
`s ∈ [0,1]`, and any translate `|t| ≤ 2h`, `F(x,s) + t ∈ [0,1]`. This is the
membership the double-box (C²) smear evaluations need so that `clipS'` acts
as the identity along the whole kernel support. -/
theorem lowDelta_window_C2_double :
    ∀ x ∈ Set.Icc (1 / 2 : ℝ) (77 / 100), ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ t : ℝ, |t| ≤ 2 * (1 / 10) →
        lowDeltaParams.F x s + t ∈ Set.Icc (0 : ℝ) 1 := by
  intro x hx s hs t ht
  rw [abs_le] at ht
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hs1, hs2⟩ := hs
  simp only [lowDeltaParams_F, Sanctions.AbstractGame.affineF, Set.mem_Icc]
  constructor <;> linarith [ht.1, ht.2]

/-- **(C2) No-clip realized literally**: on the translated window the clip map
`clipS` is the identity — the shocked evaluations along the kernel support
read the value function at the *unclipped* realized state. -/
theorem lowDelta_window_C2_noclip :
    ∀ x ∈ Set.Icc (1 / 2 : ℝ) (77 / 100), ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ t : ℝ, |t| ≤ 2 * (1 / 10) →
        (Sanctions.clipS' (lowDeltaParams.F x s + t)).val
          = lowDeltaParams.F x s + t := by
  intro x hx s hs t ht
  obtain ⟨h0, h1⟩ := lowDelta_window_C2_double x hx s hs t ht
  simp only [Sanctions.clipS', Sanctions.clipS]
  rw [min_eq_right h1, max_eq_right h0]

/-- (C2a) exact lower margin: `(1−δ)·x_lo − 2h = 59/200`. -/
theorem lowDelta_window_C2a_margin :
    (1 - (1 : ℝ) / 100) * (1 / 2) - 2 * (1 / 10) = 59 / 200 := by norm_num

/-- (C2b) exact upper margin: `(1−2h) − ((1−δ)·x_hi + δ) = 277/10000`. -/
theorem lowDelta_window_C2b_margin :
    (1 - 2 * ((1 : ℝ) / 10)) - ((1 - 1 / 100) * (77 / 100) + 1 / 100)
      = 277 / 10000 := by norm_num

/-- **(C3) Smeared Sender concavity is strictly positive.** The stage
concavity `c_S_stage = 6/5` of `U_S` in `s` survives the worst-case curvature
`β_S·δ²·M_S/h²` that the C²-smeared continuation can subtract
(`M_S = 523/160` is the Sender invariant-ball radius `‖U_S‖/(1−β_S)`):
`c_S(h) = 6/5 − β_S·δ²·M_S/h² > 0`. At P3 (δ = 1/5) this positivity forces
`h > 0.233`, incompatible with no-clip; at δ = 1/100 it needs only
`h > ≈ 0.0117` — cleared 8.6× at `h = 1/10`. -/
theorem lowDelta_window_C3 :
    (0 : ℝ) < 6 / 5
      - lowDeltaParams.β_S * lowDeltaParams.δ ^ 2 * (523 / 160) / (1 / 10) ^ 2 := by
  simp only [lowDeltaParams_β_S, lowDeltaParams_δ]
  norm_num

/-- (C3) exact value: `c_S(h) = 37877/32000` at the design point. -/
theorem lowDelta_window_C3_eq :
    6 / 5 - lowDeltaParams.β_S * lowDeltaParams.δ ^ 2 * (523 / 160) / (1 / 10) ^ 2
      = (37877 : ℝ) / 32000 := by
  simp only [lowDeltaParams_β_S, lowDeltaParams_δ]
  norm_num

/-! ### The C4 contraction chain, factor by factor

Every intermediate of the audit's `L_lead` chain as an exact rational
identity. Factors with a Lean-side anchor are stated in the anchor's own
form (`Lσ` from `sigma_top_lipschitz_in_V`; `L_VT` from
`VTdyn_shock_lipschitz` with `L_smVT = M_T/h` from
`movAvgShockedParams_smear_lipschitz`); the remaining factors
(`κ_a`, `K_S`, `G`, `T1`–`T3`) exist only as spec algebra and are stated at
the explicit rationals. -/

/-- **Chain: `Lσ = 2·β_S·Lκ·LF/c_S = 3200/37877`** — the σ-Lipschitz constant
of `sigma_top_lipschitz_in_V` at the box-kernel creation bound `Lκ = 1/h = 10`
(`movAvg_lipschitz`), transition action-Lipschitz `LF = δ`, and the smeared
concavity `c_S = 37877/32000` of (C3). -/
theorem lowDelta_chain_Lσ :
    2 * lowDeltaParams.β_S * (1 / (1 / 10)) * lowDeltaParams.δ / (37877 / 32000)
      = (3200 : ℝ) / 37877 := by
  simp only [lowDeltaParams_β_S, lowDeltaParams_δ]
  norm_num

/-- **Chain: `κ_a = |∂²U_S/∂s∂a|/c_S = 16000/37877`** — the follower argmax's
action-Lipschitz constant (favorable IFT form; the repo argmax-core pattern of
`Foundations/StrongConcaveArgmax` yields `2×` this, covered by
`lowDelta_window_C4_robust`). Spec algebra only; `|∂²U_S/∂s∂a| = 1/2` at the
P3 payoffs. -/
theorem lowDelta_chain_κa :
    ((1 : ℝ) / 2) / (37877 / 32000) = 16000 / 37877 := by norm_num

/-- **Chain: `L_VT = (L_UT + β_T·L_smVT·LF)·Lσ/(1−β_T) = 12800/5411`** — the
slaved-Target-value Lipschitz constant of `VTdyn_shock_lipschitz`, at
`L_UT = 1`, `L_smVT = M_T/h = 200` (the closed form
`movAvgShockedParams_smear_lipschitz` on the Target ball `‖V‖ ≤ 20`),
`LF = δ`, and `Lσ = 3200/37877`. -/
theorem lowDelta_chain_LVT :
    (1 + lowDeltaParams.β_T * (20 / (1 / 10)) * lowDeltaParams.δ) * (3200 / 37877)
        / (1 - lowDeltaParams.β_T)
      = (12800 : ℝ) / 5411 := by
  simp only [lowDeltaParams_β_T, lowDeltaParams_δ]
  norm_num

/-- **Chain: `K_S = L_Ux + β_S·(M_S/h)·(1−δ) = 57377/3200`** — the Sender
Bellman-image state-Lipschitz constant (spec algebra; `L_Ux = 7/4` is the
`U_S` state-Lipschitz constant, `M_S/h = 523/16` the smear creation bound on
the Sender ball). Phase-2 gap: needs a carrier-restricted Lean restatement. -/
theorem lowDelta_chain_KS :
    (7 : ℝ) / 4
        + lowDeltaParams.β_S * ((523 / 160) / (1 / 10)) * (1 - lowDeltaParams.δ)
      = 57377 / 3200 := by
  simp only [lowDeltaParams_β_S, lowDeltaParams_δ]
  norm_num

/-- **Chain: `G = max|∂U_T/∂s| + β_T·δ·(M_T/h) = 14/5`** — the bound on the
composed leader-objective sanction-slope (spec algebra; `max|∂U_T/∂s| = 1` at
the P3 payoffs). -/
theorem lowDelta_chain_G :
    1 + lowDeltaParams.β_T * lowDeltaParams.δ * (20 / (1 / 10)) = (14 : ℝ) / 5 := by
  simp only [lowDeltaParams_β_T, lowDeltaParams_δ]
  norm_num

/-- **Chain: `T1 = |∂²U_T/∂a∂s|·Lσ = 1600/37877`** — the direct
cross-partial term of the leader objective-difference (spec algebra;
`|∂²U_T/∂a∂s| = 1/2` at the P3 payoffs). -/
theorem lowDelta_chain_T1 :
    ((1 : ℝ) / 2) * (3200 / 37877) = 1600 / 37877 := by norm_num

/-- **Chain: `T2 = κ_a·β_T·δ·[L_VT/h + (M_T/h²)·δ·Lσ] = 138240000/37877²`**
— the slaved-Target-value channel of the leader objective-difference
(spec algebra; `37877² = 1434667129`). -/
theorem lowDelta_chain_T2 :
    (16000 / 37877) * lowDeltaParams.β_T * lowDeltaParams.δ
        * ((12800 / 5411) / (1 / 10)
            + (20 / (1 / 10) ^ 2) * lowDeltaParams.δ * (3200 / 37877))
      = (138240000 : ℝ) / 1434667129 := by
  simp only [lowDeltaParams_β_T, lowDeltaParams_δ]
  norm_num

/-- **Chain: `T3 = G·|∂²U_S/∂s∂a|·β_S·δ²·[1/h² + (K_S/h²)·δ·Lσ]/c_S²
= 39373588480/7762983835019`** — the follower-response-derivative channel
(the term whose `δ²/h²` scaling kills P3 and opens at low δ; spec algebra;
`7762983835019 = 37877³/7`). -/
theorem lowDelta_chain_T3 :
    (14 / 5) * (1 / 2) * lowDeltaParams.β_S * lowDeltaParams.δ ^ 2
        * (1 / (1 / 10) ^ 2
            + ((57377 / 3200) / (1 / 10) ^ 2) * lowDeltaParams.δ * (3200 / 37877))
        / (37877 / 32000) ^ 2
      = (39373588480 : ℝ) / 7762983835019 := by
  simp only [lowDeltaParams_β_S, lowDeltaParams_δ]
  norm_num

/-- **Chain sum: `L_lead = T1 + T2 + T3 = 1115314143680/7762983835019`.** -/
theorem lowDelta_chain_Llead :
    (1600 : ℝ) / 37877 + 138240000 / 1434667129 + 39373588480 / 7762983835019
      = 1115314143680 / 7762983835019 := by norm_num

/-- **(C4) Contraction: `L_lead < 1/2`.** The derived leader coupling constant
beats the budget `(1−β_S)·c_T/(2·L_Ua) = 1/2` with slack ≈ 0.3563. -/
theorem lowDelta_window_C4 :
    (1115314143680 : ℝ) / 7762983835019 < 1 / 2 := by norm_num

/-- (C4) exact slack: `1/2 − L_lead = 5532355547659/15525967670038`. -/
theorem lowDelta_window_C4_slack :
    (1 : ℝ) / 2 - 1115314143680 / 7762983835019
      = 5532355547659 / 15525967670038 := by norm_num

/-- **(C4) robustness to the chain-form ambiguity**: with the repo-pinned
factor-2 argmax-core `κ_a` (the `Foundations/StrongConcaveArgmax` pattern) instead of
the favorable IFT value, `T2` doubles and the window is STILL open:
`L_lead = 1863330783680/7762983835019 ≈ 0.2400 < 1/2`. (The audit's frontier
point δ = 1/54 dies under this doubling; the design point δ = 1/100 does not —
this is why the witness is built here and not at the frontier.) -/
theorem lowDelta_window_C4_robust :
    (1600 : ℝ) / 37877 + 2 * (138240000 / 1434667129) + 39373588480 / 7762983835019
        = 1863330783680 / 7762983835019
      ∧ (1863330783680 : ℝ) / 7762983835019 < 1 / 2 := by
  constructor <;> norm_num

/-- **(C4) in the exact form consumed by the interior existence theorem**:
`β_S + L_Ua·(2·L_lead/c_T) < 1` at the actual Lean-side `β_S` of the shocked
low-δ economy, with `L_Ua = 1`, `c_T = 2` (the P3-inherited leader constants)
and the certified `L_lead`. This is the `hmargin` hypothesis of
`shockedFeedbackStackelbergTop_interior_discharged_canonical`, discharged
arithmetically. -/
theorem lowDelta_contraction_margin :
    lowDeltaShocked.toParams.β_S
        + 1 * (2 * ((1115314143680 : ℝ) / 7762983835019) / 2) < 1 := by
  have hβ : lowDeltaShocked.toParams.β_S = 1 / 2 := rfl
  rw [hβ]; norm_num

/-! ## Conditional analytic wrapper at the window economy

The following implication instantiates the canonical interior theorem at
`lowDeltaShocked`.  Its scalar arithmetic is checked exactly, but it still
consumes the leader selector, continuity, strong concavity, optimality, and
objective-difference geometry.  It is therefore an optional witness-level
consistency check, not a constructed existence result and not a headline.
The symbolic quadratic-growth sensitivity theorem in
`Foundations/ArgmaxSensitivity.lean` is the preferred interface for future
discharge work. -/

/- Retired numerical existence wrapper (2026-07-27, user-approved).
The historical declaration is kept as commented audit evidence below; it no
longer enters the Lean environment.  Its objective-difference coefficient and
curvature modulus were assumed inside an existence theorem rather than derived
through the symbolic canonical carrier theorem.
/-- **Conditional purified-existence implication at the low-δ window.**
The exact rational constants are discharged, while the decisive analytic
leader package is supplied as hypotheses.  This declaration must not be cited
as an unconditional or constructed low-δ equilibrium witness. -/
theorem lowDelta_purified_existence
    (lead : SBCF → (ℝ → ℝ))
    (lead_cont : ∀ V, Continuous (lead V))
    (lead_mem : ∀ V, ∀ x ∈ Sanctions.S, lead V x ∈ Sanctions.I)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V) xa.1 xa.2))
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I 2
        (fun a => lowDeltaShocked.toParams.joint_T_top_integrand
          (lowDeltaShocked.smear (lowDeltaShocked.V_T_dyn_shock V (hσc V)))
          (lowDeltaShocked.smear V) x.val a))
    (lopt_obj : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      IsMaxOn (fun a => lowDeltaShocked.toParams.joint_T_top_integrand
        (lowDeltaShocked.smear (lowDeltaShocked.V_T_dyn_shock V (hσc V)))
        (lowDeltaShocked.smear V) x.val a)
        Sanctions.I (lead V x.val))
    (h_obj_diff : ∀ (V W : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      |(lowDeltaShocked.toParams.joint_T_top_integrand
            (lowDeltaShocked.smear (lowDeltaShocked.V_T_dyn_shock V (hσc V)))
            (lowDeltaShocked.smear V) x.val (lead V x.val)
          - lowDeltaShocked.toParams.joint_T_top_integrand
            (lowDeltaShocked.smear (lowDeltaShocked.V_T_dyn_shock W (hσc W)))
            (lowDeltaShocked.smear W) x.val (lead V x.val))
        - (lowDeltaShocked.toParams.joint_T_top_integrand
            (lowDeltaShocked.smear (lowDeltaShocked.V_T_dyn_shock V (hσc V)))
            (lowDeltaShocked.smear V) x.val (lead W x.val)
          - lowDeltaShocked.toParams.joint_T_top_integrand
            (lowDeltaShocked.smear (lowDeltaShocked.V_T_dyn_shock W (hσc W)))
            (lowDeltaShocked.smear W) x.val (lead W x.val))|
        ≤ (((1115314143680 : ℝ) / 7762983835019) * dist V W)
            * |lead V x.val - lead W x.val|) :
    Nonempty lowDeltaShocked.ShockedFeedbackStackelbergEquilibriumTop := by
  refine lowDeltaShocked.shockedFeedbackStackelbergTop_interior_discharged_canonical
    lead lead_cont lead_mem (c_T := 2)
    (L_lead := 1115314143680 / 7762983835019) (L_Ua := 1)
    (by norm_num) (by norm_num) hσc sc lopt_obj h_obj_diff ?_ ?_
  · -- `hU_lip`: U_S is action-Lipschitz with constant 1 (∂U_S/∂a = 1 − s/2,
    -- |·| ≤ 1 on s ∈ [0,1]) — identical to P3, the payoff is unchanged.
    intro x a a' _ha _ha' s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hkey : lowDeltaShocked.toParams.U_S x.val a s
          - lowDeltaShocked.toParams.U_S x.val a' s = (a - a') * (1 - s / 2) := by
      simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S, mwU_S]; ring
    rw [hkey, abs_mul]
    have h2 : |1 - s / 2| ≤ 1 := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s / 2)]; linarith
    nlinarith [h2, abs_nonneg (a - a')]
  · -- `hmargin`: β_S + L_Ua·(2·L_lead/c_T) = 1/2 + L_lead < 1 at the
    -- certified chain value — the window certificate (C4) in action.
    have hβ : lowDeltaShocked.toParams.β_S = 1 / 2 := rfl
    rw [hβ]; norm_num
-/

/-! The exact window and chain equalities above remain witness diagnostics.
Any future low-adjustment equilibrium result must instantiate the symbolic
canonical coupled theorem with an optimal selector and derived local row and
carrier certificates; no numerical existence wrapper is retained here. -/

end Examples
end Sanctions
