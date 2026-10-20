/-
Sanctions/Examples/EpsilonIsolationWitness.lean

**Wave-6 P7: ε-isolation witness corollaries** — the parametric
ε-isolation layer (`Theory/Equilibrium/EpsilonIsolation.lean`)
instantiated at the two shipped Schur witnesses, with every margin
inequality discharged by `norm_num` on exact rationals.

## Plain-language statement

**The certified equilibria are locally isolated in value space**: no
distinct equilibrium with the same selector convention and the same
carrier shape exists within ε of the certified one in sup-norm.
Sup-norm ε-closeness discharges only the NORM component of
enlarged-carrier membership; the SHAPE pins (Sender Lipschitz bound,
Target monotonicity / slope windows) are carried as hypotheses on the
candidate equilibrium — irreducibly so, because an ε-amplitude
**sawtooth** added to the fixed point is ε-close in sup-norm yet
non-monotone with unbounded Lipschitz constant (probe exhibit: at
sup-distance `≤ 1/100` and tooth width `1/10000` the perturbed eeCert
Sender value has chord slope `16/3 − 200 < 0`). This is the scoped
Doraszelski–Escobar-style local regularity available WITHOUT
differentiability machinery; full genericity stays out of scope.

## What is delivered

1. **Coupled Schur witness at ε = 1** — ⚠ **the two capstones that consumed
   this chain (`coupledSchur_unique_in_carrier_wide`,
   `coupledSchur_epsilon_isolation`) were RETIRED on 2026-07-28 as vacuous
   conditionals**; see `coupledSchurWide_sc_T_contradictory` in §5. The
   *chain arithmetic* below is unaffected and remains valid — what was
   refuted is the modulus-`2` leader premise the capstones consumed, not the
   ε-shifted matrix or its margin. On 2026-10-06 (round BG3.9) the enlarged
   operator `coupledJointOpWide` and its reverse bridge were retired as well:
   their Target-invariance premise `h_invT` fails at the zero continuation
   pair (`coupledJointOpWide_h_invT_contradictory`, §5). The carriers are now
   defined symbolically as `valLipBall (coupledEpsMS 1) (coupledEpsKS 1)` and
   `{‖V‖ ≤ coupledEpsMT 1} ∩ monotone`; the evaluated forms
   `valLipBall (683/160) (73217/3200)` and `{‖V‖ ≤ 21} ∩ monotone` are
   recorded by `coupledCarrierS_wide_eq` / `coupledCarrierT_wide_eq`. They
   carry the ε-shifted row
   matrix `[[9/10, 9248/37717], [2880/37717, 60236226306669/107310302961626]]`
   whose Schur margin survives with slack
   `+26982804053357/1073103029616260 ≈ +0.0251` (vs `+0.026` at ε = 0
   — the enlargement consumes the slack quantifiably). Any shocked
   equilibrium within sup-distance 1 of the exact-carrier joint fixed
   point, carrying the two shape pins and the leader-selector
   coincidence, IS that fixed point. ε = 1 is the recommended build
   point: the Schur frontier is `ε* ≈ 24.8698` (the margin function
   `coupledEpsMargin` is positive at ε = 24 and negative at ε = 25,
   kernel-checked below), but the strong-rally ingredient of the
   still-open Target monotone-preservation discharge route dies at
   `ε_SR = 328853/174240 ≈ 1.8874`, so ε = 1 keeps that route alive
   (`coupledEpsSR_pos_at_one`).
2. **Decoupled eeCert witness** (`eeCert_epsilon_isolation`): the
   Schur margin is EXACTLY `1/20` and the cross constants are
   structurally zero, so the margin does not move at all under
   enlargement; the exact carriers already leave norm slack
   `80 − ‖V_T*‖ = 69` (Target) and `12 − ‖V_S*‖ = 1` (Sender), so the
   corollary holds at the LARGER radii `(ε_T, ε_S) = (69, 1)` — larger
   slack ⇒ larger ε — and, unlike the coupled witness, it is
   **unconditional**: every consumed ingredient (rows, invariance,
   fixed point, selector pin) is already proved in the tree.
3. **eeCert GLOBAL isolation bonus** (`eeCert_global_isolation`):
   at eeCert the policy pin is carrier-free, so defiance-policy
   coincidence `E.α ≡ 0` ALONE pins `V_S = (16x+17)/3` via the global
   `β_S = 1/2` contraction at the constant policy, and then
   `V_T = (82x+39)/11` via the global `β_T = 9/10` contraction at the
   pinned selector `σ ≡ 1` — **no proximity and no shape pins needed
   at all**. This is stronger than ε-isolation (the honest form of
   "the admissible ε at eeCert is unbounded") and consumes only
   existing proved machinery.

## Honest scope

* The coupled corollary consumes, at ε-shifted constants, exactly the
  SAME named analytic package as the shipped capstone
  `coupledSchur_unique_in_carrier` (see that file's header): the
  two-sided leader family (`lead`, `lead_cont`, `lead_mem`), selector
  continuity `hσc`, carrier-restricted strong concavities `sc_S`
  (modulus `c_S(1) = 37717/32000` on the WIDE Sender carrier) and
  `sc_T` (modulus 2), leader argmax `lopt` (Rule 1), the two-sided
  channel-split objective-difference regularity `h_obj_diff` at the
  ε = 1 split constants `(2880/37717, 3290537412928/53655151480813)`,
  and carrier invariance `h_invT`/`h_invS` at the WIDE carriers (norm
  invariance is elementary — `M + β·ε < M + ε`; the monotone/K'-
  Lipschitz image preservation is the same recorded inherited gap as
  at ε = 0). **No new assumption KIND anywhere — the same named shapes
  at shifted constants (Rule 3 clean).** Since 2026-10-06 the Target
  half `h_invT` is known to be false at the WIDE carriers too
  (`coupledJointOpWide_h_invT_contradictory`): the monotone pin fails
  for the Bellman image of the zero continuation pair, so the "inherited
  gap" is a refutation, not an open discharge item.
* The pin hypotheses on the candidate equilibrium are irreducible at
  this layer (sawtooth exhibit); the pin-free bootstrap would need
  invariance quantified over bare norm balls — a strictly wider
  hypothesis shape (Rule-3 stop, deliberately not taken).
* Everything numeric — enlarged chain constants, both Schur margins,
  the frontier bracket, the strong-rally cap — is discharged by
  `norm_num` on exact rationals.

Probe/verify scripts: `docs/archive/workflow-scratch/w6_p7_coupled_eps.py`,
`docs/archive/workflow-scratch/w6_p7_eecert_eps.py`, `docs/archive/workflow-scratch/w6_verify_P7-isolation_*.py`
(all green, exact `Fraction` arithmetic).
-/

import Sanctions.Theory.Equilibrium.EpsilonIsolation
import Sanctions.Foundations.ArgmaxSensitivity
import Sanctions.Examples.CoupledRoute.CoupledSchurWitness
import Sanctions.Examples.FourGroupPlannerWitness

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction
open scoped NNReal

noncomputable section

namespace Examples

open AbstractGame Sanctions.AbstractGame.Params

/-! ## §1 The ε-enlarged coupled chain as exact rational functions of ε

The `EpsilonChain` closed forms (`Theory/Equilibrium/EpsilonIsolation`)
instantiated at the low-δ window economy's primitive constants
(`β_S = 1/2`, `β_T = 9/10`, `δ = 1/100`, `h = 1/10`, `L_Ux = 7/4`,
`L_UT = L_Ua = 1`, `c_T = 2`, `|∂²U_S/∂s∂a| = 1/2`, stage-modulus
intercept `6/5`, smear-curvature fall rate `1/200`), at common
enlargement ε of both norm radii. The `L_leadS` split constants
`T1/T2S/T3` are the witness-level closed forms of the W3 chain (the
Lean tree consumes `L_leadS` through the pinned `h_obj_diff`
hypothesis; the chain provenance is the adversarially-verified probe
algebra). -/

/-- Enlarged Sender norm radius `M_S'(ε) = 523/160 + ε`. -/
def coupledEpsMS (ε : ℝ) : ℝ := 523 / 160 + ε

/-- Enlarged Target norm radius `M_T'(ε) = 20 + ε`. -/
def coupledEpsMT (ε : ℝ) : ℝ := 20 + ε

/-- Enlarged Sender Lipschitz constant `K'(ε) = L_Ux + β_S·(M_S'/h)·(1−δ)`. -/
def coupledEpsKS (ε : ℝ) : ℝ :=
  EpsilonChain.KS (7 / 4) (1 / 2) (1 / 10) (1 / 100) (coupledEpsMS ε)

/-- Enlarged smeared concavity modulus `c_S(ε) = 6/5 − M_S'(ε)/200`. -/
def coupledEpsCS (ε : ℝ) : ℝ :=
  EpsilonChain.cS (6 / 5) (1 / 200) (coupledEpsMS ε)

/-- Enlarged selector Lipschitz constant `Lσ(ε) = (1/10)/c_S(ε)`. -/
def coupledEpsLσ (ε : ℝ) : ℝ :=
  EpsilonChain.Lσ (1 / 2) (1 / 10) (1 / 100) (coupledEpsCS ε)

/-- Enlarged Target-row factor `G(ε) = 1 + β_T·(M_T'/h)·δ = 14/5 + (9/100)ε`. -/
def coupledEpsG (ε : ℝ) : ℝ :=
  EpsilonChain.G 1 (9 / 10) (1 / 10) (1 / 100) (coupledEpsMT ε)

/-- Enlarged Target-row cross constant `L_TS(ε) = G(ε)·Lσ(ε)`. -/
def coupledEpsLTS (ε : ℝ) : ℝ :=
  EpsilonChain.L_TS 1 (9 / 10) (1 / 2) (1 / 10) (1 / 100) (coupledEpsMT ε)
    (coupledEpsCS ε)

/-- Enlarged Sender-row cross constant
`L_ST(ε) = L_Ua·(2/c_T)·κ_a(ε)·β_T·δ·(1/h) = (9/100)/c_S(ε)`
(robust factor-2 argmax-core convention). -/
def coupledEpsLST (ε : ℝ) : ℝ :=
  EpsilonChain.L_ST 1 2 (1 / 2) (9 / 10) (1 / 10) (1 / 100) (coupledEpsCS ε)

/-- `T1(ε) = (1/20)/c_S(ε)` — the direct selector term of the leader
objective-difference chain. -/
def coupledEpsT1 (ε : ℝ) : ℝ := (1 / 20) / coupledEpsCS ε

/-- `T2S(ε) = (9/10000)·M_T'(ε)/c_S(ε)²` — the continuation-radius term. -/
def coupledEpsT2S (ε : ℝ) : ℝ :=
  (9 / 10000) * coupledEpsMT ε / (coupledEpsCS ε) ^ 2

/-- `T3(ε) = G(ε)·(1/400)·(1 + K'(ε)·Lσ(ε)/100)/c_S(ε)²` — the
selector-composition term. -/
def coupledEpsT3 (ε : ℝ) : ℝ :=
  coupledEpsG ε * (1 / 400) * (1 + coupledEpsKS ε * coupledEpsLσ ε / 100)
    / (coupledEpsCS ε) ^ 2

/-- Enlarged leader-Lipschitz Sender channel `L_leadS(ε) = T1 + T2S + T3`. -/
def coupledEpsLleadS (ε : ℝ) : ℝ :=
  coupledEpsT1 ε + coupledEpsT2S ε + coupledEpsT3 ε

/-- Enlarged Sender-row diagonal `b_S(ε) = β_S + L_Ua·(2/c_T)·L_leadS(ε)
= 1/2 + L_leadS(ε)`. -/
def coupledEpsBS (ε : ℝ) : ℝ := 1 / 2 + coupledEpsLleadS ε

/-- **The enlarged Schur margin `m(ε)`** of the ε-shifted row matrix
`[[β_T, L_TS(ε)], [L_ST(ε), b_S(ε)]]`. Margin survival at enlargement
ε is the explicit inequality `0 < coupledEpsMargin ε`. -/
def coupledEpsMargin (ε : ℝ) : ℝ :=
  EpsilonChain.schurMargin (9 / 10) (coupledEpsBS ε) (coupledEpsLTS ε)
    (coupledEpsLST ε)

/-- **Strong-rally guard `SR(ε) = 27/20 − (99/2000)·K'(ε)`** — the margin
of the sketched discharge route for the (hypothesized) Target monotone
preservation; it dies at `ε_SR = 328853/174240 ≈ 1.8874`, which is why
the witness corollary is built at ε = 1. -/
def coupledEpsSR (ε : ℝ) : ℝ := 27 / 20 - (99 / 2000) * coupledEpsKS ε

/-! ### ε = 0 anchors: the chain reproduces the shipped W3 constants -/

/-- At ε = 0 the chain reproduces every shipped W3 constant:
`K' = 57377/3200` (`lowDelta_chain_KS`), `c_S = 37877/32000` (window
C3), `L_TS = 1280/5411`, `L_ST = 2880/37877`,
`b_S = 8697049946379/15525967670038`, margin
`= 4036322267659/155259676700380 ≈ +0.026`
(`coupledSchur_margin_robust_exact`). -/
theorem coupledEps_anchors_at_zero :
    coupledEpsKS 0 = 57377 / 3200 ∧ coupledEpsCS 0 = 37877 / 32000
      ∧ coupledEpsLTS 0 = 1280 / 5411 ∧ coupledEpsLST 0 = 2880 / 37877
      ∧ coupledEpsBS 0 = 8697049946379 / 15525967670038
      ∧ coupledEpsMargin 0 = 4036322267659 / 155259676700380 := by
  simp only [coupledEpsKS, coupledEpsCS, coupledEpsLTS, coupledEpsLST,
    coupledEpsBS, coupledEpsMargin, coupledEpsLleadS, coupledEpsT1,
    coupledEpsT2S, coupledEpsT3, coupledEpsG, coupledEpsLσ, coupledEpsMS,
    coupledEpsMT, EpsilonChain.KS, EpsilonChain.cS, EpsilonChain.Lσ,
    EpsilonChain.G, EpsilonChain.L_TS, EpsilonChain.L_ST, EpsilonChain.κa,
    EpsilonChain.schurMargin]
  norm_num

/-! ### ε = 1 (the build point): exact shifted constants and margin survival -/

/-- At ε = 1: `K' = 73217/3200`, `c_S = 37717/32000`,
`L_TS = 9248/37717`, `L_ST = 2880/37717`,
`b_S = 60236226306669/107310302961626`. -/
theorem coupledEps_anchors_at_one :
    coupledEpsKS 1 = 73217 / 3200 ∧ coupledEpsCS 1 = 37717 / 32000
      ∧ coupledEpsLTS 1 = 9248 / 37717 ∧ coupledEpsLST 1 = 2880 / 37717
      ∧ coupledEpsBS 1 = 60236226306669 / 107310302961626 := by
  simp only [coupledEpsKS, coupledEpsCS, coupledEpsLTS, coupledEpsLST,
    coupledEpsBS, coupledEpsLleadS, coupledEpsT1, coupledEpsT2S,
    coupledEpsT3, coupledEpsG, coupledEpsLσ, coupledEpsMS, coupledEpsMT,
    EpsilonChain.KS, EpsilonChain.cS, EpsilonChain.Lσ, EpsilonChain.G,
    EpsilonChain.L_TS, EpsilonChain.L_ST, EpsilonChain.κa]
  norm_num

/-- **Margin survival at the shipped enlargement ε = 1** — the exact
enlarged Schur slack is `26982804053357/1073103029616260 ≈ +0.0251448`
(barely below the ε = 0 slack `≈ +0.026`: one unit of sup-norm
enlargement costs `≈ 0.00085` of margin). -/
theorem coupledEpsMargin_at_one :
    coupledEpsMargin 1 = 26982804053357 / 1073103029616260 := by
  simp only [coupledEpsMargin, coupledEpsBS, coupledEpsLleadS, coupledEpsT1,
    coupledEpsT2S, coupledEpsT3, coupledEpsG, coupledEpsLσ, coupledEpsKS,
    coupledEpsCS, coupledEpsLTS, coupledEpsLST, coupledEpsMS, coupledEpsMT,
    EpsilonChain.KS, EpsilonChain.cS, EpsilonChain.Lσ, EpsilonChain.G,
    EpsilonChain.L_TS, EpsilonChain.L_ST, EpsilonChain.κa,
    EpsilonChain.schurMargin]
  norm_num

/-- Margin survival at ε = 1, as the positivity the isolation theorem
consumes. -/
theorem coupledEpsMargin_pos_at_one : 0 < coupledEpsMargin 1 := by
  rw [coupledEpsMargin_at_one]; norm_num

/-- **The Schur frontier lies in (24, 25)**: the margin is still positive
at ε = 24 and negative at ε = 25 — the kernel-checked bracket for the
largest admissible enlargement `ε* ≈ 24.8698` (the unique positive root
of the exact frontier cubic `m(ε)·c_S(ε)³`; probe algebra). The witness
is nevertheless built at ε = 1, capped by the strong-rally guard below,
not by Schur. -/
theorem coupledEpsMargin_frontier_bracket :
    0 < coupledEpsMargin 24 ∧ coupledEpsMargin 25 < 0 := by
  constructor <;>
  · simp only [coupledEpsMargin, coupledEpsBS, coupledEpsLleadS,
      coupledEpsT1, coupledEpsT2S, coupledEpsT3, coupledEpsG, coupledEpsLσ,
      coupledEpsKS, coupledEpsCS, coupledEpsLTS, coupledEpsLST,
      coupledEpsMS, coupledEpsMT, EpsilonChain.KS, EpsilonChain.cS,
      EpsilonChain.Lσ, EpsilonChain.G, EpsilonChain.L_TS, EpsilonChain.L_ST,
      EpsilonChain.κa, EpsilonChain.schurMargin]
    norm_num

/-- **The strong-rally guard**: `SR(0) = 2959677/6400000 ≈ +0.4625`,
`SR(1) = 1391517/6400000 ≈ +0.2174 > 0` (the ε = 1 build point keeps
the future monotone-preservation discharge route alive), and the route
dies exactly at `ε_SR = 328853/174240 ≈ 1.8874`. -/
theorem coupledEpsSR_pos_at_one :
    coupledEpsSR 0 = 2959677 / 6400000 ∧ 0 < coupledEpsSR 1
      ∧ coupledEpsSR (328853 / 174240) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [coupledEpsSR, coupledEpsKS, coupledEpsMS, EpsilonChain.KS]
    norm_num

/-! ## §2 The ε = 1 enlarged coupled carriers -/

/-- **The ε = 1 enlarged Target carrier**: sup-ball of radius
`21 = M_T + 1` intersected with the SAME monotone pin (the shape pin is
unchanged by enlargement — it is a shape, not a radius). -/
def coupledCarrierT_wide : Set SBCF :=
  {V : SBCF | ‖V‖ ≤ coupledEpsMT 1} ∩
    {V : SBCF | LowerSlopeOnValueOn V (Set.Icc (0 : ℝ) 1) 0}

/-- **The ε = 1 enlarged Sender carrier**: the Lipschitz ball at the
enlarged radius `683/160 = M_S + 1` and the self-consistent enlarged
Lipschitz constant `K'(1) = 73217/3200` (the chain formula
`L_Ux + β_S·(M_S'/h)·(1−δ)` at `M_S' = 683/160`, `coupledEpsKS 1`). -/
def coupledCarrierS_wide : Set SBCF :=
  valLipBall (coupledEpsMS 1) (coupledEpsKS 1)

/-! ### ε = 1 evaluation bridges

The three radii above are **derived**, not chosen: `M_S'(1) = M_S + 1`,
`M_T'(1) = M_T + 1`, and `K'(1)` is the chain formula
`L_Ux + β_S·(M_S'/h)·(1−δ)` evaluated at `M_S'(1)`.  The bridges below
record their evaluated rational form so downstream `norm_num` proofs are
unaffected, while the carrier *definitions* stay symbolic in the chain.
Changing a witness primitive now propagates through `coupledEps*` instead
of requiring every inlined literal to be recomputed by hand. -/

/-- Bridge: the ε = 1 Target norm radius evaluates to `21`. -/
theorem coupledEpsMT_one : coupledEpsMT 1 = 21 := by
  norm_num [coupledEpsMT]

/-- Bridge: the ε = 1 Sender norm radius evaluates to `683/160`. -/
theorem coupledEpsMS_one : coupledEpsMS 1 = 683 / 160 := by
  norm_num [coupledEpsMS]

/-- Bridge: the ε = 1 Sender Lipschitz constant evaluates to `73217/3200`. -/
theorem coupledEpsKS_one : coupledEpsKS 1 = 73217 / 3200 :=
  coupledEps_anchors_at_one.1

/-- The enlarged Sender carrier in its previous inlined-rational form.
Definitional-equality bridge: no hypothesis or conclusion moves. -/
theorem coupledCarrierS_wide_eq :
    coupledCarrierS_wide = valLipBall (683 / 160) (73217 / 3200) := by
  unfold coupledCarrierS_wide
  rw [coupledEpsMS_one, coupledEpsKS_one]

/-- The enlarged Target carrier in its previous inlined-rational form. -/
theorem coupledCarrierT_wide_eq :
    coupledCarrierT_wide =
      {V : SBCF | ‖V‖ ≤ 21} ∩
        {V : SBCF | LowerSlopeOnValueOn V (Set.Icc (0 : ℝ) 1) 0} := by
  unfold coupledCarrierT_wide
  rw [coupledEpsMT_one]

/-- The enlarged Target carrier is closed. -/
theorem coupledCarrierT_wide_isClosed : IsClosed coupledCarrierT_wide :=
  (isClosed_le continuous_norm continuous_const).inter
    (lowerSlopeOnValueOn_isClosed (Set.Icc (0 : ℝ) 1) 0)

/-- The enlarged Sender carrier is closed. -/
theorem coupledCarrierS_wide_isClosed : IsClosed coupledCarrierS_wide :=
  valLipBall_isClosed _ _

/-- The exact Target carrier embeds in the enlarged one. -/
theorem coupledCarrierT_subset_wide :
    coupledCarrierT ⊆ coupledCarrierT_wide :=
  fun _ hV => ⟨le_trans
    (by simpa only [lowDeltaTargetCarrierNorm_eq] using hV.1)
    (by norm_num [coupledEpsMT] : (20 : ℝ) ≤ coupledEpsMT 1), hV.2⟩

/-- The exact Sender carrier embeds in the enlarged one (norm radius up,
Lipschitz constant up: `57377/3200 ≤ 73217/3200`). -/
theorem coupledCarrierS_subset_wide :
    coupledCarrierS ⊆ coupledCarrierS_wide :=
  fun _ hV => ⟨le_trans
    (by simpa only [lowDeltaSenderCarrierNorm_eq] using hV.1)
    (by norm_num [coupledEpsMS] : (523 / 160 : ℝ) ≤ coupledEpsMS 1),
    hV.2.mono_constant
      (by rw [lowDeltaSenderCarrierLip_eq, coupledEpsKS_one]; norm_num)⟩

/-- The enlarged Target carrier is nonempty. -/
theorem coupledCarrierT_wide_nonempty : coupledCarrierT_wide.Nonempty :=
  coupledCarrierT_nonempty.imp fun _ hV => coupledCarrierT_subset_wide hV

/-- The enlarged Sender carrier is nonempty. -/
theorem coupledCarrierS_wide_nonempty : coupledCarrierS_wide.Nonempty :=
  coupledCarrierS_nonempty.imp fun _ hV => coupledCarrierS_subset_wide hV

/-! ## §3 The ε = 1 row-Lipschitz bounds (shifted chain constants)

Mirrors §5 of `CoupledSchurWitness.lean` at the ε = 1 constants: the
Target-carrier norm `21` raises the smear creation bound to
`L_smVT = 210` and the factor `G` to `289/100`; the Sender-carrier norm
`683/160` lowers the certified smeared concavity to
`c_S(1) = 37717/32000`, raising `Lσ` to `3200/37717`. Same consumed
hypothesis shapes as at ε = 0, at the shifted constants. -/

/-- **Enlarged Target ROW at ε = 1 — cross constant
`L_TS(1) = 9248/37717`.** Same derivation as `coupled_L_TS` with the
enlarged constants `L_smVT = 210` (from `‖V_T'‖ ≤ 21`) and
`Lσ = 3200/37717` (from the enlarged-carrier concavity modulus
`37717/32000`): `(1 + (9/10)·210·(1/100))·(3200/37717)
= (289/100)·(3200/37717) = 9248/37717`. -/
theorem coupled_L_TS_wide
    (V_T V_T' V_S W_S : SBCF) (hV_T'_norm : ‖V_T'‖ ≤ 21)
    (hσcV : Continuous (fun xa : ℝ × ℝ =>
      lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) xa.1 xa.2))
    (hσcW : Continuous (fun xa : ℝ × ℝ =>
      lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear W_S) xa.1 xa.2))
    (sc_V : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
      StrongConcaveOn Sanctions.I (37717 / 32000)
        (fun s => lowDeltaShocked.toParams.U_S x a s
          + lowDeltaShocked.toParams.β_S
            * (lowDeltaShocked.smear V_S)
              (Sanctions.clipS' (lowDeltaShocked.toParams.F x s))))
    (sc_W : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
      StrongConcaveOn Sanctions.I (37717 / 32000)
        (fun s => lowDeltaShocked.toParams.U_S x a s
          + lowDeltaShocked.toParams.β_S
            * (lowDeltaShocked.smear W_S)
              (Sanctions.clipS' (lowDeltaShocked.toParams.F x s)))) :
    dist (lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S)) hσcV V_T)
      (lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear W_S)) hσcW V_T')
      ≤ (9 / 10) * dist V_T V_T' + (9248 / 37717) * dist V_S W_S := by
  -- σ-Lipschitz in `V_S` at the enlarged `Lσ = 3200/37717`.
  have hσ_lip : ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
      |lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) x a
        - lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear W_S) x a|
        ≤ (3200 / 37717) * dist V_S W_S := by
    intro x hx a ha
    have h := Sanctions.AbstractGame.Params.sigma_top_lipschitz_in_V_pair
      (p := lowDeltaShocked.toParams) lowDeltaShocked.smear
      (Lκ := 10) (by norm_num)
      (AbstractGame.movAvgShockedParams_smear_sub lowDeltaParams lowDeltaH_pos)
      lowDelta_smear_creation_lip
      (c := 37717 / 32000) (by norm_num) x a V_S W_S
      (sc_V x hx a ha) (sc_W x hx a ha)
      (LF := 1 / 100) (by norm_num) (fun s s' => lowDelta_clipF_lip x s s')
    have hβ : lowDeltaShocked.toParams.β_S = 1 / 2 := rfl
    rw [hβ] at h
    linarith [h]
  -- Smear creation bound at the enlarged Target norm: `L_smVT = 210`.
  have hsmVT_lip : ∀ z z' : ↥(Sanctions.S : Set ℝ),
      |lowDeltaShocked.smear V_T' z - lowDeltaShocked.smear V_T' z'|
        ≤ 210 * dist z z' := by
    intro z z'
    have h := lowDelta_smear_creation_lip V_T' z z'
    have h2 : 10 * ‖V_T'‖ * dist z z' ≤ 210 * dist z z' := by
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      linarith
    exact le_trans h h2
  have h := lowDeltaShocked.targetDynBCF_shock_row_lipschitz_box
    (Lσ := 3200 / 37717) (L_UT := 1) (L_smVT := 210) (LF := 1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    V_T V_T' V_S W_S
    (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S))
    (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear W_S))
    hσcV hσcW
    (fun x _hx a _ha =>
      lowDeltaShocked.toParams.σ_dyn_top_mem_I (lowDeltaShocked.smear V_S) x a)
    (fun x _hx a _ha =>
      lowDeltaShocked.toParams.σ_dyn_top_mem_I (lowDeltaShocked.smear W_S) x a)
    hσ_lip lowDelta_UT_action_lip hsmVT_lip
    (fun x s s' => lowDelta_clipF_lip x s s')
  have hβ : lowDeltaShocked.toParams.β_T = 9 / 10 := rfl
  rw [hβ] at h
  linarith [h]

/-- **Enlarged two-sided leader-policy Lipschitz bound at the ε = 1
split constants** `(L_leadT, L_leadS) = (2880/37717,
3290537412928/53655151480813)` — same argmax-core wiring as
`coupled_lead_lipschitz`, `c_T = 2`. -/
theorem coupled_lead_lipschitz_wide
    (lead : SBCF → SBCF → ℝ → ℝ)
    (V_T V_S V_T' W_S : SBCF) (x : ↥(Sanctions.S : Set ℝ))
    (scV : StrongConcaveOn Sanctions.I 2
      (fun a => coupledLeaderObj V_T V_S x.val a))
    (scW : StrongConcaveOn Sanctions.I 2
      (fun a => coupledLeaderObj V_T' W_S x.val a))
    (hmemV : lead V_T V_S x.val ∈ Sanctions.I)
    (hmemW : lead V_T' W_S x.val ∈ Sanctions.I)
    (loptV : IsMaxOn (fun a => coupledLeaderObj V_T V_S x.val a)
      Sanctions.I (lead V_T V_S x.val))
    (loptW : IsMaxOn (fun a => coupledLeaderObj V_T' W_S x.val a)
      Sanctions.I (lead V_T' W_S x.val))
    (hod : |(coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T V_S x.val))
        - (coupledLeaderObj V_T V_S x.val (lead V_T' W_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T' W_S x.val))|
        ≤ ((2880 / 37717) * dist V_T V_T'
            + (3290537412928 / 53655151480813) * dist V_S W_S)
          * |lead V_T V_S x.val - lead V_T' W_S x.val|) :
    |lead V_T V_S x.val - lead V_T' W_S x.val|
      ≤ (2880 / 37717) * dist V_T V_T'
        + (3290537412928 / 53655151480813) * dist V_S W_S := by
  have h := Sanctions.argmax_lipschitz_two_coordinates_of_strongConcave
    (objective := fun V W a => coupledLeaderObj V W x.val a)
    (select := fun V W => lead V W x.val)
    (A := Sanctions.I) (c := 2)
    (Lx := 2880 / 37717) (Ly := 3290537412928 / 53655151480813)
    (by norm_num) (by norm_num) (by norm_num)
    (convex_Icc 0 1) V_T V_T' V_S W_S
    scV scW hmemV hmemW loptV loptW hod
  linarith [h]

/-- **Enlarged Sender ROW at ε = 1 — cross constant
`L_ST(1) = 2880/37717`, diagonal `b_S(1) = 1/2 + L_leadS(1)
= 60236226306669/107310302961626`.** Same value/policy channel split as
`coupled_L_ST` at the shifted constants. -/
theorem coupled_L_ST_wide
    (α₁ α₂ : ℝ → ℝ) (hα₁ : Continuous α₁) (hα₂ : Continuous α₂)
    (V_T V_S V_T' W_S : SBCF)
    (hpol : ∀ x : ↥(Sanctions.S : Set ℝ), |α₁ x.val - α₂ x.val|
      ≤ (2880 / 37717) * dist V_T V_T'
        + (3290537412928 / 53655151480813) * dist V_S W_S) :
    dist (lowDeltaShocked.bellmanS_shock α₁ hα₁ V_S)
      (lowDeltaShocked.bellmanS_shock α₂ hα₂ W_S)
      ≤ (2880 / 37717) * dist V_T V_T'
        + (60236226306669 / 107310302961626) * dist V_S W_S := by
  have hC0 : (0 : ℝ) ≤ (2880 / 37717) * dist V_T V_T'
      + (60236226306669 / 107310302961626) * dist V_S W_S := by
    have h1 := dist_nonneg (x := V_T) (y := V_T')
    have h2 := dist_nonneg (x := V_S) (y := W_S)
    positivity
  rw [BoundedContinuousFunction.dist_le hC0]
  intro x
  -- value channel at the fixed policy α₁
  have h1 : dist (lowDeltaShocked.bellmanS_shock α₁ hα₁ V_S x)
      (lowDeltaShocked.bellmanS_shock α₁ hα₁ W_S x)
      ≤ (1 / 2) * dist V_S W_S := by
    have h := lowDeltaShocked.bellmanS_shock_pointwise_dist hα₁ V_S W_S x
    have hβ : lowDeltaShocked.toParams.β_S = 1 / 2 := rfl
    rwa [hβ] at h
  -- policy channel at the fixed value W_S
  have h2 : dist (lowDeltaShocked.bellmanS_shock α₁ hα₁ W_S x)
      (lowDeltaShocked.bellmanS_shock α₂ hα₂ W_S x)
      ≤ |α₁ x.val - α₂ x.val| := by
    rw [Real.dist_eq]
    refine lowDeltaShocked.toParams.bellmanS_BCF_policy_pointwise_dist α₁ α₂
      hα₁ hα₂ (lowDeltaShocked.smear W_S) x _ ?_
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hkey : lowDeltaShocked.toParams.U_S x.val (α₁ x.val) s
        - lowDeltaShocked.toParams.U_S x.val (α₂ x.val) s
        = (α₁ x.val - α₂ x.val) * (1 - s / 2) := by
      simp only [lowDeltaShocked_toParams, lowDeltaParams_U_S, mwU_S]; ring
    rw [hkey, abs_mul]
    have habs : |1 - s / 2| ≤ 1 := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s / 2)]; linarith
    nlinarith [habs, abs_nonneg (α₁ x.val - α₂ x.val)]
  have h3 := hpol x
  have htri := dist_triangle (lowDeltaShocked.bellmanS_shock α₁ hα₁ V_S x)
    (lowDeltaShocked.bellmanS_shock α₁ hα₁ W_S x)
    (lowDeltaShocked.bellmanS_shock α₂ hα₂ W_S x)
  linarith [h1, h2, h3, htri]

/-! ## §4 The enlarged Schur margin at ε = 1 (norm_num, exact) -/

/-- **Margin survival at ε = 1** — the load-bearing enlarged Schur
inequality: `L_TS(1)·L_ST(1) < (1 − β_T)·(1 − b_S(1))`. -/
theorem coupledSchur_margin_wide :
    (9248 / 37717 : ℝ) * (2880 / 37717)
      < (1 - 9 / 10) * (1 - 60236226306669 / 107310302961626) := by
  norm_num

/-- Exact enlarged Schur slack at ε = 1:
`+26982804053357/1073103029616260 ≈ +0.0251448` (the ε = 0 slack
`+4036322267659/155259676700380 ≈ +0.026` minus the quantified
enlargement cost). -/
theorem coupledSchur_margin_wide_exact :
    (1 - (9 : ℝ) / 10) * (1 - 60236226306669 / 107310302961626)
        - (9248 / 37717) * (2880 / 37717)
      = 26982804053357 / 1073103029616260 := by
  norm_num

/-! ## §5 The enlarged joint operator, Perov uniqueness, reverse bridge

Since 2026-10-06 (round BG3.9) only the two refutations below are live: the
enlarged operator `coupledJointOpWide`, its row bounds, its Perov uniqueness
and its reverse bridge are commented audit evidence in the retirement block
that follows them. -/

/-- **The modulus-`2` leader strong-concavity premise is CONTRADICTORY on the
enlarged carriers.**

`not_coupledLeaderStrongConcave` refutes the modulus-`2` package on
`coupledCarrierT × coupledCarrierS`.  Enlarging the carriers cannot rescue it:
the refuting continuation pair `(0, 0)` at state `5/12` lies in the smaller
carriers, hence in the enlarged ones by `coupledCarrierT_subset_wide` and
`coupledCarrierS_subset_wide`.  Consequently every declaration consuming this
premise is a **vacuous conditional** (Rule 11.3 / 12.2): its statement is true
and its `#print axioms` scan is clean, but it asserts nothing about the model.

The proof is purely structural — it transports the existing refutation along
the two carrier inclusions.  No arithmetic is involved, and none is possible:
the defect is in the shape of the hypothesis, not in the size of a constant. -/
theorem coupledSchurWide_sc_T_contradictory
    (sc_T : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      StrongConcaveOn Sanctions.I 2
        (fun a => coupledLeaderObj V_T V_S x.val a)) : False :=
  not_coupledLeaderStrongConcave fun V_T hT V_S hS x =>
    sc_T V_T (coupledCarrierT_subset_wide hT) V_S
      (coupledCarrierS_subset_wide hS) x

/-- **The enlarged Target-carrier invariance premise is CONTRADICTORY
(round BG3.9, 2026-10-06).**

`coupledJointOpWide` and every declaration stated over it take the premise
`h_invT`: the shocked Target Bellman row, at the greatest Sender selector
`σ_dyn_top (smear V_S)`, maps every pair of the ε = 1 enlarged carriers back
into the enlarged Target carrier. That premise is false. The zero continuation
pair `(0, 0)` lies in both enlarged carriers (`coupledCarrierT_subset_wide`,
`coupledCarrierS_subset_wide`), and on physical states the unclamped selector
agrees with the clamped one, so the Bellman image is the one computed in
`CoupledSchurWitness.lean`: value `0` at state `0` and `-7/600` at state
`1/10`. The image therefore decreases, while the enlarged Target carrier keeps
the same nondecreasing-value pin as the exact one. Enlarging the norm radius
does not help, because the failure is in the shape pin, not the radius.

Plain language: with zero continuation values, the Target's best-response
value falls between states `0` and `1/10` once the Sender's endogenous
response is taken into account, so a Target carrier that contains the zero
pair and keeps the nondecreasing-value pin cannot be invariant under this row.
Any statement that consumes `h_invT` is a vacuous conditional.
The continuity premise `hσc` is carried only because `h_invT` mentions it.
Rule 22: witness-specific (the low-δ economy), not a general-`F` statement. -/
theorem coupledJointOpWide_h_invT_contradictory
    (hσc : ∀ V_S : SBCF, Continuous (fun xa : ℝ × ℝ =>
      lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) xa.1 xa.2))
    (h_invT : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S))
        (hσc V_S) V_T ∈ coupledCarrierT_wide) : False := by
  have hmem := h_invT 0 (coupledCarrierT_subset_wide zero_mem_coupledCarrierT)
    0 (coupledCarrierS_subset_wide zero_mem_coupledCarrierS)
  -- On physical states the unclamped and clamped selectors agree, so the
  -- enlarged image coincides there with the exact zero-pair image.
  have hpt : ∀ x : ↥(Sanctions.S : Set ℝ),
      lowDeltaShocked.targetDynBCF_shock
          (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear (0 : SBCF)))
          (hσc 0) (0 : SBCF) x
        = lowDeltaShocked.targetDynBCF_shock
          (lowDeltaShocked.toParams.σ_dyn_top_clamped
            (lowDeltaShocked.smear (0 : SBCF)))
          (coupled_sigmaDynTop_clamped_continuous 0 zero_mem_coupledCarrierS)
          (0 : SBCF) x := by
    intro x
    change sSup ((fun a => lowDeltaShocked.toParams.targetDynIntegrand
        (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear (0 : SBCF)))
        (lowDeltaShocked.smear (0 : SBCF)) x.val a) '' Sanctions.I)
      = sSup ((fun a => lowDeltaShocked.toParams.targetDynIntegrand
        (lowDeltaShocked.toParams.σ_dyn_top_clamped
          (lowDeltaShocked.smear (0 : SBCF)))
        (lowDeltaShocked.smear (0 : SBCF)) x.val a) '' Sanctions.I)
    simp only [AbstractGame.Params.targetDynIntegrand,
      lowDeltaShocked.toParams.σ_dyn_top_clamped_eq_of_mem
        (lowDeltaShocked.smear (0 : SBCF)) x.property]
  have hmono := hmem.2
    (⟨0, by norm_num⟩ : ↥(Sanctions.S : Set ℝ))
    (⟨1 / 10, by norm_num⟩ : ↥(Sanctions.S : Set ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  rw [hpt, hpt, coupledZeroPair_target_bellman_zero,
    coupledZeroPair_target_bellman_one_tenth] at hmono
  norm_num at hmono

/- **Retired vacuous ε = 1 conditionals (2026-07-28).**

`coupledJointOpWide_rows`, `coupledSchur_unique_in_carrier_wide`, and
`coupledSchur_epsilon_isolation` each consume the `sc_T` premise proved
contradictory immediately above, so each is a vacuous conditional.  They are
kept below as commented audit evidence and no longer enter the Lean
environment — the same disposition applied on 2026-07-27 to the numerical
wrappers in `CoupledSchurWitness.lean` and `LowDeltaWindowWitness.lean`, and
on 2026-07-24 to the §9 canonical layer, which failed for this identical
reason.  These three survived those sweeps because they inline the modulus-`2`
statement rather than referencing the named `CoupledLeaderStrongConcave`
abbreviation, so a name-based scan did not reach them.

Reinstating any of them requires a replacement leader premise that survives
its own Rule-11 refutation gate.  The modulus-`2` package does not.  The
weaker realised-policy inequality `(1/2)·(a − lead)^2 ≤ J(lead) − J(a)`
recorded in `ASSUMPTION-SURFACE-REGISTER.md` is the natural candidate, but it
has **not** been gated on these enlarged carriers and must not be assumed to
survive here.

2026-10-06 (round BG3.9): the enlarged operator `coupledJointOpWide` (first
below) and its reverse bridge `coupledJointOpWide_fixed_of_equilibrium` (last
below) joined this block. Neither consumes `sc_T`, but both take the
Target-invariance premise `h_invT`, which
`coupledJointOpWide_h_invT_contradictory` above proves false at the zero
continuation pair. Every statement about the operator is therefore a vacuous
conditional, and its remaining consumers were already retired here and in §6.
Reinstatement needs a Target carrier that its own Bellman row preserves.

/-- **The joint two-sided shocked Bellman operator on the ε = 1 enlarged
carrier product** — same coordinates as `coupledJointOp`, on the wide
carriers (invariance at the wide carriers consumed: `h_invT`, `h_invS`,
the same accepted hypothesis shape at shifted constants). -/
def coupledJointOpWide
    (lead : SBCF → SBCF → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S : SBCF, Continuous (lead V_T V_S))
    (hσc : ∀ V_S : SBCF, Continuous (fun xa : ℝ × ℝ =>
      lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) xa.1 xa.2))
    (h_invT : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S))
        (hσc V_S) V_T ∈ coupledCarrierT_wide)
    (h_invS : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      lowDeltaShocked.bellmanS_shock (lead V_T V_S) (lead_cont V_T V_S) V_S
        ∈ coupledCarrierS_wide)
    (z : ↥coupledCarrierT_wide × ↥coupledCarrierS_wide) :
    ↥coupledCarrierT_wide × ↥coupledCarrierS_wide :=
  (⟨lowDeltaShocked.targetDynBCF_shock
      (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear z.2.val))
      (hσc z.2.val) z.1.val,
    h_invT z.1.val z.1.property z.2.val z.2.property⟩,
   ⟨lowDeltaShocked.bellmanS_shock (lead z.1.val z.2.val)
      (lead_cont z.1.val z.2.val) z.2.val,
    h_invS z.1.val z.1.property z.2.val z.2.property⟩)

/-- **Row bounds of the enlarged joint operator** (subtype form): the
ε = 1 matrix `[[9/10, 9248/37717], [2880/37717,
60236226306669/107310302961626]]`. Factored out so both the Perov
uniqueness and the isolation capstone consume the same estimates. -/
theorem coupledJointOpWide_rows
    (lead : SBCF → SBCF → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S : SBCF, Continuous (lead V_T V_S))
    (lead_mem : ∀ V_T V_S : SBCF, ∀ x ∈ Sanctions.S, lead V_T V_S x ∈ Sanctions.I)
    (hσc : ∀ V_S : SBCF, Continuous (fun xa : ℝ × ℝ =>
      lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) xa.1 xa.2))
    (sc_S : ∀ V_S ∈ coupledCarrierS_wide, ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
      StrongConcaveOn Sanctions.I (37717 / 32000)
        (fun s => lowDeltaShocked.toParams.U_S x a s
          + lowDeltaShocked.toParams.β_S
            * (lowDeltaShocked.smear V_S)
              (Sanctions.clipS' (lowDeltaShocked.toParams.F x s))))
    (sc_T : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      StrongConcaveOn Sanctions.I 2 (fun a => coupledLeaderObj V_T V_S x.val a))
    (lopt : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      IsMaxOn (fun a => coupledLeaderObj V_T V_S x.val a) Sanctions.I
        (lead V_T V_S x.val))
    (h_obj_diff : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      ∀ V_T' ∈ coupledCarrierT_wide, ∀ W_S ∈ coupledCarrierS_wide,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      |(coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T V_S x.val))
        - (coupledLeaderObj V_T V_S x.val (lead V_T' W_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T' W_S x.val))|
        ≤ ((2880 / 37717) * dist V_T V_T'
            + (3290537412928 / 53655151480813) * dist V_S W_S)
          * |lead V_T V_S x.val - lead V_T' W_S x.val|)
    (h_invT : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S))
        (hσc V_S) V_T ∈ coupledCarrierT_wide)
    (h_invS : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      lowDeltaShocked.bellmanS_shock (lead V_T V_S) (lead_cont V_T V_S) V_S
        ∈ coupledCarrierS_wide) :
    (∀ z z' : ↥coupledCarrierT_wide × ↥coupledCarrierS_wide,
      dist (coupledJointOpWide lead lead_cont hσc h_invT h_invS z).1
            (coupledJointOpWide lead lead_cont hσc h_invT h_invS z').1
        ≤ (9 / 10) * dist z.1 z'.1 + (9248 / 37717) * dist z.2 z'.2)
    ∧ (∀ z z' : ↥coupledCarrierT_wide × ↥coupledCarrierS_wide,
      dist (coupledJointOpWide lead lead_cont hσc h_invT h_invS z).2
            (coupledJointOpWide lead lead_cont hσc h_invT h_invS z').2
        ≤ (2880 / 37717) * dist z.1 z'.1
          + (60236226306669 / 107310302961626) * dist z.2 z'.2) := by
  constructor
  · -- Target row on the enlarged carrier subtypes.
    intro z z'
    have h := coupled_L_TS_wide z.1.val z'.1.val z.2.val z'.2.val
      (by simpa only [coupledEpsMT_one] using z'.1.property.1)
      (hσc z.2.val) (hσc z'.2.val)
      (fun x hx a ha => sc_S z.2.val z.2.property x hx a ha)
      (fun x hx a ha => sc_S z'.2.val z'.2.property x hx a ha)
    simpa only [Subtype.dist_eq] using h
  · -- Sender row on the enlarged carrier subtypes.
    intro z z'
    have hpol : ∀ x : ↥(Sanctions.S : Set ℝ),
        |lead z.1.val z.2.val x.val - lead z'.1.val z'.2.val x.val|
          ≤ (2880 / 37717) * dist z.1.val z'.1.val
            + (3290537412928 / 53655151480813) * dist z.2.val z'.2.val :=
      fun x => coupled_lead_lipschitz_wide lead z.1.val z.2.val z'.1.val z'.2.val x
        (sc_T z.1.val z.1.property z.2.val z.2.property x)
        (sc_T z'.1.val z'.1.property z'.2.val z'.2.property x)
        (lead_mem z.1.val z.2.val x.val x.property)
        (lead_mem z'.1.val z'.2.val x.val x.property)
        (lopt z.1.val z.1.property z.2.val z.2.property x)
        (lopt z'.1.val z'.1.property z'.2.val z'.2.property x)
        (h_obj_diff z.1.val z.1.property z.2.val z.2.property
          z'.1.val z'.1.property z'.2.val z'.2.property x)
    have h := coupled_L_ST_wide (lead z.1.val z.2.val) (lead z'.1.val z'.2.val)
      (lead_cont z.1.val z.2.val) (lead_cont z'.1.val z'.2.val)
      z.1.val z.2.val z'.1.val z'.2.val hpol
    simpa only [Subtype.dist_eq] using h

/-- **Enlarged within-carrier uniqueness at ε = 1**: the joint two-sided
shocked Bellman operator has exactly one fixed point in the ε = 1
enlarged carrier product — Perov at the ε-shifted matrix, margin
`coupledSchur_margin_wide`. Same consumed analytic package as
`coupledSchur_unique_in_carrier`, at the shifted constants. -/
theorem coupledSchur_unique_in_carrier_wide
    (lead : SBCF → SBCF → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S : SBCF, Continuous (lead V_T V_S))
    (lead_mem : ∀ V_T V_S : SBCF, ∀ x ∈ Sanctions.S, lead V_T V_S x ∈ Sanctions.I)
    (hσc : ∀ V_S : SBCF, Continuous (fun xa : ℝ × ℝ =>
      lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) xa.1 xa.2))
    (sc_S : ∀ V_S ∈ coupledCarrierS_wide, ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
      StrongConcaveOn Sanctions.I (37717 / 32000)
        (fun s => lowDeltaShocked.toParams.U_S x a s
          + lowDeltaShocked.toParams.β_S
            * (lowDeltaShocked.smear V_S)
              (Sanctions.clipS' (lowDeltaShocked.toParams.F x s))))
    (sc_T : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      StrongConcaveOn Sanctions.I 2 (fun a => coupledLeaderObj V_T V_S x.val a))
    (lopt : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      IsMaxOn (fun a => coupledLeaderObj V_T V_S x.val a) Sanctions.I
        (lead V_T V_S x.val))
    (h_obj_diff : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      ∀ V_T' ∈ coupledCarrierT_wide, ∀ W_S ∈ coupledCarrierS_wide,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      |(coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T V_S x.val))
        - (coupledLeaderObj V_T V_S x.val (lead V_T' W_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T' W_S x.val))|
        ≤ ((2880 / 37717) * dist V_T V_T'
            + (3290537412928 / 53655151480813) * dist V_S W_S)
          * |lead V_T V_S x.val - lead V_T' W_S x.val|)
    (h_invT : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S))
        (hσc V_S) V_T ∈ coupledCarrierT_wide)
    (h_invS : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      lowDeltaShocked.bellmanS_shock (lead V_T V_S) (lead_cont V_T V_S) V_S
        ∈ coupledCarrierS_wide) :
    ∃! z : ↥coupledCarrierT_wide × ↥coupledCarrierS_wide,
      coupledJointOpWide lead lead_cont hσc h_invT h_invS z = z := by
  haveI : CompleteSpace ↥coupledCarrierT_wide :=
    coupledCarrierT_wide_isClosed.completeSpace_coe
  haveI : CompleteSpace ↥coupledCarrierS_wide :=
    coupledCarrierS_wide_isClosed.completeSpace_coe
  haveI : Nonempty ↥coupledCarrierT_wide := coupledCarrierT_wide_nonempty.to_subtype
  haveI : Nonempty ↥coupledCarrierS_wide := coupledCarrierS_wide_nonempty.to_subtype
  obtain ⟨hrowT, hrowS⟩ := coupledJointOpWide_rows lead lead_cont lead_mem hσc
    sc_S sc_T lopt h_obj_diff h_invT h_invS
  exact Sanctions.Foundations.Perov.perov2_existsUnique_fixedPoint
    (T := coupledJointOpWide lead lead_cont hσc h_invT h_invS)
    (a := 9 / 10) (b := 9248 / 37717) (c := 2880 / 37717)
    (d := 60236226306669 / 107310302961626)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hrowT hrowS (by norm_num) (by norm_num) coupledSchur_margin_wide

/-- **The reverse bridge (equilibrium → enlarged joint fixed point).**
A shocked feedback-Stackelberg TOP equilibrium whose values lie in the
enlarged carriers and whose policy coincides with the two-sided leader
best response is a fixed point of the enlarged joint operator. Sender
coordinate: the shocked follower fixed-point field at the coinciding
policy (`bellmanS_BCF` policy congruence). Target coordinate: the
shocked leader fixed-point field, since the shocked top integrand
`joint_T_top_integrand (smear V_T) (smear V_S)` and the selector
integrand `targetDynIntegrand (σ_dyn_top (smear V_S)) (smear V_T)` are
definitionally the same expression (both players use the same
selector; no argmax uniqueness needed in this direction). -/
theorem coupledJointOpWide_fixed_of_equilibrium
    (lead : SBCF → SBCF → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S : SBCF, Continuous (lead V_T V_S))
    (hσc : ∀ V_S : SBCF, Continuous (fun xa : ℝ × ℝ =>
      lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) xa.1 xa.2))
    (h_invT : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S))
        (hσc V_S) V_T ∈ coupledCarrierT_wide)
    (h_invS : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      lowDeltaShocked.bellmanS_shock (lead V_T V_S) (lead_cont V_T V_S) V_S
        ∈ coupledCarrierS_wide)
    (E : lowDeltaShocked.ShockedFeedbackStackelbergEquilibriumTop)
    (hVT : E.V_T ∈ coupledCarrierT_wide) (hVS : E.V_S ∈ coupledCarrierS_wide)
    (hαE : E.α = lead E.V_T E.V_S) :
    coupledJointOpWide lead lead_cont hσc h_invT h_invS
        (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩)
      = (⟨E.V_T, hVT⟩, ⟨E.V_S, hVS⟩) := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · -- Target coordinate: the shocked Target Bellman equation.
    change lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear E.V_S))
        (hσc E.V_S) E.V_T = E.V_T
    ext x
    have happly : lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear E.V_S))
        (hσc E.V_S) E.V_T x
        = sSup ((fun a => lowDeltaShocked.toParams.targetDynIntegrand
            (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear E.V_S))
            (lowDeltaShocked.smear E.V_T) x.val a) '' Sanctions.I) := rfl
    have hint : (fun a => lowDeltaShocked.toParams.targetDynIntegrand
            (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear E.V_S))
            (lowDeltaShocked.smear E.V_T) x.val a)
        = (fun a => lowDeltaShocked.toParams.joint_T_top_integrand
            (lowDeltaShocked.smear E.V_T) (lowDeltaShocked.smear E.V_S)
            x.val a) := by
      funext a
      simp only [Sanctions.AbstractGame.Params.targetDynIntegrand,
        Sanctions.AbstractGame.Params.joint_T_top_integrand]
    rw [happly, hint]
    exact (E.V_T_fix_shock x).symm
  · -- Sender coordinate: the shocked follower fixed point at the
    -- coinciding policy.
    change lowDeltaShocked.bellmanS_shock (lead E.V_T E.V_S)
        (lead_cont E.V_T E.V_S) E.V_S = E.V_S
    have hcongr : lowDeltaShocked.bellmanS_shock (lead E.V_T E.V_S)
        (lead_cont E.V_T E.V_S) E.V_S
        = lowDeltaShocked.bellmanS_shock E.α E.hα E.V_S :=
      WitnessKit.bellmanS_BCF_congr_α hαE.symm
        (lead_cont E.V_T E.V_S) E.hα (lowDeltaShocked.smear E.V_S)
    rw [hcongr]
    exact E.V_S_fix_shock.symm
-/

/-! ## §6 CAPSTONE: coupled ε-isolation at ε = 1 — **RETIRED 2026-07-28**

The capstone below consumes the `sc_T` premise proved contradictory by
`coupledSchurWide_sc_T_contradictory` in §5, so it is a vacuous conditional.
It is kept as commented audit evidence and no longer enters the Lean
environment.  See the retirement note in §5 for the reinstatement condition. -/

/- **Retired vacuous capstone (2026-07-28).**

/-- **CAPSTONE (coupled ε-isolation at ε = 1).** Let `(V_T✶, V_S✶)` be
any EXACT-carrier joint fixed point of the two-sided shocked Bellman
system (e.g. the value pair of the certified Perov equilibrium
`coupledSchur_exists_equilibrium` / `coupledSchur_unique_in_carrier` —
value-level fixed-point equations exactly as produced there). Then any
shocked feedback-Stackelberg TOP equilibrium `E` with

* sup-norm ε-closeness at ε = 1: `dist E.V_T V_T✶ ≤ 1`,
  `dist E.V_S V_S✶ ≤ 1` (this discharges the NORM component of
  enlarged-carrier membership, and ONLY that component),
* the two SHAPE pins carried as hypotheses: `E.V_T` monotone (the
  zero-slope lower pin) and `E.V_S` Lipschitz at the enlarged constant
  `K'(1) = 73217/3200` — irreducible per the sawtooth exhibit (an
  ε-sawtooth is ε-close, non-monotone, unbounded-Lipschitz), and
* leader-selector coincidence `E.α = lead E.V_T E.V_S`,

has EXACTLY the fixed point's values: `E.V_T = V_T✶ ∧ E.V_S = V_S✶`.
The enlarged Schur margin `+26982804053357/1073103029616260` survives
the enlargement (`coupledSchur_margin_wide`); consumed analytic
package: same named shapes as the shipped capstone at ε-shifted
constants (file header). This is the scoped Doraszelski–Escobar-style
local isolation — no differentiability, no genericity claim. -/
theorem coupledSchur_epsilon_isolation
    (lead : SBCF → SBCF → ℝ → ℝ)
    (lead_cont : ∀ V_T V_S : SBCF, Continuous (lead V_T V_S))
    (lead_mem : ∀ V_T V_S : SBCF, ∀ x ∈ Sanctions.S, lead V_T V_S x ∈ Sanctions.I)
    (hσc : ∀ V_S : SBCF, Continuous (fun xa : ℝ × ℝ =>
      lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S) xa.1 xa.2))
    (sc_S : ∀ V_S ∈ coupledCarrierS_wide, ∀ x ∈ Sanctions.S, ∀ a ∈ Sanctions.I,
      StrongConcaveOn Sanctions.I (37717 / 32000)
        (fun s => lowDeltaShocked.toParams.U_S x a s
          + lowDeltaShocked.toParams.β_S
            * (lowDeltaShocked.smear V_S)
              (Sanctions.clipS' (lowDeltaShocked.toParams.F x s))))
    (sc_T : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      StrongConcaveOn Sanctions.I 2 (fun a => coupledLeaderObj V_T V_S x.val a))
    (lopt : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      IsMaxOn (fun a => coupledLeaderObj V_T V_S x.val a) Sanctions.I
        (lead V_T V_S x.val))
    (h_obj_diff : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      ∀ V_T' ∈ coupledCarrierT_wide, ∀ W_S ∈ coupledCarrierS_wide,
      ∀ x : ↥(Sanctions.S : Set ℝ),
      |(coupledLeaderObj V_T V_S x.val (lead V_T V_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T V_S x.val))
        - (coupledLeaderObj V_T V_S x.val (lead V_T' W_S x.val)
          - coupledLeaderObj V_T' W_S x.val (lead V_T' W_S x.val))|
        ≤ ((2880 / 37717) * dist V_T V_T'
            + (3290537412928 / 53655151480813) * dist V_S W_S)
          * |lead V_T V_S x.val - lead V_T' W_S x.val|)
    (h_invT : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      lowDeltaShocked.targetDynBCF_shock
        (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear V_S))
        (hσc V_S) V_T ∈ coupledCarrierT_wide)
    (h_invS : ∀ V_T ∈ coupledCarrierT_wide, ∀ V_S ∈ coupledCarrierS_wide,
      lowDeltaShocked.bellmanS_shock (lead V_T V_S) (lead_cont V_T V_S) V_S
        ∈ coupledCarrierS_wide)
    -- The reference: an EXACT-carrier joint fixed point (value level).
    {VstarT VstarS : SBCF}
    (hzT : VstarT ∈ coupledCarrierT) (hzS : VstarS ∈ coupledCarrierS)
    (hfixT : lowDeltaShocked.targetDynBCF_shock
      (lowDeltaShocked.toParams.σ_dyn_top (lowDeltaShocked.smear VstarS))
      (hσc VstarS) VstarT = VstarT)
    (hfixS : lowDeltaShocked.bellmanS_shock (lead VstarT VstarS)
      (lead_cont VstarT VstarS) VstarS = VstarS)
    -- The candidate: ε = 1 proximity + shape pins + selector coincidence.
    (E : lowDeltaShocked.ShockedFeedbackStackelbergEquilibriumTop)
    (hd_T : dist E.V_T VstarT ≤ 1) (hd_S : dist E.V_S VstarS ≤ 1)
    (h_mono : LowerSlopeOnValueOn E.V_T (Set.Icc (0 : ℝ) 1) 0)
    (h_lip : ValueLipschitzWith E.V_S (73217 / 3200))
    (hαE : E.α = lead E.V_T E.V_S) :
    E.V_T = VstarT ∧ E.V_S = VstarS := by
  obtain ⟨hrowT, hrowS⟩ := coupledJointOpWide_rows lead lead_cont lead_mem hσc
    sc_S sc_T lopt h_obj_diff h_invT h_invS
  -- The reference embeds in the enlarged carriers and stays fixed.
  have hzT_wide : VstarT ∈ coupledCarrierT_wide := coupledCarrierT_subset_wide hzT
  have hzS_wide : VstarS ∈ coupledCarrierS_wide := coupledCarrierS_subset_wide hzS
  have hz : coupledJointOpWide lead lead_cont hσc h_invT h_invS
      (⟨VstarT, hzT_wide⟩, ⟨VstarS, hzS_wide⟩)
      = (⟨VstarT, hzT_wide⟩, ⟨VstarS, hzS_wide⟩) :=
    Prod.ext (Subtype.ext hfixT) (Subtype.ext hfixS)
  -- The parametric ε-isolation core at ε = 1.
  exact Sanctions.epsIsolation_of_schur_rows
    (T := coupledJointOpWide lead lead_cont hσc h_invT h_invS)
    (by norm_num) (by norm_num) hrowT hrowS
    (by norm_num) (by norm_num) coupledSchur_margin_wide
    (⟨VstarT, hzT_wide⟩, ⟨VstarS, hzS_wide⟩) hz
    (M_T := 20) (M_S := 523 / 160) (ε_T := 1) (ε_S := 1)
    (by simpa only [lowDeltaTargetCarrierNorm_eq] using hzT.1)
    (by simpa only [lowDeltaSenderCarrierNorm_eq] using hzS.1)
    (shape_T := {V : SBCF | LowerSlopeOnValueOn V (Set.Icc (0 : ℝ) 1) 0})
    (shape_S := {V : SBCF | ValueLipschitzWith V (coupledEpsKS 1)})
    (fun V hn hp => ⟨by norm_num [coupledEpsMT] at hn ⊢; exact hn, hp⟩)
    (fun V hn hp => ⟨by norm_num [coupledEpsMS] at hn ⊢; exact hn, hp⟩)
    hd_T hd_S h_mono (by simpa only [coupledEpsKS_one] using h_lip)
    (fun hWT hWS => coupledJointOpWide_fixed_of_equilibrium lead lead_cont hσc
      h_invT h_invS E hWT hWS hαE)
-/

/-! ## §7 eeCert: enlargement-independent margin, exact largest ε, isolation

The decoupled eeCert world (`EECertWitness.lean`) is strictly better
than the coupled one: cross constants are structurally zero, so the
Schur margin is EXACTLY `1/20` and does not move under enlargement;
norm and upper-Lipschitz enlargements are unbounded; the sole binding
enlargement constraint is the Sender slope floor (relaxable from `16/3`
only down to `24/5`, i.e. by at most `8/15`). Everything here is
UNCONDITIONAL — every consumed ingredient is already proved. -/

/-- The eeCert Schur margin is exactly `1/20`, independent of the
enlargement (both cross constants are structurally zero given the two
policy pins). -/
theorem eeCertSchur_margin_exact :
    EpsilonChain.schurMargin (9 / 10) (1 / 2) 0 0 = 1 / 20 := by
  simp only [EpsilonChain.schurMargin]; norm_num

/-- **σ-pin margin at the relaxed Sender slope floor** `29/6 = 16/3 − 1/2`:
the chord margin `β_S·g'/2 − 6/5 = 1/120 > 0` (the sole binding eeCert
enlargement constraint; the pin needs `g' > 24/5`, so the maximal floor
relaxation is `16/3 − 24/5 = 8/15`). -/
theorem eeCert_sigma_pin_margin_relaxed :
    (1 / 2 : ℝ) * (29 / 6) / 2 - 6 / 5 = 1 / 120
      ∧ (16 : ℝ) / 3 - 24 / 5 = 8 / 15 := by
  constructor <;> norm_num

/-- **eeCert norm enlargement is unbounded**: for every ε ≥ 0 both
norm-invariance inequalities survive (Sender image `23/2 + ε/2 ≤ 12 + ε`,
Target image `75 + (9/10)ε ≤ 80 + ε`) — the image radius is
`M + β·ε < M + ε` because `M = ‖U‖/(1−β)` exactly. -/
theorem eeCert_norm_enlargement_unbounded (ε : ℝ) (hε : 0 ≤ ε) :
    23 / 2 + ε / 2 ≤ 12 + ε ∧ 75 + (9 / 10) * ε ≤ 80 + ε := by
  constructor <;> linarith

/-- `‖V_T✶‖ ≤ 11` — the exact eeCert Target fixed value
`V_T✶ = (82x+39)/11` peaks at `121/11 = 11`, leaving norm slack
`80 − 11 = 69` inside the exact carrier. -/
theorem eeVTstar_norm_le : ‖eeVTstar‖ ≤ 11 :=
  (affineInterceptBCF_mem_gainBall (by norm_num) (by norm_num)
    (by norm_num : (39 : ℝ) / 11 + 82 / 11 ≤ 11)).1

/-- `‖V_S✶‖ ≤ 11` — the exact eeCert Sender fixed value
`V_S✶ = (16x+17)/3` peaks at `33/3 = 11`, leaving norm slack
`12 − 11 = 1` inside the exact carrier. -/
theorem eeVSstar_norm_le : ‖eeVSstar‖ ≤ 11 :=
  (affineInterceptBCF_mem_gainBall (by norm_num) (by norm_num)
    (by norm_num : (17 : ℝ) / 3 + 16 / 3 ≤ 11)).1

/-- **The eeCert closed-form pair is a fixed point of the joint subtype
operator** — the W2 pins (`eeCert_VS_star_fixed`, `eeCert_VT_star_fixed`)
routed through the parametric bridge
`fixedPoint_of_bellman_fixed_of_selector_coincidence` at the derived
defiance policy `α_on ≡ 0`. -/
theorem eeCert_star_pair_isFixedPoint :
    (eeCertClass.jointTargetOp_sub eeCertClass_IsInvariant
        (⟨eeVTstar, eeVTstar_mem⟩, ⟨eeVSstar, eeVSstar_mem⟩),
      eeCertClass.jointSenderOp_sub eeCertClass_IsInvariant
        (⟨eeVTstar, eeVTstar_mem⟩, ⟨eeVSstar, eeVSstar_mem⟩))
      = (⟨eeVTstar, eeVTstar_mem⟩, ⟨eeVSstar, eeVSstar_mem⟩) := by
  refine eeCertClass.fixedPoint_of_bellman_fixed_of_selector_coincidence
    eeCertClass_IsInvariant eeVTstar_mem eeVSstar_mem
    (α := fun _ => (0 : ℝ)) continuous_const ?_ ?_ ?_
  · exact (eeCert_α_on_eq_zero ⟨eeVTstar, eeVTstar_mem⟩
      ⟨eeVSstar, eeVSstar_mem⟩).symm
  · exact eeCert_VS_star_fixed.symm
  · intro x
    have hint : (fun a => eeCertParams.joint_T_top_integrand eeVTstar eeVSstar
          x.val a)
        = (fun a => eeCertParams.joint_T_integrand eeVTstar eeVSstar
          x.val a) := by
      funext a
      exact eeCertParams.joint_T_top_integrand_eq_joint_T_integrand_of_unique
        (eeCert_DAU_on_carrier eeVSstar_mem) x.property a
    rw [hint,
      ← eeCertParams.jointTarget_BCF_on_S_apply eeVTstar eeVSstar
        (eeCert_DAU_on_carrier eeVSstar_mem).toOnI x,
      eeCert_VT_star_fixed x]

/-- **eeCert ε-isolation at the exact largest carrier ε:
`(ε_T, ε_S) = (69, 1)`** — larger slack ⇒ larger ε (vs ε = 1 at the
coupled witness). UNCONDITIONAL: rows (`eeCertClass_hT_T_op` /
`eeCertClass_hT_S_op`, cross constants structurally zero), invariance
(`eeCertClass_IsInvariant`), the fixed point (W2 closed forms), and the
selector pin are all proved; the Schur margin is the
enlargement-independent `(1 − 9/10)(1 − 1/2) = 1/20 > 0 = L_TS·L_ST`.
Any top-selector feedback Stackelberg equilibrium of the eeCert economy
with the defiance-policy convention `α ≡ 0`, values within `(69, 1)` of
`(V_T✶, V_S✶) = ((82x+39)/11, (16x+17)/3)` in sup-norm, and the affine
slope pins carried as hypotheses (sawtooth-irreducible), has exactly
the certified values. -/
theorem eeCert_epsilon_isolation
    (E : eeCertParams.FeedbackStackelbergEquilibriumTop)
    (hα : E.α = fun _ => (0 : ℝ))
    (hd_T : dist E.V_T eeVTstar ≤ 69) (hd_S : dist E.V_S eeVSstar ≤ 1)
    (h_lip_T : ValueLipschitzWith E.V_T (82 / 11))
    (h_slope_T : LowerSlopeOnValueOn E.V_T (Set.Icc (0 : ℝ) 1) (82 / 11))
    (h_lip_S : ValueLipschitzWith E.V_S (16 / 3))
    (h_slope_S : LowerSlopeOnValueOn E.V_S (Set.Icc (0 : ℝ) 1) (16 / 3)) :
    E.V_T = eeVTstar ∧ E.V_S = eeVSstar :=
  eeCertClass.epsilonIsolation_feedbackStackelbergTop_schur
    eeCertClass_IsInvariant
    (β_T := 9 / 10) (β_S := 1 / 2) (L_TS := 0) (L_ST := 0)
    le_rfl le_rfl
    (eeCertClass_hT_T_op eeCertClass_IsInvariant)
    (eeCertClass_hT_S_op eeCertClass_IsInvariant)
    (by norm_num) (by norm_num)
    (⟨eeVTstar, eeVTstar_mem⟩, ⟨eeVSstar, eeVSstar_mem⟩)
    eeCert_star_pair_isFixedPoint
    (M_T := 11) (M_S := 11) (ε_T := 69) (ε_S := 1)
    eeVTstar_norm_le eeVSstar_norm_le
    (shape_T := {V : Val | ValueLipschitzWith V (82 / 11)
      ∧ LowerSlopeOnValueOn V (Set.Icc (0 : ℝ) 1) (82 / 11)})
    (shape_S := {V : Val | ValueLipschitzWith V (16 / 3)
      ∧ LowerSlopeOnValueOn V (Set.Icc (0 : ℝ) 1) (16 / 3)})
    (fun V hn hp => by
      show V ∈ eeCarrierT
      rw [eeCarrierT_eq]
      exact ⟨by norm_num at hn ⊢; exact hn, hp.1, hp.2⟩)
    (fun V hn hp => by
      show V ∈ eeCarrierS
      rw [eeCarrierS_eq]
      exact ⟨by norm_num at hn ⊢; exact hn, hp.1, hp.2⟩)
    E hd_T hd_S ⟨h_lip_T, h_slope_T⟩ ⟨h_lip_S, h_slope_S⟩
    (fun hVT hVS => by
      rw [hα, eeCert_α_on_eq_zero ⟨E.V_T, hVT⟩ ⟨E.V_S, hVS⟩])

/-! ## §8 eeCert GLOBAL isolation (flagship bonus)

Stronger than ε-isolation: at eeCert the defiance-policy coincidence
`E.α ≡ 0` ALONE pins both values — no proximity hypothesis, no shape
pins. The Sender Bellman operator at the constant policy is a GLOBAL
`β_S = 1/2` contraction on all of BCF, pinning `V_S = (16x+17)/3`; then
the pinned selector `σ_dyn_top(V_S✶) ≡ 1` makes the top-integrand
Target operator a GLOBAL `β_T = 9/10` contraction, pinning
`V_T = (82x+39)/11`. This is the honest form of "the admissible ε at
eeCert is unbounded" (larger slack ⇒ larger ε, taken to its limit). -/

/-- Target Bellman image in closed form at a FREE Target continuation
(the eeCert §7 image lemma without the Target-carrier restriction —
only the Sender carrier membership of `V_S✶` is used, since the
defiance corner `a = 0` is the argmax for every `V_T`). -/
theorem eeCert_jointTarget_image_free (V_T : Val)
    (x : ↥(Sanctions.S : Set ℝ)) :
    eeCertParams.jointTarget_BCF_on_S V_T eeVSstar
        (eeCert_DAU_on_carrier eeVSstar_mem).toOnI x
      = 41 / 10 * x.val - 3
        + 9 / 10 * V_T (Sanctions.clipS' ((x.val + 1) / 2)) := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn V_T eeVSstar
        (eeCert_DAU_on_carrier eeVSstar_mem).toOnI x
        (⟨le_refl 0, by norm_num⟩ : (0 : ℝ) ∈ Sanctions.I)
        (eeCert_zero_isMaxOn_joint V_T eeVSstar_mem x.property),
      eeCert_joint_T_integrand_eq V_T eeVSstar_mem x.property
        (⟨le_refl 0, by norm_num⟩ : (0 : ℝ) ∈ Sanctions.I)]
  ring

/-- **eeCert GLOBAL isolation**: any top-selector feedback Stackelberg
equilibrium of the eeCert economy whose policy is the defiance
convention `α ≡ 0` has EXACTLY the certified values — no proximity, no
shape pins. Consumes only proved machinery: the two W2 closed-form
fixed points, the global `β_S` contraction of `bellmanS_BCF` at a fixed
policy, the carrier-free defiance argmax, and the σ-pin at `V_S✶`. -/
theorem eeCert_global_isolation
    (E : eeCertParams.FeedbackStackelbergEquilibriumTop)
    (hα : E.α = fun _ => (0 : ℝ)) :
    E.V_T = eeVTstar ∧ E.V_S = eeVSstar := by
  -- Step 1: the Sender value is pinned by the global 1/2-contraction.
  have hVS_fix : E.V_S
      = eeCertParams.bellmanS_BCF (fun _ => (0 : ℝ)) continuous_const E.V_S := by
    have h := E.V_S_fix
    rwa [WitnessKit.bellmanS_BCF_congr_α hα E.hα continuous_const E.V_S] at h
  have hS : E.V_S = eeVSstar := by
    have hc : (0 : ℝ) ≤ (1 / 2) * dist E.V_S eeVSstar := by positivity
    have hd : dist E.V_S eeVSstar ≤ (1 / 2) * dist E.V_S eeVSstar := by
      calc dist E.V_S eeVSstar
          = dist (eeCertParams.bellmanS_BCF (fun _ => (0 : ℝ))
                continuous_const E.V_S)
              (eeCertParams.bellmanS_BCF (fun _ => (0 : ℝ))
                continuous_const eeVSstar) := by
            rw [← hVS_fix, eeCert_VS_star_fixed]
        _ ≤ (1 / 2) * dist E.V_S eeVSstar := by
            rw [BoundedContinuousFunction.dist_le hc]
            intro x
            have h := eeCertParams.bellmanS_BCF_pointwise_dist
              (α := fun _ => (0 : ℝ)) continuous_const E.V_S eeVSstar x
            have hβ : eeCertParams.β_S = 1 / 2 := rfl
            rwa [hβ] at h
    have h0 : dist E.V_S eeVSstar ≤ 0 := by linarith
    exact eq_of_dist_eq_zero (le_antisymm h0 dist_nonneg)
  -- Step 2: with `V_S = V_S✶`, the top Target equation is the global
  -- 9/10-contraction closed form; it pins `V_T = V_T✶`.
  have hVT_eq : ∀ x : ↥(Sanctions.S : Set ℝ),
      E.V_T x = 41 / 10 * x.val - 3
        + 9 / 10 * E.V_T (Sanctions.clipS' ((x.val + 1) / 2)) := by
    intro x
    have h1 := E.V_T_fix_top x
    rw [hS] at h1
    have hint : (fun a => eeCertParams.joint_T_top_integrand E.V_T eeVSstar
          x.val a)
        = (fun a => eeCertParams.joint_T_integrand E.V_T eeVSstar
          x.val a) := by
      funext a
      exact eeCertParams.joint_T_top_integrand_eq_joint_T_integrand_of_unique
        (eeCert_DAU_on_carrier eeVSstar_mem) x.property a
    rw [hint,
      ← eeCertParams.jointTarget_BCF_on_S_apply E.V_T eeVSstar
        (eeCert_DAU_on_carrier eeVSstar_mem).toOnI x,
      eeCert_jointTarget_image_free E.V_T x] at h1
    exact h1
  have hstar_eq : ∀ x : ↥(Sanctions.S : Set ℝ),
      eeVTstar x = 41 / 10 * x.val - 3
        + 9 / 10 * eeVTstar (Sanctions.clipS' ((x.val + 1) / 2)) := by
    intro x
    rw [← eeCert_VT_star_fixed x]
    exact eeCert_jointTarget_image_free eeVTstar x
  have hT : E.V_T = eeVTstar := by
    have hc : (0 : ℝ) ≤ (9 / 10) * dist E.V_T eeVTstar := by positivity
    have hd : dist E.V_T eeVTstar ≤ (9 / 10) * dist E.V_T eeVTstar := by
      rw [BoundedContinuousFunction.dist_le hc]
      intro x
      rw [Real.dist_eq, hVT_eq x, hstar_eq x]
      have hpt : |E.V_T (Sanctions.clipS' ((x.val + 1) / 2))
          - eeVTstar (Sanctions.clipS' ((x.val + 1) / 2))|
          ≤ dist E.V_T eeVTstar := by
        have h := BoundedContinuousFunction.dist_coe_le_dist
          (f := E.V_T) (g := eeVTstar) (Sanctions.clipS' ((x.val + 1) / 2))
        rwa [Real.dist_eq] at h
      have hkey : (41 / 10 * x.val - 3
            + 9 / 10 * E.V_T (Sanctions.clipS' ((x.val + 1) / 2)))
          - (41 / 10 * x.val - 3
            + 9 / 10 * eeVTstar (Sanctions.clipS' ((x.val + 1) / 2)))
          = (9 / 10) * (E.V_T (Sanctions.clipS' ((x.val + 1) / 2))
            - eeVTstar (Sanctions.clipS' ((x.val + 1) / 2))) := by ring
      rw [hkey, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10)]
      linarith [hpt]
    have h0 : dist E.V_T eeVTstar ≤ 0 := by linarith
    exact eq_of_dist_eq_zero (le_antisymm h0 dist_nonneg)
  exact ⟨hT, hS⟩

/-- **The unbounded-ε corollary at eeCert**: for EVERY ε the
ε-isolation statement holds given only the policy convention — the
proximity hypotheses are not needed at all (one-line from the global
theorem; recorded in ε-form for symmetry with the coupled witness). -/
theorem eeCert_epsilon_isolation_unbounded (ε_T ε_S : ℝ)
    (E : eeCertParams.FeedbackStackelbergEquilibriumTop)
    (hα : E.α = fun _ => (0 : ℝ))
    (_hd_T : dist E.V_T eeVTstar ≤ ε_T) (_hd_S : dist E.V_S eeVSstar ≤ ε_S) :
    E.V_T = eeVTstar ∧ E.V_S = eeVSstar :=
  eeCert_global_isolation E hα

end Examples

end -- noncomputable section

end Sanctions

/-! ## Axiom hygiene (Rule 10) -/

#print axioms Sanctions.fixedPoint_unique_of_schur_rows
#print axioms Sanctions.epsIsolation_of_schur_rows
namespace Sanctions.AbstractGame.Params.ValueClass2
#print axioms epsilonIsolation_feedbackStackelbergTop_schur
end Sanctions.AbstractGame.Params.ValueClass2
-- `coupledSchur_epsilon_isolation` and `coupledSchur_unique_in_carrier_wide`
-- were retired on 2026-07-28 as vacuous conditionals; their axiom scans are
-- replaced by the scan of the refutation that retired them.  A clean axiom
-- scan on a vacuous conditional is actively misleading, which is why the two
-- lines are removed rather than merely commented at the call site.
#print axioms Sanctions.Examples.coupledSchurWide_sc_T_contradictory
#print axioms Sanctions.Examples.coupledJointOpWide_h_invT_contradictory
#print axioms Sanctions.Examples.eeCert_epsilon_isolation
#print axioms Sanctions.Examples.eeCert_global_isolation
#print axioms Sanctions.Examples.coupledEpsMargin_pos_at_one
#print axioms Sanctions.Examples.coupledEpsMargin_frontier_bracket
