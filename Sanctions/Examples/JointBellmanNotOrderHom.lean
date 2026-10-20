/-
# Kernel-checked refutation: the leader argmax is monotone in `V_T` in
NEITHER direction under the pointwise order

The A4 (general-existence) closure artifact. The dual-Tarski route to
from-primitives equilibrium existence
(`Foundations/TarskiMPE.joint_value_fixedPoint_via_dual`) needs the
joint value operator to be an order homomorphism on the dualized value
rectangle, whose load-bearing ingredient — "D3b" in the 2026-06-18/19
probe record — is that the leader's joint-Bellman argmax is *antitone*
in the Target continuation value under the pointwise order. The June
probes exhibited this false numerically (order-reversal `+0.45` on a
Float grid); this file exhibits the refutation at exact rationals.

## Parametric, not witness-specific

The mathematical content now lives in
`Theory/Equilibrium/LeaderArgmaxOrderRefutation.lean`, proved for an
arbitrary `p : AbstractGame.Params`, an arbitrary Target continuation
value, and symbolic rate constants. Everything in this file is a
specialization of two parametric theorems:

* `leaderArgmax_not_antitone_pointwise` — adding a **nonnegative**
  low-state ramp drives the leader argmax **up** to full compliance;
* `leaderArgmax_not_monotone_pointwise` — adding a **nonnegative**
  high-state ramp drives it **down** to full defiance.

Both hold at every economy with a live *placation channel*: compliance
strictly lowers the successor political state, at any rate `κ > 0`. The
ramp height needed is the closed form `c ≥ L/(β_T·κ)` where `L` bounds
the base integrand's variation in compliance — no magnitude is chosen.

## The specialization

At the B2 witness economy `b2Params` (state `x = 1/2`, Sender carrier
member `V_S = base`), the forward-looking Sender response is the pinned
interior selector `σ_dyn = 7/8 − a/2`, so the successor state is
`y(a) = 11/16 − a/4` (`b2_jointSucc_eq`): the placation channel runs at
rate `κ = 1/4`, and the anchor `11/16` of the perturbation below is that
*derived* defiance successor, not a chosen number.

* At `V_T = 5y` (the affine hawk value) the integrand is
  `5/2 − (27/100)·a` (`b2_baseIntegrand_eq`): the leader argmax is `0`.
* Adding `ntDelta = lowStateRamp 2 y(0)` — nonnegative, so `V_T + Δ ≥
  V_T` pointwise — makes the integrand `5/2 + (9/50)·a`: the argmax
  jumps to `1`. Antitonicity fails.
* Adding instead `highStateRamp 1 y(1)` to *that* value — again
  nonnegative — sends the argmax back to `0`. Monotonicity fails too.

## What this closes, and what it does not

**Closed: the pointwise-order Tarski route**, and now for *every*
economy in which the leader's action moves the successor state at a
strictly positive rate — not merely at `b2Params`. Under the pointwise
order a nonnegative increment may be concentrated near either
successor, so the comparative static is available in neither direction
and no complete-lattice carrier repairs it. Together with the
machine-checked Hölder-½ selector bound
(`StrongConcaveHolder.sigma_dyn_sq_le_of_strongConcave`), which kills
the naive contraction route, this is why the witness-route /
shocked-route posture is taken here.

**NOT closed: the slope-order route of Curtat (1996).** Curtat orders
continuation values by their *derivatives* — `∂v ≥ ∂w` iff
`∂v(u) ≥ ∂w(u)` for almost all `u` (Curtat 1996, §4.1) — not
pointwise; his Theorem 4.1 gives the reduced game a unique pure Nash
equilibrium increasing in the state *and in the slope* `∂ṽ`, and
existence of the Markov equilibrium then follows from **Schauder's**
theorem on a compact convex set of increasing Lipschitz functions
(Theorem 4.6), with the slope bounds computable from the primitives —
not from Tarski. Nothing below refutes that route:

* the increment `ntDelta` is state-**antitone** (slope `−2` where it
  bites), hence not positive in the slope order at all; and
* the mirror increment `highStateRamp` *is* state-monotone, hence
  positive in the slope order — but the argmax it moves goes **down**,
  which is what Theorem 4.1 predicts once the transition is
  *decreasing* in the leader's action. `b2_placation` proves exactly
  that decrease at `b2Params`, so this economy sits outside Curtat's
  supermodular class and is no counterexample to his theorem.

The honest scope is therefore: pointwise-order Tarski is refuted;
slope-order + Schauder is untouched and remains a live route to
from-primitives existence.
-/

import Sanctions.Examples.B2NonMonotoneCertWitness
import Sanctions.Theory.Equilibrium.LeaderArgmaxOrderRefutation

namespace Sanctions
namespace Examples

open AbstractGame.Params

noncomputable section

/-! ## 1. The derived successor state at the probe -/

/-- The Sender's peak sanction at the probe state is `7/8`. -/
theorem b2pt_at_half : b2pt (1/2 : ℝ) = 7/8 := by
  unfold b2pt b2clip
  rw [max_eq_left (by norm_num : (0:ℝ) ≤ 1/2),
      min_eq_left (by norm_num : (1/2:ℝ) ≤ 1),
      max_eq_right (by norm_num : (1/2:ℝ) - 5/8 ≤ 0)]
  norm_num

/-- The B2 dynamic response at the probe state: `σ = 7/8 − a/2`
(interior for every feasible compliance). -/
theorem b2sdyn_at_half {a : ℝ} (ha : a ∈ Sanctions.I) :
    b2sdyn (1/2) a = 7/8 - a/2 := by
  have hlam : b2lam (1/2 : ℝ) = 4 := by
    unfold b2lam b2clip
    rw [max_eq_left (by norm_num : (0:ℝ) ≤ 1/2),
        min_eq_left (by norm_num : (1/2:ℝ) ≤ 1),
        max_eq_right (by norm_num : (1/2:ℝ) - 1/2 ≤ 0)]
    norm_num
  unfold b2sdyn
  rw [b2pt_at_half, hlam, min_eq_right (by linarith [ha.1] : 7/8 - 2*a/4 ≤ 1)]
  ring

/-- **The derived successor state at the probe**: once the Sender has
best-responded, leader compliance `a` sends the economy to
`y(a) = 11/16 − a/4`. Compliance *lowers* the continuation state — the
placation channel — at rate exactly `1/4`. -/
theorem b2_jointSucc_eq {a : ℝ} (ha : a ∈ Sanctions.I) :
    (b2Params.jointSucc b2baseBCF (1/2) a).val = 11/16 - a/4 := by
  have hmemS : b2baseBCF ∈ b2CarrierS := b2_zero_shift_mem
  have hhalf : (1/2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  change (Sanctions.clipS' (b2Params.F (1/2)
      (b2Params.σ_dyn b2baseBCF (1/2) a))).val = _
  rw [b2_σ_dyn_eq hmemS hhalf ha, b2sdyn_at_half ha, b2Params_F]
  have hy : (1/2 + (7/8 - a/2))/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by nlinarith [ha.2], by nlinarith [ha.1]⟩
  rw [clipS'_val_of_mem hy]
  ring

/-- **The placation channel at the probe, in the form the parametric
refutation consumes**: raising compliance from `b` to `b'` lowers the
successor political state by at least `(1/4)·(b' − b)` (here: exactly
that). -/
theorem b2_placation : ∀ b ∈ Sanctions.I, ∀ b' ∈ Sanctions.I, b ≤ b' →
    (1/4 : ℝ) * (b' - b)
      ≤ (b2Params.jointSucc b2baseBCF (1/2) b).val
        - (b2Params.jointSucc b2baseBCF (1/2) b').val := by
  intro b hb b' hb' _
  rw [b2_jointSucc_eq hb, b2_jointSucc_eq hb']
  linarith

/-! ## 2. The antitone increment -/

/-- The state-antitone ramp `Δ(y) = 2·(y(0) − y)⁺`: nonnegative
everywhere, rewarding LOW continuation states. Its anchor is the
*derived* full-defiance successor `y(0)`, and its height `2` is any
value past the closed-form threshold `L/(β_T·κ) = (27/100)/(9/40) =
6/5` supplied by the parametric theorem. -/
def ntDelta : Val :=
  Sanctions.lowStateRamp 2 (b2Params.jointSucc b2baseBCF (1/2) 0).val

@[simp] theorem ntDelta_apply (y : ↥(Sanctions.S : Set ℝ)) :
    ntDelta y = 2 * max (11/16 - y.val) 0 := by
  rw [ntDelta, Sanctions.lowStateRamp_apply,
      b2_jointSucc_eq (⟨le_refl 0, zero_le_one⟩ : (0:ℝ) ∈ Sanctions.I)]
  norm_num

theorem ntDelta_nonneg (y : ↥(Sanctions.S : Set ℝ)) : 0 ≤ ntDelta y :=
  Sanctions.lowStateRamp_nonneg (by norm_num) _ y

/-! ## 3. The base and perturbed integrands at `x = 1/2` -/

/-- **Base-integrand closed form** at the affine hawk value: the leader
integrand strictly falls in compliance (slope `−27/100`), so full
defiance is the base argmax. -/
theorem b2_baseIntegrand_eq {a : ℝ} (ha : a ∈ Sanctions.I) :
    b2Params.joint_T_integrand (affineBCF 5) b2baseBCF (1/2) a
      = 5/2 - (27/100)*a := by
  have hmemT : affineBCF 5 ∈ b2CarrierT := b2_zero_shift_mem
  have hmemS : b2baseBCF ∈ b2CarrierS := b2_zero_shift_mem
  have hhalf : (1/2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hp : b2p (1/2 : ℝ) = 7/8 := by
    unfold b2p; rw [b2pt_at_half]; norm_num
  have h0 : (affineBCF 5) (Sanctions.clipS' 0) = 0 := by
    rw [affineBCF_apply,
      clipS'_val_of_mem (⟨le_refl 0, zero_le_one⟩ : (0:ℝ) ∈ Set.Icc (0:ℝ) 1)]
    ring
  rw [b2_joint_T_integrand_eq hmemT hmemS hhalf ha, b2sdyn_at_half ha, hp, h0]
  ring

/-- **Perturbed-integrand closed form**: with the ramp added to the
affine hawk value, the leader integrand strictly RISES in compliance
(slope `+9/50`) — the placation channel's continuation discount
overwhelms the direct terms once low states are rewarded. -/
theorem ntIntegrand_eq {a : ℝ} (ha : a ∈ Sanctions.I) :
    b2Params.joint_T_integrand (affineBCF 5 + ntDelta) b2baseBCF (1/2) a
      = 5/2 + (9/50)*a := by
  rw [b2Params.joint_T_integrand_add, b2_baseIntegrand_eq ha, ntDelta_apply,
      b2_jointSucc_eq ha, b2Params_β_T,
      max_eq_left (by linarith [ha.1] : (0:ℝ) ≤ 11/16 - (11/16 - a/4))]
  ring

/-- **Full compliance is the leader argmax at the perturbed value.**
The pointwise-raised continuation value has flipped the leader's whole
ranking of compliance. -/
theorem b2_one_isMaxOn_joint_ntDelta :
    IsMaxOn (fun b => b2Params.joint_T_integrand (affineBCF 5 + ntDelta)
      b2baseBCF (1/2) b) Sanctions.I 1 := by
  rw [isMaxOn_iff]
  intro b hb
  rw [ntIntegrand_eq hb,
      ntIntegrand_eq (⟨zero_le_one, le_refl 1⟩ : (1:ℝ) ∈ Sanctions.I)]
  linarith [hb.2]

/-! ## 4. The refutations -/

/-- **Kernel-checked: the leader joint-Bellman argmax is NOT antitone
in the Target continuation value under the pointwise order** — the D3b
ingredient of the dual-Tarski order-homomorphism route, refuted by an
exhibited object rather than a numeric probe. At `b2Params`,
`x = 1/2`, `V_S = base`: the affine hawk value has leader argmax `0`
(full defiance), and raising it pointwise by the state-antitone ramp
`ntDelta` moves the argmax to `1` (full compliance) — the pointwise
order permits exactly the increment shapes that reverse the
comparative static, so the joint value operator is not an order
homomorphism on any pointwise-ordered value rectangle containing these
values, and `TarskiMPE.joint_value_fixedPoint_via_dual` cannot be
instantiated there.

One-line specialization of the parametric
`leaderArgmax_not_antitone_pointwise` at `κ = 1/4` (the derived
placation rate), `L = 27/100` (the derived base slope), and ramp height
`c = 2 > L/(β_T·κ) = 6/5`. -/
theorem b2_leaderArgmax_not_antitone_in_V_T :
    ¬ (∀ (V_T V_T' V_S : Val), (∀ y, V_T y ≤ V_T' y) →
        ∀ x ∈ Sanctions.S, ∀ a a' : ℝ,
          a ∈ Sanctions.I → a' ∈ Sanctions.I →
          IsMaxOn (fun b => b2Params.joint_T_integrand V_T V_S x b)
            Sanctions.I a →
          IsMaxOn (fun b => b2Params.joint_T_integrand V_T' V_S x b)
            Sanctions.I a' →
          a' ≤ a) := by
  have hmemT : affineBCF 5 ∈ b2CarrierT := b2_zero_shift_mem
  have hmemS : b2baseBCF ∈ b2CarrierS := b2_zero_shift_mem
  have hhalf : (1/2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine b2Params.leaderArgmax_not_antitone_pointwise (affineBCF 5) b2baseBCF
    (1/2) ⟨by norm_num, by norm_num⟩ (κ := 1/4) (L := 27/100) (c := 2)
    (a := 0) (by rw [b2Params_β_T]; norm_num) (by norm_num) (by norm_num)
    b2_placation ?_ (by rw [b2Params_β_T]; norm_num)
    ⟨le_refl 0, zero_le_one⟩ (by norm_num)
    (b2_zero_isMaxOn_joint hmemT hmemS hhalf)
  intro b hb b' hb' _
  rw [b2_baseIntegrand_eq hb, b2_baseIntegrand_eq hb']
  linarith

/-- **Kernel-checked: the leader argmax is NOT monotone in the Target
continuation value under the pointwise order either.** Starting from
the already-perturbed value `affineBCF 5 + ntDelta`, whose leader
argmax is full compliance `1`, adding the nonnegative *state-monotone*
ramp `highStateRamp 1 y(1)` sends the argmax back down to full defiance
`0`. So the pointwise order constrains the leader's argmax in neither
direction, and the failure is not an artifact of the first
perturbation's downward slope.

One-line specialization of the parametric
`leaderArgmax_not_monotone_pointwise` at `κ = 1/4`, `L = 9/50` (the
derived perturbed slope), and ramp height `c = 1 > L/(β_T·κ) = 4/5`. -/
theorem b2_leaderArgmax_not_monotone_in_V_T :
    ¬ (∀ (V_T V_T' V_S : Val), (∀ y, V_T y ≤ V_T' y) →
        ∀ x ∈ Sanctions.S, ∀ a a' : ℝ,
          a ∈ Sanctions.I → a' ∈ Sanctions.I →
          IsMaxOn (fun b => b2Params.joint_T_integrand V_T V_S x b)
            Sanctions.I a →
          IsMaxOn (fun b => b2Params.joint_T_integrand V_T' V_S x b)
            Sanctions.I a' →
          a ≤ a') := by
  refine b2Params.leaderArgmax_not_monotone_pointwise (affineBCF 5 + ntDelta)
    b2baseBCF (1/2) ⟨by norm_num, by norm_num⟩ (κ := 1/4) (L := 9/50)
    (c := 1) (a := 1) (by rw [b2Params_β_T]; norm_num) (by norm_num)
    (by norm_num) b2_placation ?_ (by rw [b2Params_β_T]; norm_num)
    ⟨zero_le_one, le_refl 1⟩ (by norm_num) b2_one_isMaxOn_joint_ntDelta
  intro b hb b' hb' _
  rw [ntIntegrand_eq hb, ntIntegrand_eq hb']
  linarith

end -- noncomputable section

#print axioms b2_leaderArgmax_not_antitone_in_V_T
#print axioms b2_leaderArgmax_not_monotone_in_V_T
#print axioms b2_jointSucc_eq
#print axioms b2_placation

end Examples
end Sanctions
