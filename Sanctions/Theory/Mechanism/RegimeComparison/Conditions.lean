/-
Sanctions/Theory/Mechanism/RegimeComparison/Conditions.lean

**The assumption surface of the four-regime comparison, in one place, adopted
nowhere.**

This directory exists to make a boundary architectural rather than only
documentary. Everything in `Theory/Mechanism/` *above* this folder is
assumption-free:

* `ContinuationProfile.lean` — definitions. `withProfile` is a total function,
  so it cannot fail and cannot exclude an economy.
* `PrimitiveReduction.lean` — reductions. `C1` is shown to be a stage-payoff
  condition and `C2` to follow from one; both are theorems *about* conditions,
  not adoptions of them.
* `RegimeExistence.lean` — constructions, plus an honest account of what is not
  constructed.

Everything **inside** this folder carries a condition the baseline does not
imply. Nothing here is consumed by any theorem in this development, and the
separation is the point: a reader can see the entire assumption surface of the
mechanism programme by reading one file, and can see that it is not yet load
bearing by observing that nothing imports it downstream.

## Status

`ASSUMPTION-SURFACE-REGISTER.md` carries the classification. In summary:

| | where it lives | status |
|---|---|---|
| `C1` | `PrimitiveReduction.SenderStagePlacation` | **not an assumption in the proposed form** — the continuation cancels identically |
| `C2` | `PrimitiveReduction.SenderStageStateMonotone` | **derivable** from a stage-payoff monotonicity through existing machinery |
| `C3` | here | would be a new primitive — **not adopted** |
| `C4` | here | would be a new primitive — **not adopted** |
| `C5` | here | would be a new primitive, and the load-bearing one — **not adopted** |

`C1` and `C2` are *not* in this folder, and that placement is the finding: they
belong with the primitives because that is where they live.

## The prior obligation

None of these conditions matters until the four regimes exist.
`RegimeExistence.lean` shows the factorial splits — `00` and `10` are
constructed, `01` and `11` are not, because a forward-looking Sender closes a
loop with no single operator to contract. Conditions `C3`–`C5` order regimes
that are not known to exist in pure strategies where the mechanism is
interesting. That is a stronger objection to adopting them than any of the
individual costs below.
-/

import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Theory.Mechanism.ContinuationProfile

namespace Sanctions
namespace AbstractGame
namespace Params

open Set Sanctions.Mechanism
open BoundedContinuousFunction

variable (p : Params)

/-! ## The reduced Target objective

`C3`–`C5` are conditions on the Target's objective *after* the Sender's response
has been substituted into it. That substitution is what makes them different in
kind from `C1` and `C2`: they constrain an endogenous object, and
`suggestions/33` §6 concedes that their preservation through the reduction is an
obligation rather than a closure property. -/

/-- **The Sender's greatest response at a continuation profile.**

`σ_dyn_top` read at the profile view. When the Sender is myopic the discount
factor is zero, so this is the greatest maximizer of the *stage* payoff.

**A selection caveat that must not be lost.** `Params.σ_isMaxOn_U_S` makes the
model's own static response `σ` *a* maximizer of `U_S`, not the greatest one, and
nothing in this development proves them equal. So at the myopic profiles this
object and the `Params` field `σ` coincide only where the static argmax is
unique. They are two admissible readings of "the myopic Sender" — the greatest
selection and the model's designated one — and a four-regime comparison must say
which it uses, or a regime becomes a proof device rather than an equilibrium
(`suggestions/32` §9, acceptance test 2). `RegimeExistence.regime10TargetValue`
is built on the `Params` field. -/
noncomputable def profileSenderResponse
    (c : ContinuationProfile) (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (x a : ℝ) : ℝ :=
  (p.withProfile c).σ_dyn_top V_S x a

/-- **The Target's reduced objective at a profile**, in defiance.

Stage payoff at the Sender's profile response, plus the Target's profile-switched
continuation at the state that response induces. Written in defiance `d = 1 − a`
so that the mechanism comparisons all point upward. -/
noncomputable def reducedTargetObjective
    (c : ContinuationProfile)
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x d : ℝ) : ℝ :=
  p.U_T x (1 - d) (p.profileSenderResponse c V_S x (1 - d))
    + p.profileβ_T c *
        V_T (Sanctions.clipS'
          (p.F x (p.profileSenderResponse c V_S x (1 - d))))

/-! ## `C3` — the Sender-to-Target spillover

*A forward-looking Sender makes Target defiance more attractive.*

**Not derivable.** `suggestions/33` §4 states outright that "The baseline does
not imply this condition", and `Examples/SenderSwitchSignUndetermined.lean`
refutes the sign as a universal: the switch channel's contribution is genuinely
undetermined by the maintained primitives. This is the primitive-class version of
the unsigned Sender-switch channel, not a repair of it. -/

/-- **`C3`.** Increasing differences of the reduced Target objective in defiance
and the Sender's activation, at fixed Target activation.

**Cost if adopted:** excludes every economy in which a tougher anticipated
sanction schedule makes the Target *more* compliant — which is the intuitive
direction, and which the baseline permits. **What it would buy:** the
Sender-to-Target spillover `d⁰¹ ≥ d⁰⁰` and `d¹¹ ≥ d¹⁰`. **Not consumed
anywhere.** -/
def C3_SenderToTargetSpillover
    (tT : Bool) (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  ∀ dL ∈ Sanctions.I, ∀ dH ∈ Sanctions.I, dL ≤ dH →
    p.reducedTargetObjective ⟨tT, false⟩ V_T V_S x dH
        - p.reducedTargetObjective ⟨tT, false⟩ V_T V_S x dL
      ≤ p.reducedTargetObjective ⟨tT, true⟩ V_T V_S x dH
        - p.reducedTargetObjective ⟨tT, true⟩ V_T V_S x dL

/-! ## `C4` — the Target's own channel

*A Target that values the future political state finds defiance more attractive.*

**A misclassification corrected, 2026-08-30.** This docstring previously called
`DynamicVsMyopicIncreasingDifferencesAt`
(`Theory/LockIn/DifferentPolicyComparator.lean`) "the `11`-versus-`00` member of
this family," and cited the fact that no theorem discharges it as a measurement
of how hard `C4` is. **It is not a member of this family.** `C4` holds the
Sender's switch `tS` fixed, so its two members are `00`-versus-`10` and
`01`-versus-`11`. The `11`-versus-`00` comparison moves *both* switches at once,
so it varies `β_S` as well as `β_T` and belongs to no unilateral family.

The consequence is that the difficulty of `C4` is **unmeasured here**, not
measured and found high: as far as this file can establish, the actual `C4` may
never have been attempted. Any claim that closing `C4` would be a major win is
correspondingly unsupported, and should not be made on the strength of that
theorem's standing as an undischarged hypothesis. -/

/-- **`C4`.** Increasing differences in defiance and the Target's own activation,
at fixed Sender activation.

**Cost if adopted:** excludes economies where looking ahead makes the Target
*more* compliant — for instance where entrenchment is bad for the incumbent.
**What it would buy:** the direct Target effect `d¹⁰ ≥ d⁰⁰`, `d¹¹ ≥ d⁰¹`.
**Not consumed anywhere.** -/
def C4_TargetOwnChannel
    (tS : Bool) (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  ∀ dL ∈ Sanctions.I, ∀ dH ∈ Sanctions.I, dL ≤ dH →
    p.reducedTargetObjective ⟨false, tS⟩ V_T V_S x dH
        - p.reducedTargetObjective ⟨false, tS⟩ V_T V_S x dL
      ≤ p.reducedTargetObjective ⟨true, tS⟩ V_T V_S x dH
        - p.reducedTargetObjective ⟨true, tS⟩ V_T V_S x dL

/-! ## `C5` — the interaction primitive, and the one to be most careful with

*A Target that values its political future reacts more strongly to a Sender that
values its own.*

`suggestions/33` §4 records that this is "stronger than the two unilateral
monotonicity conditions". The sharper worry is that it is very close to the
conclusion it is meant to deliver. `C5` is the amplification claim stated on
*objectives*; the interaction result is the same claim stated on *outcomes*.
Either the step between them is substantial — in which case that step is the
contribution, and §6 concedes it is unproved — or it is thin, in which case the
theorem is near-circular. Neither branch has been established, and settling which
one holds should precede adoption. -/

/-- **`C5`.** Increasing differences between the two activation indicators: the
gain in defiance from the Target's own channel is larger when the Sender's
channel is also on.

Written as a single cross-difference inequality over the four profiles, which is
supermodularity of the reduced objective's defiance-increment in the two
switches.

**Cost if adopted:** it is the strongest of the five, it implies neither `C3` nor
`C4` and is implied by neither, and it constrains how two anticipations compound
— which no primitive of the model speaks to. **What it would buy:** the
interaction result. **Not consumed anywhere.**

**And note the target it buys is the wrong shape.**
`Mechanism.interaction_sign_not_scale_invariant` proves that the sign of a
sanction cross-difference reverses under `s ↦ s²`, a strictly increasing
relabelling that changes no economics. The invariant statement to aim at is
strict inclusion of the self-sustaining sets, which no cross-difference
condition is needed to reach. -/
def C5_ActivationComplementarity
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) : Prop :=
  ∀ dL ∈ Sanctions.I, ∀ dH ∈ Sanctions.I, dL ≤ dH →
    (p.reducedTargetObjective ContinuationProfile.p10 V_T V_S x dH
        - p.reducedTargetObjective ContinuationProfile.p10 V_T V_S x dL)
      - (p.reducedTargetObjective ContinuationProfile.p00 V_T V_S x dH
        - p.reducedTargetObjective ContinuationProfile.p00 V_T V_S x dL)
    ≤ (p.reducedTargetObjective ContinuationProfile.p11 V_T V_S x dH
        - p.reducedTargetObjective ContinuationProfile.p11 V_T V_S x dL)
      - (p.reducedTargetObjective ContinuationProfile.p01 V_T V_S x dH
        - p.reducedTargetObjective ContinuationProfile.p01 V_T V_S x dL)

/-! ## Relations among the three

The only relation provable without adopting anything is bookkeeping: `C5` is the
statement that `C4`'s increment is itself increasing in the Sender's switch. It
does **not** follow from `C3` and `C4` together, and neither follows from it —
which is exactly why `suggestions/33` lists it separately, and why adopting
`C3` and `C4` would not deliver the interaction. -/

/-- `C5` restated as monotonicity of the `C4` increment in the Sender's switch.
A rearrangement, proved so the reading is on the record rather than asserted. -/
theorem C5_iff_C4_increment_mono
    (V_T V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (x : ℝ) :
    p.C5_ActivationComplementarity V_T V_S x ↔
      ∀ dL ∈ Sanctions.I, ∀ dH ∈ Sanctions.I, dL ≤ dH →
        (p.reducedTargetObjective ContinuationProfile.p10 V_T V_S x dH
            - p.reducedTargetObjective ContinuationProfile.p00 V_T V_S x dH)
          - (p.reducedTargetObjective ContinuationProfile.p10 V_T V_S x dL
            - p.reducedTargetObjective ContinuationProfile.p00 V_T V_S x dL)
        ≤ (p.reducedTargetObjective ContinuationProfile.p11 V_T V_S x dH
            - p.reducedTargetObjective ContinuationProfile.p01 V_T V_S x dH)
          - (p.reducedTargetObjective ContinuationProfile.p11 V_T V_S x dL
            - p.reducedTargetObjective ContinuationProfile.p01 V_T V_S x dL) := by
  unfold C5_ActivationComplementarity
  constructor <;> intro h dL hdL dH hdH hd <;>
    (have := h dL hdL dH hdH hd; linarith)

end Params
end AbstractGame
end Sanctions
