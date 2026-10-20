/-
Sanctions/Examples/EquilibriumStrictReluctanceWitness.lean

**An economy where the forward-looking Target complies strictly less than every
myopic one, at a constructed equilibrium.**

Every Target-ordering result in the development concludes `α^FF(x) ≤ α^MM(x)`,
which is satisfied when the two regimes choose identically, so the whole family
was compatible with the reluctance channel being inert everywhere. This exhibits
an economy where it is not.

**Scope — read this before citing the file.** The comparison is between the two
*equilibrium concepts*: `E.α x` maximises the forward-looking Target integrand,
which is built on the dynamic Sender selector `σ_dyn_top E.V_S`, while `M.α x`
maximises the myopic objective built on the static `σ`. Those are formally
different objectives. **At this economy they are not numerically different on the
Sender side**: `maV_S = 0`, so the dynamic Sender problem is the static one, and
`ni_top_eq_ideal_of_mem` together with `niSigma = clipS ∘ niIdeal` gives
`σ_dyn_top maV_S = σ` wherever the Sender's ideal is feasible — which is the
whole action range at the pivot.

So what is witnessed here is the **Target-continuation** channel: the incumbent
holds out because compliance erodes the entrenchment it will want tomorrow. The
**Sender-response-switch** channel — the Target facing a genuinely tougher
forward-looking Sender — is *inert* at this economy, and remains unwitnessed
anywhere in the development, because every constructed equilibrium in the tree
carries a Sender value that is either identically zero or affine. Do not read
this file as evidence about that channel.

Here it is:

    α^FF(1/2) = 1/2   <   α^MM(1/2)   for every myopic equilibrium,

at `maParams` from `NonAffineMechanismActiveWitness.lean` — an economy whose
forward-looking equilibrium `maEquilibrium` is **constructed** from a solved
Bellman fixed point, over the **non-affine** transition `quadBumpF`.

## Why no wedge condition is assumed

The natural route to a cross-response ordering is through the total
forward-looking-minus-myopic wedge. That route is blocked at its root:
`SenderSwitchSignUndetermined.lean` proves the Sender-response-switch half of
that wedge has no sign determined by the model's primitives, so assuming the
wedge falls would be assuming exactly what cannot be derived.

`alpha_lt_myopic_of_myopic_improves_above` takes the other road and asks nothing
about the wedge. It needs only two facts about the **myopic** objective
`a ↦ U_T(x, a, σ(x,a))` relative to the forward-looking equilibrium action:
nothing weakly below it is myopically better, and something is myopically
strictly better. Both are checked here by exact arithmetic.

## The economics

`maU_T` charges the Target a current cost `−(9/10)·clipS(F(x,s))` for the
political state its sanction induces. In the forward-looking regime the
continuation value restores that cost, and the Target settles at `1/2`. The
myopic Target sees only the charge. A lighter sanction means a lower successor
state and a smaller charge, and compliance is what buys a lighter sanction — so
the myopic incumbent complies **more**, to `≈ 0.556`.

That is the reluctance mechanism running in the intended direction: looking
ahead makes the incumbent hold out, because the compliance that buys relief
today also erodes the entrenchment it will want tomorrow.

## Why the two hypotheses hold, structurally

At `x = 1/2` the Sender's response is `σ(1/2,a) = 7/8 − a/4`, and the sanction
terms in `niU_T` cancel against the ideal, leaving

    myopic objective (a) = −(a − 1/2)² + 1/2 − (9/10) · F(1/2, 7/8 − a/4).

Below `1/2` **both** terms move the wrong way for the myopic Target: the square
is negative, and since `σ` falls in compliance while `F` rises in the sanction,
the successor state — and so the charge — is *larger* at lower compliance. So no
action weakly below `1/2` beats `1/2`, and that is `h_best_below`, proved from
monotonicity rather than from a numeric sweep.

Above `1/2` the linear relief from the shrinking charge beats the quadratic loss
until about `0.556`. `a' = 11/20` is a clean rational inside that range, with an
exact margin of `1603771/512000000 > 0`.

## Rule 9A: what this licenses

Existence, and nothing more. It shows the cross-response reluctance channel is
active *somewhere*, over a transition that is not affine for any `δ`. It says
nothing about genericity, about how large the gap typically is, or about whether
the channel must be active. The Python search and exact re-verification are in
`docs/archive/workflow-scratch/cross_witness.py`.

The conclusion is quantified over **every** `MyopicFeedbackEquilibrium` of this
economy, so it is selection-proof: it does not depend on which myopic maximizer
the canonical construction happens to pick.
-/

import Sanctions.Examples.NonAffineMechanismActiveWitness
import Sanctions.Theory.LockIn.TwoSidedForwardLooking

namespace Sanctions
namespace Examples

open Set AbstractGame

noncomputable section

/-! ## 1. The myopic objective at the pivot, in closed form -/

/-- The Sender's static response at the pivot, on the feasible action range.
`niIdeal (1/2) a = 7/8 − a/4` lands in `[5/8, 7/8]`, so the clip is inert. -/
theorem ma_sigma_at_pivot {a : ℝ} (ha : a ∈ Sanctions.I) :
    maParams.σ (1 / 2) a = 7 / 8 - a / 4 := by
  have hmem : niIdeal (1 / 2) a ∈ Set.Icc (0 : ℝ) 1 := by
    unfold niIdeal
    constructor <;> [linarith [ha.2]; linarith [ha.1]]
  show niSigma (1 / 2) a = 7 / 8 - a / 4
  unfold niSigma
  rw [clipS_of_mem hmem]
  unfold niIdeal
  ring

/-- The induced sanction is feasible, so the successor state is too. -/
theorem ma_sigma_at_pivot_mem {a : ℝ} (ha : a ∈ Sanctions.I) :
    maParams.σ (1 / 2) a ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ma_sigma_at_pivot ha]
  constructor <;> [linarith [ha.2]; linarith [ha.1]]

/-- **The myopic objective at the pivot.** The sanction term in `niU_T` cancels
against the ideal, leaving a quadratic loss in compliance and the political
charge on the successor state. -/
theorem ma_myopic_objective_at_pivot {a : ℝ} (ha : a ∈ Sanctions.I) :
    maParams.U_T (1 / 2) a (maParams.σ (1 / 2) a)
      = -(a - 1 / 2) ^ 2 + 1 / 2
        - 9 / 10 * quadBumpF (1 / 2) (maParams.σ (1 / 2) a) := by
  have hs := ma_sigma_at_pivot_mem ha
  have hx : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hq : quadBumpF (1 / 2) (maParams.σ (1 / 2) a) ∈ Set.Icc (0 : ℝ) 1 :=
    quadBumpF_mem _ _ hx hs
  show maU_T (1 / 2) a (maParams.σ (1 / 2) a) = _
  unfold maU_T niU_T
  rw [clipS_of_mem hq, ma_sigma_at_pivot ha]
  unfold niIdeal
  ring

/-! ## 2. The two hypotheses of the general theorem -/

/-- **Nothing weakly below the forward-looking action is myopically better.**

Proved from monotonicity, not from a sweep: below `1/2` the quadratic term is
negative, and the Sender's response is *higher* (compliance placates, so less
compliance means a harsher sanction), which by `quadBumpF_mono_s` makes the
successor state and hence the political charge larger. Both effects push the
myopic objective down. -/
theorem ma_myopic_best_below_pivot :
    ∀ a ∈ Sanctions.I, a ≤ 1 / 2 →
      maParams.U_T (1 / 2) a (maParams.σ (1 / 2) a)
        ≤ maParams.U_T (1 / 2) (1 / 2) (maParams.σ (1 / 2) (1 / 2)) := by
  intro a ha hle
  have hhalf : (1 / 2 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  rw [ma_myopic_objective_at_pivot ha, ma_myopic_objective_at_pivot hhalf]
  -- the induced sanction is weakly higher at the lower compliance ...
  have hsig : maParams.σ (1 / 2) (1 / 2) ≤ maParams.σ (1 / 2) a := by
    rw [ma_sigma_at_pivot ha, ma_sigma_at_pivot hhalf]
    linarith
  -- ... so the successor state, and the charge on it, is weakly larger
  have hF : quadBumpF (1 / 2) (maParams.σ (1 / 2) (1 / 2))
              ≤ quadBumpF (1 / 2) (maParams.σ (1 / 2) a) :=
    quadBumpF_mono_s _ hsig
  nlinarith [sq_nonneg (a - 1 / 2)]

/-- **Something is myopically strictly better**, namely `a' = 11/20`. The exact
margin is `1603771/512000000`. -/
theorem ma_myopic_better_above_pivot :
    maParams.U_T (1 / 2) (1 / 2) (maParams.σ (1 / 2) (1 / 2))
      < maParams.U_T (1 / 2) (11 / 20) (maParams.σ (1 / 2) (11 / 20)) := by
  have hhalf : (1 / 2 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  have hap : (11 / 20 : ℝ) ∈ Sanctions.I := ⟨by norm_num, by norm_num⟩
  rw [ma_myopic_objective_at_pivot hhalf, ma_myopic_objective_at_pivot hap,
    ma_sigma_at_pivot hhalf, ma_sigma_at_pivot hap]
  rw [quadBumpF_sq ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩,
    quadBumpF_sq ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩]
  norm_num

/-! ## 3. The witness -/

/-- **The forward-looking Target complies strictly less than every myopic one.**

At the constructed equilibrium `maEquilibrium` over the non-affine transition
`quadBumpF`, the forward-looking Target complies `1/2` while every myopic
equilibrium of the *same economy* complies strictly more.

Rule 9A: this licenses existence — the cross-response reluctance channel is
active somewhere — and nothing about genericity, magnitude, or necessity. -/
theorem ma_forwardLooking_complies_strictly_less
    (M : maParams.MyopicFeedbackEquilibrium) :
    maEquilibrium.α (1 / 2) < M.α (1 / 2) := by
  have hx : (1 / 2 : ℝ) ∈ Sanctions.S := ⟨by norm_num, by norm_num⟩
  have hα : maEquilibrium.α (1 / 2) = 1 / 2 := rfl
  have h := maParams.alpha_lt_myopic_of_myopic_improves_above
    maEquilibrium M (a' := 11 / 20) hx ⟨by norm_num, by norm_num⟩
    (by rw [hα]; exact ma_myopic_best_below_pivot)
    (by rw [hα]; exact ma_myopic_better_above_pivot)
  exact h

/-- **The witness, assembled.** A non-affine transition, a constructed
forward-looking equilibrium, and a strict cross-response compliance gap holding
for every myopic equilibrium of the same economy. -/
theorem equilibrium_strict_reluctance_witness :
    (∀ δ : ℝ, maParams.F ≠ AbstractGame.affineF δ)
    ∧ maEquilibrium.α (1 / 2) = 1 / 2
    ∧ ∀ M : maParams.MyopicFeedbackEquilibrium,
        maEquilibrium.α (1 / 2) < M.α (1 / 2) :=
  ⟨fun δ => by simpa only [maParams_F] using quadBumpF_ne_affineF δ, rfl,
    fun M => ma_forwardLooking_complies_strictly_less M⟩

end

end Examples
end Sanctions
