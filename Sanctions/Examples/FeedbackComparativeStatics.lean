/-
Sanctions/Examples/FeedbackComparativeStatics.lean

**Wave-6 P11: equilibrium-feedback comparative statics via pinned fixed
points (the Acemoglu-Jensen full-adjustment channel at the corner witness
families).**

This file closes — AT the corner-policy witness families — the channel
recorded open at `Theory/LockIn/LockInComparativeStatics.lean:47-48`:
comparative statics WITH equilibrium re-adjustment of the value functions.
The route is the pinned-fixed-point device of
`Examples/FourGroupPlannerWitness.lean` (§6), parametrized in the deep
parameter: at `eeCertParams` and `fgcParams` the equilibrium value
coefficients are exact rational functions of `(β_S, β_T, δ)`, so the FULL
adjustment derivative — direct effect at fixed `(V, α)` PLUS the
re-pinning of the equilibrium value — is closed-form. No IFT machinery;
zero new assumptions (every theorem carries only window-membership
hypotheses on Examples-layer families).

Contents (all windows exact and binding-constraint-named):

1. Three-parameter witness families `eeCertParamsGen` / `fgcParamsGen`
   (payoffs fixed, `(β_S, β_T, δ)` free) with the general Sender/Target
   corner cascade: strict monotonicity, `σ_dyn` corner pins, state-local
   Sender argmax uniqueness, and both Bellman images in closed form.
2. The eeCert `β_S`-family on the exact persistence window
   `β_S ∈ [6/13, 4/7)` — binding below: the all-compliance corner chord
   `4β/(2−β) ≥ 6/5` (closed endpoint admissible: chord strictness comes
   from `s₁ < s₂`); binding above: the STRICT certificate margin
   `β·K_S·δ < m_S = 8/5`. Pinned fixed point
   `V_S*(x;β) = (6+5β)/(2(1−β)(2−β)) + 8/(2−β)·x`, reproducing the
   shipped pin `(17/3, 16/3)` at `β = 1/2`.
3. FULL-adjustment derivatives at `β = 1/2`: slope `32/9`, intercept
   `166/9`, lock-in value `22`; DIRECT effect (one Bellman application at
   the frozen old fixed point): `8/3`, `25/3`, `11`; FEEDBACK = full −
   direct: `+8/9`, `+91/9`, `+11` — all strictly positive, with the
   amplification identity `full = direct/(1−β)` at the absorbing state,
   the exact finite-difference decomposition
   `ΔV = Δβ·V₂∘F [direct] + β₁·ΔV∘F [feedback]`, resolvent identities
   `c'(β) = (c/2)/(1−β/2)`, `dV*(1)/dβ = V*(1)/(1−β)`, and Rule-16(a)
   ordered-endpoint corollaries at `β = 1/2 < 11/20`.
4. The eeCert `δ`-channel on `δ ∈ [3/7, 2/3)`: the STRIKING result
   `dV*(1)/dδ = 0` EXACTLY (`eeCertD_lockin_value_invariant`) — the
   lock-in value is the capitalized `δ`-free corner flow; slope and
   intercept move (`∓32/9`) and offset exactly at `x = 1`.
5. Cross-feedback decoupling `dV_T*/dβ_S ≡ 0` (the SAME `V_T*` is the
   pinned Target fixed point at every `β_S` in the window), and the
   eeCert `β_T`-channel on `[598/709, 1)`: `dV_T*(1)/dβ_T = 110 =
   direct 11 + feedback 99` (amplification factor 10).
6. The `fourGroupCert` siblings (both players): Sender `β_S`-family on
   the FULL window `[0,1)` — the fgc corner pin is proved at `a = 0`
   only (see `FourGroupCertWitness.lean:36`) where the stage chord is
   `≥ 1 > 0` for every `β`, and the margin crosses only above `β = 1`;
   Target `β_T`-family on `[14/17, 1)` (the leader chord-decomposition
   coefficient IS the loss-margin quantity, so one binding constraint
   serves both); `δ`-family on `[7/27, 1)` with BOTH lock-in values
   `δ`-invariant exactly (`V_S*(1) ≡ 5`, `V_T*(1) ≡ 12`).

**Honest boundary.** At these corner families the policy-response term
of the Acemoglu-Jensen derivative is exactly ZERO: the argmax never
moves on the window (`σ_dyn ≡ 1` at eeCert / `σ_dyn(·,0) = 1` at fgc,
`α_on ≡ 0` uniformly), so the whole feedback lives in the value
re-pinning. The interior-policy feedback channel — where `dσ*/dθ ≠ 0`,
cross-feedback through `σ_dyn` comes alive, and argmax selection needs
IFT/MCS machinery — remains OPEN and connects to the P9 envelope layer
(the mechanism-active interior equilibrium is a known order-reversal
cycle; see the honest-scope notes in `docs/archive/workflow-scratch/w6_p11_spec.md` §5).

Rule 3: zero new assumptions. Rule 5: every witness-level number is a
one-line specialization of a `(β,δ)`-parametric family lemma.
-/

import Sanctions.Examples.FourGroupPlannerWitness
import Sanctions.Foundations.PatienceDecomposition
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Sanctions.Examples.AffineInstance.Microfoundations
import Sanctions.Theory.LockIn.LockInComparativeStatics

namespace Sanctions

/-! ## 0′. The corner lock-in trio for any stage payoff; the Target trio

**General in `F` (Rule 22); BH6.3, 2026-10-07.** The Sender trio
`senderValue_lockin_{amplification,capitalised,strict_iff}_of_bellman`
(`Theory/LockIn/LockInComparativeStatics.lean`, Phase 3) reads the Sender's
stage payoff only as the flow `U_S(y, a, 1)` of the corner Bellman equation
`V(y) = U_S(y, a, 1) + β·V(F(y, 1))` (the Sender at the full-sanction corner,
the Target at a constant compliance `a`), and the transition only through
`F_diag`, which makes the top state absorbing at full sanction
(`clipS'_top_fixed_of_sanction_one`). The three `cornerValue_*` theorems below
take the stage payoff as an argument `u`, so they hold for either player; the
`targetValue_*` trio is the instance `u := p.U_T`, and the Sender trio is the
instance `u := p.U_S`. Hence `V*(1) = U(1, a, 1)/(1 − β)` for both players and
every transition. Two consequences for the witness families below:

* the Target `β_T`-channel amplification identities `eeCertBT_lockin_amplification`
  and `fgcBT_lockin_amplification` are instances of
  `targetValue_lockin_amplification_of_bellman` at the pinned Target fixed point;
* the "`δ`-invariance" of the lock-in value at the `δ`-families
  (`eeCertD_lockin_value_invariant`, `fgcD_VS_lockin_invariant`,
  `fgcD_VT_lockin_invariant`) is what the capitalisation theorem predicts:
  invariance to the whole transition law, not only to `δ`. Those three lemmas
  are kept as they are — they are the coefficient algebra the pinned fixed points
  are built from, so deriving them from the trio would be circular.

These are `Params`-level statements with no witness content. They sit in this
file beside their consumers; their natural home is Phase 3 of
`LockInComparativeStatics.lean`, beside the Sender trio. Rule 15: the Bellman
equations are consumed, not constructed (`_of_bellman`). -/

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Corner lock-in amplification, for any stage payoff.** Two value functions
solving the corner Bellman equation `V(y) = u(y, a, 1) + β·V(F(y, 1))` — the
Sender at full sanction, the Target at a constant compliance `a` — with the same
stage payoff `u` and transition `p.F` but discount factors `β₁`, `β₂`, satisfy at
the absorbing top state `(1 − β₁)·(V₂(1) − V₁(1)) = (β₂ − β₁)·V₂(1)`: the full
response to patience is the direct response amplified by `1/(1 − β₁)`.

Rule 22: general in `F` (only `F_diag`, through
`clipS'_top_fixed_of_sanction_one`). Stage-payoff-generic form of
`senderValue_lockin_amplification_of_bellman`: the Sender's `p.U_S` is replaced
by any `u`; no hypothesis is added. -/
theorem cornerValue_lockin_amplification_of_bellman
    (u : ℝ → ℝ → ℝ → ℝ) (a : ℝ) {β₁ β₂ : ℝ} {V₁ V₂ : ↥(Sanctions.S : Set ℝ) → ℝ}
    (h₁ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₁ y = u y.val a 1 + β₁ * V₁ (Sanctions.clipS' (p.F y.val 1)))
    (h₂ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₂ y = u y.val a 1 + β₂ * V₂ (Sanctions.clipS' (p.F y.val 1))) :
    (1 - β₁) * (V₂ (⟨1, by constructor <;> norm_num⟩ :
          ↥(Sanctions.S : Set ℝ))
        - V₁ (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ)))
      = (β₂ - β₁) * V₂ (⟨1, by constructor <;> norm_num⟩ :
          ↥(Sanctions.S : Set ℝ)) :=
  Sanctions.PatienceDecomposition.amplification_at_fixedPoint
    (u := fun w : ↥(Sanctions.S : Set ℝ) => u w.val a 1)
    (z := fun w : ↥(Sanctions.S : Set ℝ) => Sanctions.clipS' (p.F w.val 1))
    h₁ h₂ (p.clipS'_top_fixed_of_sanction_one)

/-- **The corner lock-in value is the corner flow capitalised, for any stage
payoff.** A solution of the corner Bellman equation
`V(y) = u(y, a, 1) + β·V(F(y, 1))` with `β ≠ 1` has `V(1) = u(1, a, 1)/(1 − β)`.

Rule 22: general in `F` (only `F_diag`). Stage-payoff-generic form of
`senderValue_lockin_capitalised_of_bellman`: `p.U_S` is replaced by any `u`; no
hypothesis is added. -/
theorem cornerValue_lockin_capitalised_of_bellman
    (u : ℝ → ℝ → ℝ → ℝ) (a : ℝ) {β : ℝ} {V : ↥(Sanctions.S : Set ℝ) → ℝ}
    (h : ∀ y : ↥(Sanctions.S : Set ℝ),
      V y = u y.val a 1 + β * V (Sanctions.clipS' (p.F y.val 1)))
    (hβ : β ≠ 1) :
    V (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
      = u 1 a 1 / (1 - β) :=
  Sanctions.PatienceDecomposition.value_at_fixedPoint
    (u := fun w : ↥(Sanctions.S : Set ℝ) => u w.val a 1)
    (z := fun w : ↥(Sanctions.S : Set ℝ) => Sanctions.clipS' (p.F w.val 1))
    h (p.clipS'_top_fixed_of_sanction_one) hβ

/-- **More patience raises the corner lock-in value exactly when the corner flow
is positive, for any stage payoff.** For two solutions of the corner Bellman
equation at `β₁ < β₂ < 1`, `V₁(1) < V₂(1) ↔ 0 < u(1, a, 1)`.

Rule 22: general in `F` (only `F_diag`). Stage-payoff-generic form of
`senderValue_lockin_strict_iff_of_bellman`: `p.U_S` is replaced by any `u`; no
hypothesis is added. -/
theorem cornerValue_lockin_strict_iff_of_bellman
    (u : ℝ → ℝ → ℝ → ℝ) (a : ℝ) {β₁ β₂ : ℝ} {V₁ V₂ : ↥(Sanctions.S : Set ℝ) → ℝ}
    (h₁ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₁ y = u y.val a 1 + β₁ * V₁ (Sanctions.clipS' (p.F y.val 1)))
    (h₂ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₂ y = u y.val a 1 + β₂ * V₂ (Sanctions.clipS' (p.F y.val 1)))
    (hβ₁ : β₁ < 1) (hlt : β₁ < β₂) (hβ₂ : β₂ < 1) :
    V₁ (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
        < V₂ (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
      ↔ 0 < u 1 a 1 :=
  Sanctions.PatienceDecomposition.strict_at_fixedPoint_iff
    (u := fun w : ↥(Sanctions.S : Set ℝ) => u w.val a 1)
    (z := fun w : ↥(Sanctions.S : Set ℝ) => Sanctions.clipS' (p.F w.val 1))
    h₁ h₂ (p.clipS'_top_fixed_of_sanction_one) hβ₁ hlt hβ₂

/-- **Target lock-in amplification.** Two Target value functions solving the
Target corner Bellman equation `V(y) = U_T(y, a, 1) + β·V(F(y, 1))` — the Sender
at full sanction, the Target at a constant compliance `a` — at discount factors
`β₁`, `β₂` satisfy `(1 − β₁)·(V₂(1) − V₁(1)) = (β₂ − β₁)·V₂(1)` at the lock-in
state: the Target's full response to its own patience is the direct response
amplified by `1/(1 − β₁)`.

Rule 22: general in `F`. The Target sibling of
`senderValue_lockin_amplification_of_bellman`, as the instance `u := p.U_T` of
`cornerValue_lockin_amplification_of_bellman`; no hypothesis is added. -/
theorem targetValue_lockin_amplification_of_bellman
    (a : ℝ) {β₁ β₂ : ℝ} {V₁ V₂ : ↥(Sanctions.S : Set ℝ) → ℝ}
    (h₁ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₁ y = p.U_T y.val a 1 + β₁ * V₁ (Sanctions.clipS' (p.F y.val 1)))
    (h₂ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₂ y = p.U_T y.val a 1 + β₂ * V₂ (Sanctions.clipS' (p.F y.val 1))) :
    (1 - β₁) * (V₂ (⟨1, by constructor <;> norm_num⟩ :
          ↥(Sanctions.S : Set ℝ))
        - V₁ (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ)))
      = (β₂ - β₁) * V₂ (⟨1, by constructor <;> norm_num⟩ :
          ↥(Sanctions.S : Set ℝ)) :=
  p.cornerValue_lockin_amplification_of_bellman p.U_T a h₁ h₂

/-- **The Target lock-in value is the Target corner flow capitalised.** A
solution of the Target corner Bellman equation with `β ≠ 1` has
`V(1) = U_T(1, a, 1)/(1 − β)`, for every transition.

Rule 22: general in `F`. The Target sibling of
`senderValue_lockin_capitalised_of_bellman`, as the instance `u := p.U_T` of
`cornerValue_lockin_capitalised_of_bellman`; no hypothesis is added. -/
theorem targetValue_lockin_capitalised_of_bellman
    (a : ℝ) {β : ℝ} {V : ↥(Sanctions.S : Set ℝ) → ℝ}
    (h : ∀ y : ↥(Sanctions.S : Set ℝ),
      V y = p.U_T y.val a 1 + β * V (Sanctions.clipS' (p.F y.val 1)))
    (hβ : β ≠ 1) :
    V (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
      = p.U_T 1 a 1 / (1 - β) :=
  p.cornerValue_lockin_capitalised_of_bellman p.U_T a h hβ

/-- **More Target patience raises the Target lock-in value exactly when the
Target's corner flow is positive.** For two solutions of the Target corner
Bellman equation at `β₁ < β₂ < 1`, `V₁(1) < V₂(1) ↔ 0 < U_T(1, a, 1)`.

Rule 22: general in `F`. The Target sibling of
`senderValue_lockin_strict_iff_of_bellman`, as the instance `u := p.U_T` of
`cornerValue_lockin_strict_iff_of_bellman`; no hypothesis is added. -/
theorem targetValue_lockin_strict_iff_of_bellman
    (a : ℝ) {β₁ β₂ : ℝ} {V₁ V₂ : ↥(Sanctions.S : Set ℝ) → ℝ}
    (h₁ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₁ y = p.U_T y.val a 1 + β₁ * V₁ (Sanctions.clipS' (p.F y.val 1)))
    (h₂ : ∀ y : ↥(Sanctions.S : Set ℝ),
      V₂ y = p.U_T y.val a 1 + β₂ * V₂ (Sanctions.clipS' (p.F y.val 1)))
    (hβ₁ : β₁ < 1) (hlt : β₁ < β₂) (hβ₂ : β₂ < 1) :
    V₁ (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
        < V₂ (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
      ↔ 0 < p.U_T 1 a 1 :=
  p.cornerValue_lockin_strict_iff_of_bellman p.U_T a h₁ h₂ hβ₁ hlt hβ₂

end Params
end AbstractGame

namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.AbstractGame.Params

noncomputable section

/-! ## 0. Shared membership plumbing -/

theorem mem_910_Ico : (9/10 : ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩

theorem mem_half_Ico : (1/2 : ℝ) ∈ Set.Ico (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩

theorem mem_half_Ioo : (1/2 : ℝ) ∈ Set.Ioo (0:ℝ) 1 := ⟨by norm_num, by norm_num⟩

/-- The half-step transition point `(y+1)/2` stays in the state cube. -/
theorem mem_half_shift (y : ↥(Sanctions.S : Set ℝ)) :
    (y.val + 1)/2 ∈ Set.Icc (0:ℝ) 1 :=
  ⟨by linarith [y.property.1], by linarith [y.property.2]⟩

/-- The corner transition point `(1−d)·x + d` stays in the state cube. -/
theorem mem_affine_corner {d : ℝ} (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (1 - d) * x + d ∈ Set.Icc (0:ℝ) 1 := by
  have h := AbstractGame.affineF_mem hd x 1 hx ⟨by norm_num, le_refl 1⟩
  simpa [AbstractGame.affineF] using h

/-! ## 1. The three-parameter witness families

Payoffs, static selector, and basin geometry are FIXED at the shipped
witness values; only the deep parameters `(β_S, β_T, δ)` move. Rule 5:
each 1-D channel below is an instance of these single general families. -/

/-- **The eeCert family**: `eeCertParams` with `(β_S, β_T, δ)` free
(payoffs `eecU_S`/`eecU_T`, selector `eecσ`, affine transition). -/
def eeCertParamsGen (βS βT d : ℝ) (hβS : βS ∈ Set.Ico (0:ℝ) 1)
    (hβT : βT ∈ Set.Ico (0:ℝ) 1) (hd : d ∈ Set.Ioo (0:ℝ) 1) :
    AbstractGame.Params :=
  { eeCertParams with
    δ := d
    δ_mem := hd
    β_T := βT
    β_T_mem := hβT
    β_S := βS
    β_S_mem := hβS
    F := AbstractGame.affineF d
    F_continuous := AbstractGame.affineF_continuous d
    F_mono_x := AbstractGame.affineF_mono_x hd
    F_mono_s := AbstractGame.affineF_mono_s hd
    F_diag := AbstractGame.affineF_diag d }

@[simp] theorem eeCertParamsGen_U_S (βS βT d : ℝ)
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) :
    (eeCertParamsGen βS βT d hβS hβT hd).U_S = eecU_S := rfl

@[simp] theorem eeCertParamsGen_U_T (βS βT d : ℝ)
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) :
    (eeCertParamsGen βS βT d hβS hβT hd).U_T = eecU_T := rfl

@[simp] theorem eeCertParamsGen_β_S (βS βT d : ℝ)
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) :
    (eeCertParamsGen βS βT d hβS hβT hd).β_S = βS := rfl

@[simp] theorem eeCertParamsGen_β_T (βS βT d : ℝ)
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) :
    (eeCertParamsGen βS βT d hβS hβT hd).β_T = βT := rfl

@[simp] theorem eeCertParamsGen_δ (βS βT d : ℝ)
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) :
    (eeCertParamsGen βS βT d hβS hβT hd).δ = d := rfl

@[simp] theorem eeCertParamsGen_F (βS βT d : ℝ)
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) (x s : ℝ) :
    (eeCertParamsGen βS βT d hβS hβT hd).F x s = (1 - d) * x + d * s := rfl

/-- Sanity: the shipped witness is the `(1/2, 9/10, 1/2)` member. -/
example :
    eeCertParamsGen (1/2) (9/10) (1/2) mem_half_Ico mem_910_Ico mem_half_Ioo
      = eeCertParams := rfl

/-- **The fgc family**: the microfounded four-group polity with
`(β_S, β_T, δ)` free (all stage payoffs still DERIVED from
`fourGroupCert` via `FourGroup.toParams`). -/
def fgcParamsGen (βS βT d : ℝ) (hβS : βS ∈ Set.Ico (0:ℝ) 1)
    (hβT : βT ∈ Set.Ico (0:ℝ) 1) (hd : d ∈ Set.Ioo (0:ℝ) 1) :
    AbstractGame.Params :=
  fourGroupCert.toParams d βT βS hd hβT hβS

@[simp] theorem fgcParamsGen_U_S (βS βT d : ℝ)
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) (x a s : ℝ) :
    (fgcParamsGen βS βT d hβS hβT hd).U_S x a s
      = (2 + x) * s - 1/2 * s ^ 2 - 11/5 * s * a := by
  show fourGroupCert.U_S x a s = _
  simp only [KaempferLowenberg.FourGroup.U_S, fourGroupCert]
  ring

@[simp] theorem fgcParamsGen_U_T (βS βT d : ℝ)
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) (x a s : ℝ) :
    (fgcParamsGen βS βT d hβS hβT hd).U_T x a s
      = 3 * x - 1/5 * a + s * (x - 14/5) := by
  show fourGroupCert.U_T x a s = _
  simp only [KaempferLowenberg.FourGroup.U_T, fourGroupCert]
  ring

@[simp] theorem fgcParamsGen_β_S (βS βT d : ℝ)
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) :
    (fgcParamsGen βS βT d hβS hβT hd).β_S = βS := rfl

@[simp] theorem fgcParamsGen_β_T (βS βT d : ℝ)
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) :
    (fgcParamsGen βS βT d hβS hβT hd).β_T = βT := rfl

@[simp] theorem fgcParamsGen_F (βS βT d : ℝ)
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) (x s : ℝ) :
    (fgcParamsGen βS βT d hβS hβT hd).F x s = (1 - d) * x + d * s := rfl

/-- Sanity: the shipped microfounded witness is the `(1/2, 9/10, 1/2)`
member. -/
example :
    fgcParamsGen (1/2) (9/10) (1/2) mem_half_Ico mem_910_Ico mem_half_Ioo
      = fgcParams := rfl

/-! ## 2. The general eeCert corner cascade

All lemmas are stated over an abstract carrier slope `c` with the chord
hypothesis `6/5 ≤ β_S·c·δ` where one is needed (the all-compliance pin);
at instantiation the hypothesis is discharged from the window membership,
so no new assumption enters any final family theorem. -/

/-- **Sender dynamic objective strictly increasing at the defiance
policy `a = 0`** — chord `2 + x − (s₁+s₂)/2 ≥ 1 > 0` plus a nonnegative
continuation, so NO window condition is needed. This is the engine for
the Bellman image at `α ≡ 0` (and for the direct-effect evaluations at
frozen carriers). -/
theorem eeGen_senderObj_strictMonoOn_zero {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {c M : ℝ} (hc : 0 ≤ c) {V_S : Val} (hV_S : V_S ∈ valLipGainBall M c c 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    StrictMonoOn
      (fun s => (eeCertParamsGen βS βT d hβS hβT hd).U_S x 0 s
        + (eeCertParamsGen βS βT d hβS hβT hd).β_S
          * V_S (Sanctions.clipS'
              ((eeCertParamsGen βS βT d hβS hβT hd).F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hmem₁ : (1 - d) * x + d * s₁ ∈ Set.Icc (0:ℝ) 1 :=
    AbstractGame.affineF_mem hd x s₁ hx hs₁
  have hmem₂ : (1 - d) * x + d * s₂ ∈ Set.Icc (0:ℝ) 1 :=
    AbstractGame.affineF_mem hd x s₂ hx hs₂
  have hdiff := gainBall_clip_diff hc hV_S hmem₁ hmem₂
  simp only [eeCertParamsGen_U_S, eeCertParamsGen_β_S, eeCertParamsGen_F,
    eecU_S]
  have hVdiff : βS * (V_S (Sanctions.clipS' ((1 - d) * x + d * s₂))
        - V_S (Sanctions.clipS' ((1 - d) * x + d * s₁)))
      = βS * c * d * (s₂ - s₁) := by
    rw [hdiff]; ring
  have hVpos : (0:ℝ) ≤ βS * c * d * (s₂ - s₁) :=
    mul_nonneg (mul_nonneg (mul_nonneg hβS.1 hc) hd.1.le) (by linarith)
  have hcoef : (0:ℝ) < 2 + x - (s₁ + s₂)/2 := by
    linarith [hx.1, hs₁.2, hs₂.2]
  have hprod := mul_pos (show (0:ℝ) < s₂ - s₁ by linarith) hcoef
  nlinarith [hVdiff, hVpos, hprod]

/-- **Sender dynamic objective strictly increasing at EVERY compliance
level** — needs the all-compliance chord `6/5 ≤ β_S·c·δ` (the
binding-below window constraint). The CLOSED window endpoint is
admissible because the residual strictness comes from `s₁ < s₂ ≤ 1`
(so `(s₁+s₂)/2 < 1` strictly). -/
theorem eeGen_senderObj_strictMonoOn {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {c M : ℝ} (hc : 0 ≤ c) (hchord : 6/5 ≤ βS * c * d)
    {V_S : Val} (hV_S : V_S ∈ valLipGainBall M c c 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    StrictMonoOn
      (fun s => (eeCertParamsGen βS βT d hβS hβT hd).U_S x a s
        + (eeCertParamsGen βS βT d hβS hβT hd).β_S
          * V_S (Sanctions.clipS'
              ((eeCertParamsGen βS βT d hβS hβT hd).F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hmem₁ : (1 - d) * x + d * s₁ ∈ Set.Icc (0:ℝ) 1 :=
    AbstractGame.affineF_mem hd x s₁ hx hs₁
  have hmem₂ : (1 - d) * x + d * s₂ ∈ Set.Icc (0:ℝ) 1 :=
    AbstractGame.affineF_mem hd x s₂ hx hs₂
  have hdiff := gainBall_clip_diff hc hV_S hmem₁ hmem₂
  simp only [eeCertParamsGen_U_S, eeCertParamsGen_β_S, eeCertParamsGen_F,
    eecU_S]
  have hVdiff : βS * (V_S (Sanctions.clipS' ((1 - d) * x + d * s₂))
        - V_S (Sanctions.clipS' ((1 - d) * x + d * s₁)))
      = βS * c * d * (s₂ - s₁) := by
    rw [hdiff]; ring
  have hcoef : (0:ℝ) < 16/5 - 11/5 * a + x - (s₁ + s₂)/2 := by
    linarith [ha.2, hx.1, hs₂.2, hlt]
  have hprod := mul_pos (show (0:ℝ) < s₂ - s₁ by linarith) hcoef
  have hβc : 6/5 * (s₂ - s₁) ≤ βS * c * d * (s₂ - s₁) :=
    mul_le_mul_of_nonneg_right hchord (by linarith)
  nlinarith [hVdiff, hprod, hβc]

/-- `σ_dyn` pinned at the corner `1` at every compliance level (needs
the all-compliance chord). -/
theorem eeGen_σ_dyn_eq_one {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {c M : ℝ} (hc : 0 ≤ c) (hchord : 6/5 ≤ βS * c * d)
    {V_S : Val} (hV_S : V_S ∈ valLipGainBall M c c 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (eeCertParamsGen βS βT d hβS hβT hd).σ_dyn V_S x a = 1 :=
  WitnessKit.σ_dyn_eq_one_of_strictMonoOn
    (eeGen_senderObj_strictMonoOn hβS hβT hd hc hchord hV_S hx ha)

/-- `σ_dyn_top` (the upper selector the top equilibrium's realized rule
uses) pinned at the corner `1` at every compliance level. -/
theorem eeGen_σ_dyn_top_eq_one {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {c M : ℝ} (hc : 0 ≤ c) (hchord : 6/5 ≤ βS * c * d)
    {V_S : Val} (hV_S : V_S ∈ valLipGainBall M c c 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (eeCertParamsGen βS βT d hβS hβT hd).σ_dyn_top V_S x a = 1 :=
  WitnessKit.σ_dyn_top_eq_one_of_strictMonoOn
    (eeGen_senderObj_strictMonoOn hβS hβT hd hc hchord hV_S hx ha)

/-- **State-local Sender argmax uniqueness on any slope-pinned
carrier** — the objective is a strictly concave parabola for every
`(β_S, β_T, δ)`; no window condition. -/
theorem eeGen_DAU_on_carrier {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {c M : ℝ} (hc : 0 ≤ c) {V_S : Val} (hV_S : V_S ∈ valLipGainBall M c c 0) :
    (eeCertParamsGen βS βT d hβS hβT hd).DynamicArgmaxUnique V_S := by
  apply (eeCertParamsGen βS βT d hβS hβT hd).dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  set c₀ := V_S (Sanctions.clipS' 0) with hc₀
  have hQ : ∀ s ∈ Sanctions.I,
      (eeCertParamsGen βS βT d hβS hβT hd).U_S x a s
          + (eeCertParamsGen βS βT d hβS hβT hd).β_S
            * V_S (Sanctions.clipS'
                ((eeCertParamsGen βS βT d hβS hβT hd).F x s))
        = -(1/2) * s ^ 2 + (2 - 11/5 * a + x + βS * c * d) * s
          + (a + 3 * x + βS * c₀ + βS * c * (1 - d) * x) := by
    intro s hs
    have hmem : (1 - d) * x + d * s ∈ Set.Icc (0:ℝ) 1 :=
      AbstractGame.affineF_mem hd x s hx hs
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
    have hdiff := gainBall_clip_diff hc hV_S h0 hmem
    simp only [eeCertParamsGen_U_S, eeCertParamsGen_β_S, eeCertParamsGen_F,
      eecU_S]
    rw [hc₀]
    linear_combination βS * hdiff
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne pp qq hp hq hpq
  have hq_eq : qq = 1 - pp := by linarith
  subst hq_eq
  have hmid : pp * s₁ + (1 - pp) * s₂ ∈ Sanctions.I :=
    ⟨by nlinarith [hs₁.1, hs₂.1, hp.le, hq.le],
     by nlinarith [hs₁.2, hs₂.2, hp.le, hq.le]⟩
  simp only [smul_eq_mul, hQ s₁ hs₁, hQ s₂ hs₂, hQ _ hmid]
  have hsq : (s₁ - s₂) ^ 2 > 0 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  nlinarith [mul_pos (mul_pos hp hq) hsq]

/-- **Sender Bellman image in closed form at the defiance policy
`α ≡ 0`**: the sSup collapses at the corner `s = 1` (via the `a = 0`
strict monotonicity, so no window condition). -/
theorem eeGen_bellmanS_image {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {c M : ℝ} (hc : 0 ≤ c) {W : Val} (hW : W ∈ valLipGainBall M c c 0)
    (y : ↥(Sanctions.S : Set ℝ)) :
    (eeCertParamsGen βS βT d hβS hβT hd).bellmanS_BCF (fun _ => 0)
        continuous_const W y
      = 3/2 + 4 * y.val + βS * W (Sanctions.clipS' ((1 - d) * y.val + d)) := by
  have h1I : (1:ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hmono := eeGen_senderObj_strictMonoOn_zero hβS hβT hd hc hW y.property
  rw [WitnessKit.bellmanS_image_of_isMaxOn (α := fun _ => (0:ℝ))
      continuous_const W y h1I
      (isMaxOn_iff.mpr fun s hs => hmono.monotoneOn hs h1I hs.2)]
  rw [show (eeCertParamsGen βS βT d hβS hβT hd).F y.val 1
        = (1 - d) * y.val + d by
      simp only [eeCertParamsGen_F]; ring]
  simp only [eeCertParamsGen_U_S, eeCertParamsGen_β_S, eecU_S]
  ring

/-- **Joint Target integrand in closed form** (with `σ_dyn ≡ 1` pinned):
`−(1/10)a + (41/10)x − 3 + β_T·V_T(clip((1−δ)x + δ))` — strictly
decreasing in compliance, and `β_S`-free. -/
theorem eeGen_joint_T_integrand_eq {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) (V_T : Val)
    {c M : ℝ} (hc : 0 ≤ c) (hchord : 6/5 ≤ βS * c * d)
    {V_S : Val} (hV_S : V_S ∈ valLipGainBall M c c 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (eeCertParamsGen βS βT d hβS hβT hd).joint_T_integrand V_T V_S x a
      = -(1/10) * a + 41/10 * x - 3
        + βT * V_T (Sanctions.clipS' ((1 - d) * x + d)) := by
  have hσ := eeGen_σ_dyn_eq_one hβS hβT hd hc hchord hV_S hx ha
  simp only [AbstractGame.Params.joint_T_integrand, hσ]
  rw [show (eeCertParamsGen βS βT d hβS hβT hd).F x 1
        = (1 - d) * x + d by
      simp only [eeCertParamsGen_F]; ring]
  simp only [eeCertParamsGen_U_T, eecU_T, eeCertParamsGen_β_T]
  ring

/-- **Full defiance `a = 0` is the Target argmax** at every physical
state (the integrand's compliance slope is `−1/10 < 0`). -/
theorem eeGen_zero_isMaxOn_joint {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) (V_T : Val)
    {c M : ℝ} (hc : 0 ≤ c) (hchord : 6/5 ≤ βS * c * d)
    {V_S : Val} (hV_S : V_S ∈ valLipGainBall M c c 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    IsMaxOn
      (fun a => (eeCertParamsGen βS βT d hβS hβT hd).joint_T_integrand
        V_T V_S x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [eeGen_joint_T_integrand_eq hβS hβT hd V_T hc hchord hV_S hx ha,
      eeGen_joint_T_integrand_eq hβS hβT hd V_T hc hchord hV_S hx
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)]
  linarith [ha.1]

/-- **Joint Target Bellman image in closed form**: the sSup over
compliance collapses at the defiance corner `a = 0`. The image is
`β_S`-free — the cross-feedback decoupling in raw form. -/
theorem eeGen_jointTarget_image {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) (V_T : Val)
    {c M : ℝ} (hc : 0 ≤ c) (hchord : 6/5 ≤ βS * c * d)
    {V_S : Val} (hV_S : V_S ∈ valLipGainBall M c c 0)
    (hDAU : (eeCertParamsGen βS βT d hβS hβT hd).DynamicArgmaxUnique V_S)
    (y : ↥(Sanctions.S : Set ℝ)) :
    (eeCertParamsGen βS βT d hβS hβT hd).jointTarget_BCF_on_S V_T V_S hDAU.toOnI y
      = 41/10 * y.val - 3
        + βT * V_T (Sanctions.clipS' ((1 - d) * y.val + d)) := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn V_T V_S hDAU.toOnI y
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)
        (eeGen_zero_isMaxOn_joint hβS hβT hd V_T hc hchord hV_S y.property),
      eeGen_joint_T_integrand_eq hβS hβT hd V_T hc hchord hV_S y.property
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)]
  ring

/-! ## 3. The eeCert `β_S`-family on the persistence window `[6/13, 4/7)`

Exact pinned coefficients (rational functions of `β`):
`c(β) = 8/(2−β)`, `b(β) = (6+5β)/(2(1−β)(2−β))`,
`V*(1;β) = b + c = (11/2)/(1−β)`. -/

/-- The eeCert `β_S` window sits inside the parameter space `[0,1)`. -/
theorem eeB_βS_mem {β : ℝ} (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    β ∈ Set.Ico (0:ℝ) 1 :=
  ⟨by linarith [hβ.1], by linarith [hβ.2]⟩

/-- **The eeCert `β_S`-family** on the exact persistence window. -/
def eeCertParamsB (β : ℝ) (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    AbstractGame.Params :=
  eeCertParamsGen β (9/10) (1/2) (eeB_βS_mem hβ) mem_910_Ico mem_half_Ioo

/-- Pinned equilibrium slope `c(β) = 8/(2−β)`. -/
def eeSlopeB (β : ℝ) : ℝ := 8 / (2 - β)

/-- Pinned equilibrium intercept `b(β) = (6+5β)/(2(1−β)(2−β))`. -/
def eeInterceptB (β : ℝ) : ℝ := (6 + 5 * β) / (2 * (1 - β) * (2 - β))

/-- Pinned lock-in value `V*(1;β) = (11/2)/(1−β)` (the capitalized
corner flow `U_S(1,0,1) = 11/2`). -/
def eeLockinB (β : ℝ) : ℝ := (11/2) / (1 - β)

/-- The `β`-re-pinned Sender carrier: slope `c(β) = 8/(2−β)`, norm
radius `M(β) = (11/2)/(1−β) = V*(1;β)` (derived, tight). -/
def eeCarrierSB (β : ℝ) : Set Val :=
  valLipGainBall (eeLockinB β) (eeSlopeB β) (eeSlopeB β) 0

/-- The pinned equilibrium value family `V_S*(x;β) = b(β) + c(β)·x`. -/
def eeVSstarB (β : ℝ) : Val :=
  affineInterceptBCF (eeInterceptB β) (eeSlopeB β)

theorem eeSlopeB_nonneg {β : ℝ} (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    0 ≤ eeSlopeB β :=
  div_nonneg (by norm_num) (by linarith [hβ.2])

/-- **Binding-below window constraint (all-compliance corner chord).**
On the window the discounted continuation slope `β·c(β)·δ = 4β/(2−β)`
weakly exceeds `6/5`, the worst-case stage chord drop — exactly the
`β ≥ 6/13` boundary, with equality admissible at the closed endpoint. -/
theorem eeCertB_chord {β : ℝ} (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    6/5 ≤ β * eeSlopeB β * (1/2) := by
  have h2 : (0:ℝ) < 2 - β := by linarith [hβ.2]
  have h2' : (2:ℝ) - β ≠ 0 := ne_of_gt h2
  have key : β * eeSlopeB β * (1/2) - 6/5 = (26 * β - 12) / (5 * (2 - β)) := by
    unfold eeSlopeB
    field_simp
    ring
  have hnn : (0:ℝ) ≤ (26 * β - 12) / (5 * (2 - β)) :=
    div_nonneg (by linarith [hβ.1]) (by linarith)
  linarith [key, hnn]

/-- **Binding-above window constraint (STRICT certificate margin).**
On the window `β·K_S·δ = 4β/(2−β) < 8/5 = m_S` strictly — the
`hS_margin` field of `StandardComplianceLocalCoreCertificate`, which is
strict, fails exactly at `β = 4/7`; hence the open right endpoint. -/
theorem eeCertB_hS_margin {β : ℝ} (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    β * eeSlopeB β * (1/2) < 8/5 := by
  have h2 : (0:ℝ) < 2 - β := by linarith [hβ.2]
  have h2' : (2:ℝ) - β ≠ 0 := ne_of_gt h2
  have key : 8/5 - β * eeSlopeB β * (1/2) = (16 - 28 * β) / (5 * (2 - β)) := by
    unfold eeSlopeB
    field_simp
    ring
  have hpos : (0:ℝ) < (16 - 28 * β) / (5 * (2 - β)) :=
    div_pos (by linarith [hβ.2]) (by linarith)
  linarith [key, hpos]

/-- **Policy invariance across the window (`σ_dyn` corner pin)**: on the
re-pinned carrier the dynamic Sender response is `1` at every physical
state and every compliance level, uniformly in `β ∈ [6/13, 4/7)` — the
argmax never moves, so the Acemoglu-Jensen policy-response term is
exactly zero on this window. -/
theorem eeCertB_σ_dyn_eq_one (β : ℝ) (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7))
    {V_S : Val} (hV_S : V_S ∈ eeCarrierSB β)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (eeCertParamsB β hβ).σ_dyn V_S x a = 1 :=
  eeGen_σ_dyn_eq_one (eeB_βS_mem hβ) mem_910_Ico mem_half_Ioo
    (eeSlopeB_nonneg hβ) (eeCertB_chord hβ) hV_S hx ha

/-- Upper-selector version of the corner pin (the selector the top
equilibrium's realized rule uses). -/
theorem eeCertB_σ_dyn_top_eq_one (β : ℝ) (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7))
    {V_S : Val} (hV_S : V_S ∈ eeCarrierSB β)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (eeCertParamsB β hβ).σ_dyn_top V_S x a = 1 :=
  eeGen_σ_dyn_top_eq_one (eeB_βS_mem hβ) mem_910_Ico mem_half_Ioo
    (eeSlopeB_nonneg hβ) (eeCertB_chord hβ) hV_S hx ha

/-- The pinned coefficients tile the lock-in value exactly:
`b(β) + c(β) = (11/2)/(1−β)`. -/
theorem eeCertB_lockin_identity {β : ℝ} (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    eeInterceptB β + eeSlopeB β = eeLockinB β := by
  have h1 : (1:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 1 - β)
  have h2 : (2:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 2 - β)
  unfold eeInterceptB eeSlopeB eeLockinB
  field_simp
  ring

/-- The pinned value family lives in the re-pinned carrier (its peak
`b + c` EQUALS the radius `M(β)` — the carrier is tight). -/
theorem eeVSstarB_mem {β : ℝ} (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    eeVSstarB β ∈ eeCarrierSB β := by
  have h1 : (0:ℝ) < 1 - β := by linarith [hβ.2]
  have h2 : (0:ℝ) < 2 - β := by linarith [hβ.2]
  have hden : (0:ℝ) < 2 * (1 - β) * (2 - β) := by
    nlinarith [mul_pos h1 h2]
  exact affineInterceptBCF_mem_gainBall
    (div_nonneg (by linarith [hβ.1]) hden.le)
    (eeSlopeB_nonneg hβ)
    (le_of_eq (eeCertB_lockin_identity hβ))

/-- Family Bellman image at the defiance policy, half-step form. -/
theorem eeCertB_bellmanS_image (β : ℝ) (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7))
    {W : Val} (hW : W ∈ eeCarrierSB β) (y : ↥(Sanctions.S : Set ℝ)) :
    (eeCertParamsB β hβ).bellmanS_BCF (fun _ => 0) continuous_const W y
      = 3/2 + 4 * y.val + β * W (Sanctions.clipS' ((y.val + 1)/2)) := by
  have h := eeGen_bellmanS_image (eeB_βS_mem hβ) mem_910_Ico mem_half_Ioo
    (eeSlopeB_nonneg hβ) hW y
  rwa [show ((1:ℝ) - 1/2) * y.val + 1/2 = (y.val + 1)/2 by ring] at h

/-- **THE parametrized pinned fixed point (the W2 device, uniform in
`β`)**: for every `β` in the persistence window, the Sender Bellman
operator at the derived defiance policy `α ≡ 0` fixes
`V_S*(x;β) = (6+5β)/(2(1−β)(2−β)) + 8/(2−β)·x` EXACTLY. This is the
equilibrium value's full re-adjustment to the patience parameter in
closed form — the object whose `β`-derivative is the Acemoglu-Jensen
full-adjustment comparative static. Reproduces the shipped pin
`eeCert_VS_star_fixed` (`b, c = 17/3, 16/3`) at `β = 1/2`. -/
theorem eeCertB_VS_star_fixed (β : ℝ) (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    (eeCertParamsB β hβ).bellmanS_BCF (fun _ => 0) continuous_const
        (eeVSstarB β)
      = eeVSstarB β := by
  ext y
  rw [eeCertB_bellmanS_image β hβ (eeVSstarB_mem hβ) y]
  have h1 : (1:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 1 - β)
  have h2 : (2:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 2 - β)
  simp only [eeVSstarB, affineInterceptBCF_apply,
    clipS'_val_of_mem (mem_half_shift y)]
  unfold eeInterceptB eeSlopeB
  field_simp
  ring

/-- The family reproduces the shipped `β = 1/2` pin (Rule 5: the W2
device is the one-line specialization). -/
theorem eeVSstarB_half : eeVSstarB (1/2) = eeVSstar := by
  unfold eeVSstarB eeVSstar eeInterceptB eeSlopeB
  norm_num

/-- Rule 5 demonstration: the shipped fixed-point pin follows from the
family in one line. -/
example :
    eeCertParams.bellmanS_BCF (fun _ => 0) continuous_const eeVSstar
      = eeVSstar := by
  have h := eeCertB_VS_star_fixed (1/2) ⟨by norm_num, by norm_num⟩
  rw [eeVSstarB_half] at h
  exact h

/-- Game-tied lock-in evaluation: the pinned value at the absorbing
state `x = 1` is the lock-in coefficient `eeLockinB β`. -/
theorem eeVSstarB_lockin {β : ℝ} (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    eeVSstarB β (Sanctions.clipS' 1) = eeLockinB β := by
  simp only [eeVSstarB, affineInterceptBCF_apply,
    clipS'_val_of_mem (⟨by norm_num, le_refl 1⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
  rw [mul_one]
  exact eeCertB_lockin_identity hβ

/-- **The pinned family solves the stationary Bellman equation pointwise.**

Repackages `eeCertB_VS_star_fixed` — the operator fixes the pinned value — as the
pointwise equation `V(x) = U_S(x,0,1) + β·V(F(x,1))`, with the corner stage payoff
`3/2 + 4x` and the corner successor `(x+1)/2` written out. This is the *only*
witness-specific input the two patience identities below need; everything else
they say is the general algebra of
`Foundations/PatienceDecomposition.lean`. -/
theorem eeCertB_VS_star_solvesAlong (β : ℝ) (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    Sanctions.PatienceDecomposition.SolvesAlong
      (fun w : ↥(Sanctions.S : Set ℝ) => 3/2 + 4 * w.val)
      (fun w : ↥(Sanctions.S : Set ℝ) => Sanctions.clipS' ((w.val + 1)/2))
      β (fun w : ↥(Sanctions.S : Set ℝ) => eeVSstarB β w) := by
  intro y
  have himg := eeCertB_bellmanS_image β hβ (eeVSstarB_mem hβ) y
  rw [eeCertB_VS_star_fixed β hβ] at himg
  exact himg

/-- The corner state is fixed by the corner successor: `(1+1)/2 = 1`. -/
theorem eeCertB_corner_fixed :
    Sanctions.clipS' (((Sanctions.clipS' (1:ℝ)).val + 1)/2)
      = Sanctions.clipS' (1:ℝ) := by
  rw [clipS'_val_of_mem (⟨by norm_num, le_refl 1⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
  norm_num

/-! ## 4. The `β_S`-channel: FULL / DIRECT / FEEDBACK derivatives

FULL = derivative of the pinned equilibrium coefficients (value fully
re-adjusted per `β`). DIRECT = derivative of one Bellman application at
the FROZEN old fixed point `eeVSstar` (the fixed-`(V,α)` effect the
existing `σ_dyn_top_le_of_beta_le` channel captures). FEEDBACK = full −
direct — the equilibrium re-adjustment channel this file closes. -/

/-- FULL slope response: `dc/dβ = 8/(2−β)²` on the window. -/
theorem eeSlopeB_hasDerivAt {β : ℝ} (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    HasDerivAt eeSlopeB (8 / (2 - β)^2) β := by
  have h2 : (2:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 2 - β)
  have hden : HasDerivAt (fun t : ℝ => 2 - t) (-1) β := by
    simpa using (hasDerivAt_id β).const_sub 2
  have h := (hasDerivAt_const β (8:ℝ)).fun_div hden h2
  convert h using 1
  ring

/-- FULL slope response at the witness point: `dc/dβ = 32/9` at
`β = 1/2`. -/
theorem eeSlopeB_hasDerivAt_half : HasDerivAt eeSlopeB (32/9) (1/2:ℝ) := by
  have h := eeSlopeB_hasDerivAt (β := 1/2) ⟨by norm_num, by norm_num⟩
  convert h using 1
  norm_num

/-- **Resolvent identity for the slope**: `c'(β) = (c(β)/2)/(1−β/2)` on
the whole window — the slope's own value feeds its derivative through
the discounted-transition resolvent. -/
theorem eeSlopeB_resolvent {β : ℝ} (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    HasDerivAt eeSlopeB ((eeSlopeB β / 2) / (1 - β/2)) β := by
  have h2 : (2:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 2 - β)
  have h2' : (1:ℝ) - β/2 ≠ 0 := by
    intro hh
    apply h2
    linarith
  have h := eeSlopeB_hasDerivAt hβ
  rw [show (eeSlopeB β / 2) / (1 - β/2) = 8 / (2 - β)^2 by
    unfold eeSlopeB
    field_simp]
  exact h

/-- FULL intercept response at the witness point: `db/dβ = 166/9` at
`β = 1/2`. -/
theorem eeInterceptB_hasDerivAt_half :
    HasDerivAt eeInterceptB (166/9) (1/2:ℝ) := by
  have hnum : HasDerivAt (fun t : ℝ => 6 + 5 * t) 5 (1/2:ℝ) := by
    simpa using (hasDerivAt_const_mul (5:ℝ) (x := (1/2:ℝ))).const_add 6
  have hden : HasDerivAt (fun t : ℝ => 2 * (1 - t) * (2 - t)) (-4) (1/2:ℝ) := by
    have hsub1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) (1/2:ℝ) := by
      simpa using (hasDerivAt_id (1/2:ℝ)).const_sub 1
    have h1 : HasDerivAt (fun t : ℝ => 2 * (1 - t)) (-2) (1/2:ℝ) := by
      have := hsub1.const_mul (2:ℝ)
      convert this using 1
      norm_num
    have h2 : HasDerivAt (fun t : ℝ => 2 - t) (-1) (1/2:ℝ) := by
      simpa using (hasDerivAt_id (1/2:ℝ)).const_sub 2
    have h := h1.mul h2
    convert h using 1
    norm_num
  have h := hnum.fun_div hden (by norm_num)
  convert h using 1
  norm_num

/-- FULL lock-in response: `dV*(1)/dβ = (11/2)/(1−β)²` on the window. -/
theorem eeLockinB_hasDerivAt {β : ℝ} (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    HasDerivAt eeLockinB ((11/2) / (1 - β)^2) β := by
  have h1 : (1:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 1 - β)
  have hden : HasDerivAt (fun t : ℝ => 1 - t) (-1) β := by
    simpa using (hasDerivAt_id β).const_sub 1
  have h := (hasDerivAt_const β ((11:ℝ)/2)).fun_div hden h1
  convert h using 1
  ring

/-- FULL lock-in response at the witness point: `dV*(1)/dβ = 22` at
`β = 1/2`. -/
theorem eeLockinB_hasDerivAt_half : HasDerivAt eeLockinB 22 (1/2:ℝ) := by
  have h := eeLockinB_hasDerivAt (β := 1/2) ⟨by norm_num, by norm_num⟩
  convert h using 1
  norm_num

/-- **Resolvent identity for the lock-in value**:
`dV*(1)/dβ = V*(1;β)/(1−β)` on the whole window — the derivative-level
form of the amplification `full = direct/(1−β)`. -/
theorem eeLockinB_resolvent {β : ℝ} (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    HasDerivAt eeLockinB (eeLockinB β / (1 - β)) β := by
  have h1 : (1:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 1 - β)
  have h := eeLockinB_hasDerivAt hβ
  rw [show eeLockinB β / (1 - β) = (11/2) / (1 - β)^2 by
    unfold eeLockinB
    field_simp]
  exact h

/-- **DIRECT effect in closed form**: one Sender Bellman application
with patience `β` at the FROZEN old (`β = 1/2`) pinned value `eeVSstar`
evaluates to `3/2 + (25/3)β + (4 + (8/3)β)·x` — so at fixed `(V, α)` the
`β`-response of the intercept is `25/3` and of the slope is `8/3`. -/
theorem eeCertB_direct_eval (β : ℝ) (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7))
    (y : ↥(Sanctions.S : Set ℝ)) :
    (eeCertParamsB β hβ).bellmanS_BCF (fun _ => 0) continuous_const
        eeVSstar y
      = 3/2 + 25/3 * β + (4 + 8/3 * β) * y.val := by
  refine Eq.trans (eeGen_bellmanS_image (eeB_βS_mem hβ) mem_910_Ico
    mem_half_Ioo (by norm_num : (0:ℝ) ≤ 16/3) (mem_eeCarrierS_num eeVSstar_mem) y) ?_
  have hmem : ((1:ℝ) - 1/2) * y.val + 1/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [y.property.1], by linarith [y.property.2]⟩
  simp only [eeVSstar, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  ring

/-- DIRECT effect at the absorbing state: the frozen-value Bellman
application at `x = 1` is `11/2 + 11β` — the fixed-`(V,α)` lock-in
response is `11` per unit of patience. -/
theorem eeCertB_direct_lockin_eval (β : ℝ)
    (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    (eeCertParamsB β hβ).bellmanS_BCF (fun _ => 0) continuous_const
        eeVSstar (Sanctions.clipS' 1)
      = 11/2 + 11 * β := by
  rw [eeCertB_direct_eval β hβ (Sanctions.clipS' 1),
      clipS'_val_of_mem (⟨by norm_num, le_refl 1⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
  ring

/-- The DIRECT lock-in map `β ↦ 11/2 + 11β` has derivative `11`
(everywhere; the closed form is tied to the game by
`eeCertB_direct_lockin_eval` on the window). -/
theorem eeCertB_direct_lockin_hasDerivAt (β : ℝ) :
    HasDerivAt (fun t : ℝ => 11/2 + 11 * t) 11 β := by
  simpa using (hasDerivAt_const_mul (11:ℝ) (x := β)).const_add (11/2 : ℝ)

/-- **Machine-checked FULL = DIRECT + FEEDBACK split, slope channel**:
`32/9 = 8/3 + 8/9`, feedback strictly positive. (Numbers pinned by
`eeSlopeB_hasDerivAt_half` and `eeCertB_direct_eval`.) -/
theorem eeCertB_slope_split : (32:ℝ)/9 = 8/3 + 8/9 ∧ (0:ℝ) < 8/9 := by
  norm_num

/-- **Split, intercept channel**: `166/9 = 25/3 + 91/9`, feedback
strictly positive. -/
theorem eeCertB_intercept_split :
    (166:ℝ)/9 = 25/3 + 91/9 ∧ (0:ℝ) < 91/9 := by
  norm_num

/-- **Split, lock-in channel, with amplification**: `22 = 11 + 11`
(feedback strictly positive and EQUAL to the direct effect at
`β = 1/2`), and `full = direct/(1−β)`: `22 = 11/(1 − 1/2)`. -/
theorem eeCertB_lockin_split :
    (22:ℝ) = 11 + 11 ∧ (0:ℝ) < 11 ∧ (22:ℝ) = 11 / (1 - 1/2) := by
  norm_num

/-- **The exact finite-difference Acemoglu-Jensen decomposition**: for
any two window parameters, the change of the pinned equilibrium value
at any state splits EXACTLY as

  `ΔV(x) = Δβ·V₂(F(x,1))  [DIRECT]  +  β₁·ΔV(F(x,1))  [FEEDBACK]`

where `F(x,1) = (x+1)/2` is the corner transition. Ring-provable from
the two pinned Bellman fixed points (`eeCertB_VS_star_fixed`). -/
theorem eeCertB_feedback_decomposition (β₁ β₂ : ℝ)
    (hβ₁ : β₁ ∈ Set.Ico (6/13:ℝ) (4/7)) (hβ₂ : β₂ ∈ Set.Ico (6/13:ℝ) (4/7))
    (y : ↥(Sanctions.S : Set ℝ)) :
    eeVSstarB β₂ y - eeVSstarB β₁ y
      = (β₂ - β₁) * eeVSstarB β₂ (Sanctions.clipS' ((y.val + 1)/2))
        + β₁ * (eeVSstarB β₂ (Sanctions.clipS' ((y.val + 1)/2))
            - eeVSstarB β₁ (Sanctions.clipS' ((y.val + 1)/2))) :=
  Sanctions.PatienceDecomposition.difference_decomposition
    (eeCertB_VS_star_solvesAlong β₁ hβ₁) (eeCertB_VS_star_solvesAlong β₂ hβ₂) y

/-- **Feedback strictly positive at the lock-in state** (Rule 16(a)
directional content in finite-difference form): raising patience within
the window strictly raises the re-pinned lock-in value, so the feedback
term `β₁·ΔV(1)` is strictly positive. -/
theorem eeCertB_feedback_lockin_pos (β₁ β₂ : ℝ)
    (hβ₁ : β₁ ∈ Set.Ico (6/13:ℝ) (4/7)) (hβ₂ : β₂ ∈ Set.Ico (6/13:ℝ) (4/7))
    (hlt : β₁ < β₂) :
    0 < β₁ * (eeLockinB β₂ - eeLockinB β₁) := by
  have h1 : (0:ℝ) < 1 - β₁ := by linarith [hβ₁.2]
  have h2 : (0:ℝ) < 1 - β₂ := by linarith [hβ₂.2]
  have hβ₁pos : (0:ℝ) < β₁ := by linarith [hβ₁.1]
  have key : eeLockinB β₂ - eeLockinB β₁
      = (11/2) * (β₂ - β₁) / ((1 - β₁) * (1 - β₂)) := by
    unfold eeLockinB
    field_simp
    ring
  refine mul_pos hβ₁pos ?_
  rw [key]
  exact div_pos (by nlinarith) (mul_pos h1 h2)

/-- **Lock-in amplification identity (finite-difference, division-free
form)**: `(1−β₁)·ΔV*(1) = Δβ·V*(1;β₂)` — at the absorbing state the
full response is the direct response amplified by the patience
resolvent `1/(1−β₁)`. -/
theorem eeCertB_lockin_amplification (β₁ β₂ : ℝ)
    (hβ₁ : β₁ ∈ Set.Ico (6/13:ℝ) (4/7))
    (hβ₂ : β₂ ∈ Set.Ico (6/13:ℝ) (4/7)) :
    (1 - β₁) * (eeLockinB β₂ - eeLockinB β₁)
      = (β₂ - β₁) * eeLockinB β₂ := by
  have h := Sanctions.PatienceDecomposition.amplification_at_fixedPoint
    (eeCertB_VS_star_solvesAlong β₁ hβ₁) (eeCertB_VS_star_solvesAlong β₂ hβ₂)
    eeCertB_corner_fixed
  rwa [eeVSstarB_lockin hβ₁, eeVSstarB_lockin hβ₂] at h

/-- **Rule 16(a) ordered-endpoint corollary**: at the provably-distinct
window points `β = 1/2 < 11/20`, the pinned slope and lock-in value are
strictly ordered the economically-intended way (more patience, steeper
and deeper lock-in): slopes `16/3 < 160/29`, lock-in `11 < 110/9`. -/
theorem eeCertB_rule16a :
    (1/2:ℝ) < 11/20
      ∧ (1/2:ℝ) ∈ Set.Ico (6/13:ℝ) (4/7)
      ∧ (11/20:ℝ) ∈ Set.Ico (6/13:ℝ) (4/7)
      ∧ eeSlopeB (1/2) = 16/3 ∧ eeSlopeB (11/20) = 160/29
      ∧ eeLockinB (1/2) = 11 ∧ eeLockinB (11/20) = 110/9
      ∧ eeSlopeB (1/2) < eeSlopeB (11/20)
      ∧ eeLockinB (1/2) < eeLockinB (11/20) := by
  unfold eeSlopeB eeLockinB
  norm_num [Set.mem_Ico]

/-! ## 5. Cross-feedback decoupling and the eeCert `β_T`-channel -/

/-- State-local Sender argmax uniqueness of the pinned family value at
its own family member (input to the joint Target operator). -/
theorem eeCertB_DAU (β : ℝ) (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7)) :
    (eeCertParamsB β hβ).DynamicArgmaxUnique (eeVSstarB β) :=
  eeGen_DAU_on_carrier (eeB_βS_mem hβ) mem_910_Ico mem_half_Ioo
    (eeSlopeB_nonneg hβ) (eeVSstarB_mem hβ)

/-- **Cross-feedback decoupling — the pinned Target fixed point is the
SAME `V_T* = (82x+39)/11` at every `β_S` in the window**: the joint
Target Bellman operator (Sender input = the `β`-re-pinned `V_S*(·;β)`)
fixes the `β_S`-INDEPENDENT `eeVTstar` for every window `β`. Once
`σ_dyn ≡ 1` is pinned, the Target image is `V_S`-free, so the Target
value does not re-adjust to Sender patience at all: `dV_T*/dβ_S = 0`
exactly. -/
theorem eeCertB_VT_star_fixed (β : ℝ) (hβ : β ∈ Set.Ico (6/13:ℝ) (4/7))
    (y : ↥(Sanctions.S : Set ℝ)) :
    (eeCertParamsB β hβ).jointTarget_BCF_on_S eeVTstar (eeVSstarB β)
        (eeCertB_DAU β hβ).toOnI y
      = eeVTstar y := by
  refine Eq.trans (eeGen_jointTarget_image (eeB_βS_mem hβ) mem_910_Ico
    mem_half_Ioo eeVTstar (eeSlopeB_nonneg hβ) (eeCertB_chord hβ)
    (eeVSstarB_mem hβ) (eeCertB_DAU β hβ) y) ?_
  rw [show ((1:ℝ) - 1/2) * y.val + 1/2 = (y.val + 1)/2 by ring]
  simp only [eeVTstar, affineInterceptBCF_apply,
    clipS'_val_of_mem (mem_half_shift y)]
  ring

/-- The upper-selector Target integrand at the re-pinned value family.
The formula is affine and strictly decreasing in compliance, uniformly
over the certified Sender-patience window. -/
theorem eeCertB_joint_T_top_integrand_eq (β : ℝ)
    (hβ : β ∈ Set.Ico (6 / 13 : ℝ) (4 / 7))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {a : ℝ} (ha : a ∈ Sanctions.I) :
    (eeCertParamsB β hβ).joint_T_top_integrand eeVTstar (eeVSstarB β) x a
      = -(1 / 10) * a + 41 / 10 * x - 3
        + (9 / 10) * eeVTstar (Sanctions.clipS' ((x + 1) / 2)) := by
  have hσ := eeCertB_σ_dyn_top_eq_one β hβ (eeVSstarB_mem hβ) hx ha
  simp only [AbstractGame.Params.joint_T_top_integrand, hσ]
  rw [show (eeCertParamsB β hβ).F x 1 = (x + 1) / 2 by
    simp only [eeCertParamsB, eeCertParamsGen_F]
    ring]
  simp only [eeCertParamsB, eeCertParamsGen_U_T, eecU_T, eeCertParamsGen_β_T]
  ring

/-- Defiance is the Target's upper-selector best response throughout
the certified Sender-patience window. -/
theorem eeCertB_zero_isMaxOn_joint_top (β : ℝ)
    (hβ : β ∈ Set.Ico (6 / 13 : ℝ) (4 / 7))
    {x : ℝ} (hx : x ∈ Sanctions.S) :
    IsMaxOn
      (fun a => (eeCertParamsB β hβ).joint_T_top_integrand
        eeVTstar (eeVSstarB β) x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rw [eeCertB_joint_T_top_integrand_eq β hβ hx ha,
      eeCertB_joint_T_top_integrand_eq β hβ hx
        (⟨le_refl 0, by norm_num⟩ : (0 : ℝ) ∈ Sanctions.I)]
  linarith [ha.1]

/-- The Target value family satisfies the upper-selector Bellman
equation, not only the auxiliary unique-selector operator equation. -/
theorem eeCertB_VT_star_fixed_top (β : ℝ)
    (hβ : β ∈ Set.Ico (6 / 13 : ℝ) (4 / 7))
    (x : ↥(Sanctions.S : Set ℝ)) :
    eeVTstar x = sSup
      ((fun a => (eeCertParamsB β hβ).joint_T_top_integrand
        eeVTstar (eeVSstarB β) x.val a) '' Sanctions.I) := by
  have hmax := eeCertB_zero_isMaxOn_joint_top β hβ x.property
  have hgreatest :
      IsGreatest
        ((fun a => (eeCertParamsB β hβ).joint_T_top_integrand
          eeVTstar (eeVSstarB β) x.val a) '' Sanctions.I)
        ((eeCertParamsB β hβ).joint_T_top_integrand
          eeVTstar (eeVSstarB β) x.val 0) := by
    constructor
    · exact ⟨0, ⟨le_refl 0, by norm_num⟩, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact hmax ha
  rw [hgreatest.csSup_eq, eeCertB_joint_T_top_integrand_eq β hβ x.property
    (⟨le_refl 0, by norm_num⟩ : (0 : ℝ) ∈ Sanctions.I)]
  simp only [eeVTstar, affineInterceptBCF_apply,
    clipS'_val_of_mem (mem_half_shift x)]
  ring

/-- An explicit sequential upper-selector Stackelberg equilibrium at
every Sender-patience parameter in the certified window. This packages
the re-pinned value formulas used below as equilibrium objects. -/
noncomputable def eeCertBEquilibrium (β : ℝ)
    (hβ : β ∈ Set.Ico (6 / 13 : ℝ) (4 / 7)) :
    (eeCertParamsB β hβ).FeedbackStackelbergEquilibriumTop where
  V_T := eeVTstar
  V_S := eeVSstarB β
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_refl 0, by norm_num⟩
  V_S_fix := (eeCertB_VS_star_fixed β hβ).symm
  V_T_fix_top := eeCertB_VT_star_fixed_top β hβ
  α_opt_top := fun _ hx => eeCertB_zero_isMaxOn_joint_top β hβ hx

/-! ### SUPERSEDED FOR GENERALITY — Rule 9 scope fence

**Do not cite the four `eeCertB_*` equilibrium comparative statics below as
support for any general claim.** They are stated at the single numeric economy
`eeCertParamsB` over the hand-computed patience window `β_S ∈ [6/13, 4/7)`, so
by Rule 9A they license existence and refutation and nothing else — no
universal, no genericity, no mechanism attribution.

Every one of them is an identity in the closed forms, and the number-free
versions now live in `Sanctions/Examples/SymbolicCertifiedFamily.lean` §13a:

| numeric (here)                              | symbolic (cite this instead)              |
|---------------------------------------------|-------------------------------------------|
| `eeCertB_equilibrium_feedback_decomposition` | `symbolic_equilibrium_feedback_decomposition` |
| `eeCertB_lockin_amplification`               | `symbolic_lockin_amplification`           |
| `eeCertB_equilibrium_lockin_strict`          | `symbolic_lockin_strict`                  |
| `eeCertB_VT_star_βS_invariant`               | `symbolic_VTstar_βS_invariant`            |

On the strict patience ranking specifically: it survives the lift
**unconditionally**, and it is worth recording why, because the reason is not
visible at the numeric point. The ranking needs the corner stage payoff
`U_S(1, 0, 1)` to be positive — here it is `11/2`, which reads like a fact
about the calibration. It is not: `SymbolicEconomy.cornerStagePayoff_pos`
derives positivity from the family's own two Sender margins (chaining them
forces `q < u₀`, hence `u₀ - q/2 > 0`). The sharper
`symbolic_lockin_strict_iff` isolates that sign as the whole content of the
comparative static. -/

/-- Equilibrium-level form of the exact finite-difference decomposition:
the total change in Sender value equals its direct patience effect plus
the continuation-value feedback effect.

Rule 9 scope: witness-level. See the fence above; the general form is
`symbolic_equilibrium_feedback_decomposition`. -/
theorem eeCertB_equilibrium_feedback_decomposition (β₁ β₂ : ℝ)
    (hβ₁ : β₁ ∈ Set.Ico (6 / 13 : ℝ) (4 / 7))
    (hβ₂ : β₂ ∈ Set.Ico (6 / 13 : ℝ) (4 / 7))
    (y : ↥(Sanctions.S : Set ℝ)) :
    (eeCertBEquilibrium β₂ hβ₂).V_S y
        - (eeCertBEquilibrium β₁ hβ₁).V_S y
      = (β₂ - β₁) * (eeCertBEquilibrium β₂ hβ₂).V_S
          (Sanctions.clipS' ((y.val + 1) / 2))
        + β₁ * ((eeCertBEquilibrium β₂ hβ₂).V_S
              (Sanctions.clipS' ((y.val + 1) / 2))
            - (eeCertBEquilibrium β₁ hβ₁).V_S
              (Sanctions.clipS' ((y.val + 1) / 2))) :=
  eeCertB_feedback_decomposition β₁ β₂ hβ₁ hβ₂ y

/-- Raising Sender patience strictly raises the Sender's equilibrium
value at the absorbing lock-in state throughout the certified window. -/
theorem eeCertB_equilibrium_lockin_strict (β₁ β₂ : ℝ)
    (hβ₁ : β₁ ∈ Set.Ico (6 / 13 : ℝ) (4 / 7))
    (hβ₂ : β₂ ∈ Set.Ico (6 / 13 : ℝ) (4 / 7))
    (hlt : β₁ < β₂) :
    (eeCertBEquilibrium β₁ hβ₁).V_S (Sanctions.clipS' 1)
      < (eeCertBEquilibrium β₂ hβ₂).V_S (Sanctions.clipS' 1) := by
  change eeVSstarB β₁ (Sanctions.clipS' 1)
    < eeVSstarB β₂ (Sanctions.clipS' 1)
  rw [eeVSstarB_lockin hβ₁, eeVSstarB_lockin hβ₂]
  have hp := eeCertB_feedback_lockin_pos β₁ β₂ hβ₁ hβ₂ hlt
  rw [mul_comm] at hp
  exact sub_pos.mp
    (pos_of_mul_pos_left hp (by linarith [hβ₁.1] : 0 ≤ β₁))

/-- The `β_S`-invariance in two-parameter form: the pinned Target
equilibrium images at any two window parameters agree pointwise
(both are `eeVTstar`). Machine-checked `dV_T*/dβ_S ≡ 0`. -/
theorem eeCertB_VT_star_βS_invariant (β₁ β₂ : ℝ)
    (hβ₁ : β₁ ∈ Set.Ico (6/13:ℝ) (4/7)) (hβ₂ : β₂ ∈ Set.Ico (6/13:ℝ) (4/7))
    (y : ↥(Sanctions.S : Set ℝ)) :
    (eeCertParamsB β₁ hβ₁).jointTarget_BCF_on_S eeVTstar (eeVSstarB β₁)
        (eeCertB_DAU β₁ hβ₁).toOnI y
      = (eeCertParamsB β₂ hβ₂).jointTarget_BCF_on_S eeVTstar (eeVSstarB β₂)
          (eeCertB_DAU β₂ hβ₂).toOnI y := by
  rw [eeCertB_VT_star_fixed β₁ hβ₁ y, eeCertB_VT_star_fixed β₂ hβ₂ y]

/-! ### The eeCert `β_T`-channel on `[598/709, 1)`

Target-side pinned coefficients: `c_T(γ) = 41/(5(2−γ))`,
`b_T(γ) = (71γ−60)/(10(1−γ)(2−γ))`, `V_T*(1;γ) = (11/10)/(1−γ)`.
The window's binding constraint is the certificate's (non-strict)
loss-offset margin `cT = 299/100 ≤ γ·g_T(γ)·δ`. -/

/-- The eeCert `β_T` window sits inside the parameter space `[0,1)`. -/
theorem eeBT_βT_mem {γ : ℝ} (hγ : γ ∈ Set.Ico (598/709:ℝ) 1) :
    γ ∈ Set.Ico (0:ℝ) 1 :=
  ⟨by linarith [hγ.1], hγ.2⟩

/-- **The eeCert `β_T`-family** on the loss-offset persistence window. -/
def eeCertParamsBT (γ : ℝ) (hγ : γ ∈ Set.Ico (598/709:ℝ) 1) :
    AbstractGame.Params :=
  eeCertParamsGen (1/2) γ (1/2) mem_half_Ico (eeBT_βT_mem hγ) mem_half_Ioo

/-- Pinned Target slope `c_T(γ) = 41/(5(2−γ))`. -/
def eeSlopeT (γ : ℝ) : ℝ := 41 / (5 * (2 - γ))

/-- Pinned Target intercept `b_T(γ) = (71γ−60)/(10(1−γ)(2−γ))`. -/
def eeInterceptT (γ : ℝ) : ℝ := (71 * γ - 60) / (10 * (1 - γ) * (2 - γ))

/-- Pinned Target lock-in value `V_T*(1;γ) = (11/10)/(1−γ)` (the
capitalized corner flow `U_T(1,0,1) = 11/10`). -/
def eeLockinT (γ : ℝ) : ℝ := (11/10) / (1 - γ)

/-- The pinned Target value family `V_T*(x;γ) = b_T(γ) + c_T(γ)·x`. -/
def eeVTstarT (γ : ℝ) : Val :=
  affineInterceptBCF (eeInterceptT γ) (eeSlopeT γ)

/-- **Binding-below window constraint (Target loss-offset margin)**: on
the window `cT = 299/100 ≤ γ·g_T(γ)·δ = 41γ/(10(2−γ))` — the Target
loss-offset margin `hT_loss_margin` at the `γ`-re-pinned carrier slope
(a field of the certificate until round BJ1.4, 2026-10-07, which deleted the
Target loss-offset stack; it remains the margin input of the standalone
discharger `Target_combined_chord_of_decomposition_lowerChord_affine`), binding
exactly at `γ = 598/709` (closed endpoint admissible: the margin is
non-strict). -/
theorem eeCertBT_loss_margin {γ : ℝ} (hγ : γ ∈ Set.Ico (598/709:ℝ) 1) :
    299/100 ≤ γ * eeSlopeT γ * (1/2) := by
  have h2 : (0:ℝ) < 2 - γ := by linarith [hγ.2]
  have h2' : (2:ℝ) - γ ≠ 0 := ne_of_gt h2
  have key : γ * eeSlopeT γ * (1/2) - 299/100
      = (709 * γ - 598) / (100 * (2 - γ)) := by
    unfold eeSlopeT
    field_simp
    ring
  have hnn : (0:ℝ) ≤ (709 * γ - 598) / (100 * (2 - γ)) :=
    div_nonneg (by linarith [hγ.1]) (by linarith)
  linarith [key, hnn]

/-- Target coefficients tile the lock-in value:
`b_T(γ) + c_T(γ) = (11/10)/(1−γ)`. -/
theorem eeCertBT_lockin_identity {γ : ℝ} (hγ : γ ∈ Set.Ico (598/709:ℝ) 1) :
    eeInterceptT γ + eeSlopeT γ = eeLockinT γ := by
  have h1 : (1:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 1 - γ)
  have h2 : (2:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 2 - γ)
  unfold eeInterceptT eeSlopeT eeLockinT
  field_simp
  ring

/-- **The parametrized Target pinned fixed point (`β_T`-channel)**: for
every `γ` in the window, the joint Target Bellman operator (Sender
input = the shipped `β_S = 1/2` pin `eeVSstar`, whose corner pin holds
since `4/3 ≥ 6/5`) fixes `V_T*(x;γ) = b_T(γ) + c_T(γ)·x` exactly.
Reproduces the shipped pin `(39/11, 82/11)` at `γ = 9/10`. -/
theorem eeCertBT_VT_star_fixed (γ : ℝ) (hγ : γ ∈ Set.Ico (598/709:ℝ) 1)
    (y : ↥(Sanctions.S : Set ℝ)) :
    (eeCertParamsBT γ hγ).jointTarget_BCF_on_S (eeVTstarT γ) eeVSstar
        (eeGen_DAU_on_carrier mem_half_Ico (eeBT_βT_mem hγ) mem_half_Ioo
          (by norm_num : (0:ℝ) ≤ 16/3) (mem_eeCarrierS_num eeVSstar_mem)).toOnI y
      = eeVTstarT γ y := by
  refine Eq.trans (eeGen_jointTarget_image mem_half_Ico (eeBT_βT_mem hγ)
    mem_half_Ioo (eeVTstarT γ) (by norm_num : (0:ℝ) ≤ 16/3)
    (by norm_num : (6:ℝ)/5 ≤ 1/2 * (16/3) * (1/2)) (mem_eeCarrierS_num eeVSstar_mem)
    (eeGen_DAU_on_carrier mem_half_Ico (eeBT_βT_mem hγ) mem_half_Ioo
      (by norm_num : (0:ℝ) ≤ 16/3) (mem_eeCarrierS_num eeVSstar_mem)) y) ?_
  rw [show ((1:ℝ) - 1/2) * y.val + 1/2 = (y.val + 1)/2 by ring]
  have h1 : (1:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 1 - γ)
  have h2 : (2:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 2 - γ)
  simp only [eeVTstarT, affineInterceptBCF_apply,
    clipS'_val_of_mem (mem_half_shift y)]
  unfold eeInterceptT eeSlopeT
  field_simp
  ring

/-- The Target family reproduces the shipped `γ = 9/10` pin
`V_T* = (82x+39)/11` (Rule 5). -/
theorem eeVTstarT_910 : eeVTstarT (9/10) = eeVTstar := by
  unfold eeVTstarT eeVTstar eeInterceptT eeSlopeT
  norm_num

/-- **The pinned Target family solves the Target corner Bellman equation
pointwise.** Repackages `eeCertBT_VT_star_fixed` through the closed-form joint
Target image `eeGen_jointTarget_image`: at every state,
`V_T*(y;γ) = U_T(y, 0, 1) + γ·V_T*(F(y, 1);γ)` in the family economy — the Sender
at full sanction (`σ_dyn ≡ 1`), the Target at full defiance (`a = 0`), with the
corner flow `41/10·y − 3` and successor `(y+1)/2`. This is the only
witness-specific input the Target trio needs (BH6.3, 2026-10-07). -/
theorem eeCertBT_VT_star_cornerBellman (γ : ℝ) (hγ : γ ∈ Set.Ico (598 / 709 : ℝ) 1)
    (y : ↥(Sanctions.S : Set ℝ)) :
    eeVTstarT γ y = (eeCertParamsBT γ hγ).U_T y.val 0 1
      + γ * eeVTstarT γ (Sanctions.clipS' ((eeCertParamsBT γ hγ).F y.val 1)) := by
  have hpin : eeVTstarT γ y = 41/10 * y.val - 3
      + γ * eeVTstarT γ (Sanctions.clipS' ((1 - 1/2) * y.val + 1/2)) :=
    (eeCertBT_VT_star_fixed γ hγ y).symm.trans
      (eeGen_jointTarget_image mem_half_Ico (eeBT_βT_mem hγ)
        mem_half_Ioo (eeVTstarT γ) (by norm_num : (0:ℝ) ≤ 16/3)
        (by norm_num : (6:ℝ)/5 ≤ 1/2 * (16/3) * (1/2)) (mem_eeCarrierS_num eeVSstar_mem)
        (eeGen_DAU_on_carrier mem_half_Ico (eeBT_βT_mem hγ) mem_half_Ioo
          (by norm_num : (0:ℝ) ≤ 16/3) (mem_eeCarrierS_num eeVSstar_mem)) y)
  have hU : (eeCertParamsBT γ hγ).U_T y.val 0 1 = 41/10 * y.val - 3 := by
    simp only [eeCertParamsBT, eeCertParamsGen_U_T, eecU_T]
    ring
  have hF : (eeCertParamsBT γ hγ).F y.val 1 = (1 - 1/2) * y.val + 1/2 := by
    simp only [eeCertParamsBT, eeCertParamsGen_F]
    ring
  rw [hU, hF]
  exact hpin

/-- The pinned Target family at the lock-in state is the pinned lock-in value:
`V_T*(1;γ) = b_T(γ) + c_T(γ) = (11/10)/(1−γ)`. -/
theorem eeVTstarT_lockin {γ : ℝ} (hγ : γ ∈ Set.Ico (598 / 709 : ℝ) 1) :
    eeVTstarT γ (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
      = eeLockinT γ := by
  change eeInterceptT γ + eeSlopeT γ * 1 = eeLockinT γ
  rw [mul_one]
  exact eeCertBT_lockin_identity hγ

/-- FULL Target lock-in response: `dV_T*(1)/dγ = (11/10)/(1−γ)²` on the
window. -/
theorem eeLockinT_hasDerivAt {γ : ℝ} (hγ : γ ∈ Set.Ico (598/709:ℝ) 1) :
    HasDerivAt eeLockinT ((11/10) / (1 - γ)^2) γ := by
  have h1 : (1:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 1 - γ)
  have hden : HasDerivAt (fun t : ℝ => 1 - t) (-1) γ := by
    simpa using (hasDerivAt_id γ).const_sub 1
  have h := (hasDerivAt_const γ ((11:ℝ)/10)).fun_div hden h1
  convert h using 1
  ring

/-- FULL Target lock-in response at the witness point:
`dV_T*(1)/dβ_T = 110` at `γ = 9/10`. -/
theorem eeLockinT_hasDerivAt_910 : HasDerivAt eeLockinT 110 (9/10:ℝ) := by
  have h := eeLockinT_hasDerivAt (γ := 9/10) ⟨by norm_num, by norm_num⟩
  convert h using 1
  norm_num

/-- Resolvent identity for the Target lock-in:
`dV_T*(1)/dγ = V_T*(1;γ)/(1−γ)`. -/
theorem eeLockinT_resolvent {γ : ℝ} (hγ : γ ∈ Set.Ico (598/709:ℝ) 1) :
    HasDerivAt eeLockinT (eeLockinT γ / (1 - γ)) γ := by
  have h1 : (1:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 1 - γ)
  have h := eeLockinT_hasDerivAt hγ
  rw [show eeLockinT γ / (1 - γ) = (11/10) / (1 - γ)^2 by
    unfold eeLockinT
    field_simp]
  exact h

/-- **DIRECT Target effect in closed form**: one joint Target Bellman
application with patience `γ` at the FROZEN old (`γ = 9/10`) pin
`eeVTstar` evaluates at the absorbing state to `11/10 + 11γ` — the
fixed-`(V,σ,α)` lock-in response is `11` per unit of Target patience. -/
theorem eeCertBT_direct_lockin_eval (γ : ℝ)
    (hγ : γ ∈ Set.Ico (598/709:ℝ) 1) :
    (eeCertParamsBT γ hγ).jointTarget_BCF_on_S eeVTstar eeVSstar
        (eeGen_DAU_on_carrier mem_half_Ico (eeBT_βT_mem hγ) mem_half_Ioo
          (by norm_num : (0:ℝ) ≤ 16/3) (mem_eeCarrierS_num eeVSstar_mem)).toOnI
        (Sanctions.clipS' 1)
      = 11/10 + 11 * γ := by
  refine Eq.trans (eeGen_jointTarget_image mem_half_Ico (eeBT_βT_mem hγ)
    mem_half_Ioo eeVTstar (by norm_num : (0:ℝ) ≤ 16/3)
    (by norm_num : (6:ℝ)/5 ≤ 1/2 * (16/3) * (1/2)) (mem_eeCarrierS_num eeVSstar_mem)
    (eeGen_DAU_on_carrier mem_half_Ico (eeBT_βT_mem hγ) mem_half_Ioo
      (by norm_num : (0:ℝ) ≤ 16/3) (mem_eeCarrierS_num eeVSstar_mem)) (Sanctions.clipS' 1)) ?_
  rw [clipS'_val_of_mem (⟨by norm_num, le_refl 1⟩ :
    (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
  have hmem : ((1:ℝ) - 1/2) * 1 + 1/2 ∈ Set.Icc (0:ℝ) 1 := by
    constructor <;> norm_num
  simp only [eeVTstar, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  ring

/-- The DIRECT Target lock-in map `γ ↦ 11/10 + 11γ` has derivative
`11`. -/
theorem eeCertBT_direct_lockin_hasDerivAt (γ : ℝ) :
    HasDerivAt (fun t : ℝ => 11/10 + 11 * t) 11 γ := by
  simpa using (hasDerivAt_const_mul (11:ℝ) (x := γ)).const_add (11/10 : ℝ)

/-- **Split, Target lock-in channel**: `110 = 11 + 99` — the full
response is the direct response amplified by `1/(1−9/10) = 10`;
feedback `99` strictly positive. -/
theorem eeCertBT_lockin_split :
    (110:ℝ) = 11 + 99 ∧ (0:ℝ) < 99 ∧ (110:ℝ) = 11 / (1 - 9/10) := by
  norm_num

/-- Lock-in amplification identity for the Target channel:
`(1−γ₁)·ΔV_T*(1) = Δγ·V_T*(1;γ₂)`.

Since BH6.3 (2026-10-07) an instance of the general-`F`
`targetValue_lockin_amplification_of_bellman` at the pinned Target fixed points
(`eeCertBT_VT_star_cornerBellman`, `eeVTstarT_lockin`), the way
`eeCertB_lockin_amplification` instantiates the Sender algebra; it used to be a
`field_simp` computation on the closed form `eeLockinT`. Statement unchanged. -/
theorem eeCertBT_lockin_amplification (γ₁ γ₂ : ℝ)
    (hγ₁ : γ₁ ∈ Set.Ico (598/709:ℝ) 1) (hγ₂ : γ₂ ∈ Set.Ico (598/709:ℝ) 1) :
    (1 - γ₁) * (eeLockinT γ₂ - eeLockinT γ₁)
      = (γ₂ - γ₁) * eeLockinT γ₂ := by
  have h := (eeCertParamsBT γ₁ hγ₁).targetValue_lockin_amplification_of_bellman 0
    (eeCertBT_VT_star_cornerBellman γ₁ hγ₁) (eeCertBT_VT_star_cornerBellman γ₂ hγ₂)
  rwa [eeVTstarT_lockin hγ₁, eeVTstarT_lockin hγ₂] at h

/-- Rule 16(a) ordered endpoints for the Target channel: at
`γ = 9/10 < 23/25` (both in the window), lock-in values `11 < 55/4`. -/
theorem eeCertBT_rule16a :
    (9/10:ℝ) < 23/25
      ∧ (9/10:ℝ) ∈ Set.Ico (598/709:ℝ) 1
      ∧ (23/25:ℝ) ∈ Set.Ico (598/709:ℝ) 1
      ∧ eeLockinT (9/10) = 11 ∧ eeLockinT (23/25) = 55/4
      ∧ eeLockinT (9/10) < eeLockinT (23/25) := by
  unfold eeLockinT
  norm_num [Set.mem_Ico]

/-! ## 6. The eeCert `δ`-channel on `[3/7, 2/3)`: exact lock-in-value
invariance

Pinned coefficients: `c(δ) = 8/(1+δ)`, `b(δ) = 3 + 8δ/(1+δ)`,
`V*(1;δ) = 11` — CONSTANT. The transition weight moves the whole affine
profile (`c' = −32/9`, `b' = +32/9` at `δ = 1/2`) but the two responses
offset exactly at the absorbing state. -/

/-- The eeCert `δ` window sits inside the parameter space `(0,1)`. -/
theorem eeD_δ_mem {dd : ℝ} (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    dd ∈ Set.Ioo (0:ℝ) 1 :=
  ⟨by linarith [hdd.1], by linarith [hdd.2]⟩

/-- **The eeCert `δ`-family** on the exact persistence window. -/
def eeCertParamsD (dd : ℝ) (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    AbstractGame.Params :=
  eeCertParamsGen (1/2) (9/10) dd mem_half_Ico mem_910_Ico (eeD_δ_mem hdd)

/-- Pinned equilibrium slope `c(δ) = 8/(1+δ)`. -/
def eeSlopeD (dd : ℝ) : ℝ := 8 / (1 + dd)

/-- Pinned equilibrium intercept `b(δ) = 3 + 8δ/(1+δ)`. -/
def eeInterceptD (dd : ℝ) : ℝ := 3 + 8 * dd / (1 + dd)

/-- The `δ`-re-pinned Sender carrier: slope `c(δ)`, radius `11`
(= the `δ`-invariant lock-in value; tight). -/
def eeCarrierSD (dd : ℝ) : Set Val :=
  valLipGainBall 11 (eeSlopeD dd) (eeSlopeD dd) 0

/-- The pinned equilibrium value family `V_S*(x;δ) = b(δ) + c(δ)·x`. -/
def eeVSstarD (dd : ℝ) : Val :=
  affineInterceptBCF (eeInterceptD dd) (eeSlopeD dd)

theorem eeSlopeD_nonneg {dd : ℝ} (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    0 ≤ eeSlopeD dd :=
  div_nonneg (by norm_num) (by linarith [hdd.1])

/-- **Binding-below window constraint (all-compliance corner chord in
`δ`)**: `β·c(δ)·δ = 4δ/(1+δ) ≥ 6/5` exactly at `δ ≥ 3/7` (closed
endpoint admissible: strictness from `s₁ < s₂`). -/
theorem eeCertD_chord {dd : ℝ} (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    6/5 ≤ 1/2 * eeSlopeD dd * dd := by
  have h1 : (0:ℝ) < 1 + dd := by linarith [hdd.1]
  have h1' : (1:ℝ) + dd ≠ 0 := ne_of_gt h1
  have key : 1/2 * eeSlopeD dd * dd - 6/5 = (14 * dd - 6) / (5 * (1 + dd)) := by
    unfold eeSlopeD
    field_simp
    ring
  have hnn : (0:ℝ) ≤ (14 * dd - 6) / (5 * (1 + dd)) :=
    div_nonneg (by linarith [hdd.1]) (by linarith)
  linarith [key, hnn]

/-- **Binding-above window constraint (STRICT certificate margin in
`δ`)**: `β·K_S·δ = 4δ/(1+δ) < 8/5 = m_S` exactly for `δ < 2/3`. -/
theorem eeCertD_hS_margin {dd : ℝ} (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    1/2 * eeSlopeD dd * dd < 8/5 := by
  have h1 : (0:ℝ) < 1 + dd := by linarith [hdd.1]
  have h1' : (1:ℝ) + dd ≠ 0 := ne_of_gt h1
  have key : 8/5 - 1/2 * eeSlopeD dd * dd = (8 - 12 * dd) / (5 * (1 + dd)) := by
    unfold eeSlopeD
    field_simp
    ring
  have hpos : (0:ℝ) < (8 - 12 * dd) / (5 * (1 + dd)) :=
    div_pos (by linarith [hdd.2]) (by linarith)
  linarith [key, hpos]

/-- Policy invariance across the `δ`-window: `σ_dyn_top ≡ 1` at every
physical state and compliance level, uniformly in `δ ∈ [3/7, 2/3)`. -/
theorem eeCertD_σ_dyn_top_eq_one (dd : ℝ) (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3))
    {V_S : Val} (hV_S : V_S ∈ eeCarrierSD dd)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    (eeCertParamsD dd hdd).σ_dyn_top V_S x a = 1 :=
  eeGen_σ_dyn_top_eq_one mem_half_Ico mem_910_Ico (eeD_δ_mem hdd)
    (eeSlopeD_nonneg hdd) (eeCertD_chord hdd) hV_S hx ha

/-- **THE δ-INVARIANCE OF THE LOCK-IN VALUE (coefficient identity)**:
`b(δ) + c(δ) = 11` for EVERY `δ` in the persistence window —
`dV*(1)/dδ = 0` exactly. In economic terms: the equilibrium lock-in
value is the capitalized corner flow `U_S(1,0,1)/(1−β_S) = (11/2)/(1/2)`,
and the corner flow does not depend on how fast the political state
adjusts. A faster transition tilts the value profile (slope down,
intercept up, `∓32/9` at `δ = 1/2`) but leaves the absorbing-state value
untouched: `δ` is a PURE TRANSITION-PATH parameter for lock-in welfare,
not a lock-in-depth parameter. This is new economics delivered by the
pinned-fixed-point route — no envelope theorem is invoked; the identity
is exact, not first-order.

Cross-reference (BH6.3): the general-`F` capitalisation theorem
`senderValue_lockin_capitalised_of_bellman` (`cornerValue_lockin_capitalised_of_bellman`
at `u := U_S`) gives `V_S*(1) = U_S(1,0,1)/(1−β_S)` for every transition, so the
invariance is to the whole transition law, not only to `δ`. This lemma is kept
as the coefficient algebra the pinned fixed point is built from. -/
theorem eeCertD_lockin_value_invariant {dd : ℝ}
    (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    eeInterceptD dd + eeSlopeD dd = 11 := by
  have h1 : (1:ℝ) + dd ≠ 0 := ne_of_gt (by linarith [hdd.1] : (0:ℝ) < 1 + dd)
  unfold eeInterceptD eeSlopeD
  field_simp
  ring

/-- The pinned `δ`-family value lives in the re-pinned carrier. -/
theorem eeVSstarD_mem {dd : ℝ} (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    eeVSstarD dd ∈ eeCarrierSD dd := by
  have h1 : (0:ℝ) < 1 + dd := by linarith [hdd.1]
  have hb : 0 ≤ eeInterceptD dd := by
    have : (0:ℝ) ≤ 8 * dd / (1 + dd) :=
      div_nonneg (by linarith [hdd.1]) h1.le
    unfold eeInterceptD
    linarith
  exact affineInterceptBCF_mem_gainBall hb (eeSlopeD_nonneg hdd)
    (le_of_eq (eeCertD_lockin_value_invariant hdd))

/-- **The parametrized pinned fixed point (`δ`-channel)**: for every
`δ` in the window, the Sender Bellman operator at the defiance policy
fixes `V_S*(x;δ) = 3 + 8δ/(1+δ) + 8/(1+δ)·x` exactly. Reproduces the
shipped pin `(17/3, 16/3)` at `δ = 1/2`. -/
theorem eeCertD_VS_star_fixed (dd : ℝ) (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    (eeCertParamsD dd hdd).bellmanS_BCF (fun _ => 0) continuous_const
        (eeVSstarD dd)
      = eeVSstarD dd := by
  ext y
  refine Eq.trans (eeGen_bellmanS_image mem_half_Ico mem_910_Ico
    (eeD_δ_mem hdd) (eeSlopeD_nonneg hdd) (eeVSstarD_mem hdd) y) ?_
  have h1 : (1:ℝ) + dd ≠ 0 := ne_of_gt (by linarith [hdd.1] : (0:ℝ) < 1 + dd)
  have hmem : (1 - dd) * y.val + dd ∈ Set.Icc (0:ℝ) 1 :=
    mem_affine_corner (eeD_δ_mem hdd) y.property
  simp only [eeVSstarD, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  unfold eeInterceptD eeSlopeD
  field_simp
  ring

/-- The `δ`-family reproduces the shipped `δ = 1/2` pin (Rule 5). -/
theorem eeVSstarD_half : eeVSstarD (1/2) = eeVSstar := by
  unfold eeVSstarD eeVSstar eeInterceptD eeSlopeD
  norm_num

/-- Game-tied form of the δ-invariance: the pinned equilibrium value at
the absorbing state is `11` for every window `δ`. -/
theorem eeVSstarD_lockin_eval {dd : ℝ} (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    eeVSstarD dd (Sanctions.clipS' 1) = 11 := by
  simp only [eeVSstarD, affineInterceptBCF_apply,
    clipS'_val_of_mem (⟨by norm_num, le_refl 1⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
  rw [mul_one]
  exact eeCertD_lockin_value_invariant hdd

/-- FULL slope response in `δ`: `dc/dδ = −8/(1+δ)²` on the window. -/
theorem eeSlopeD_hasDerivAt {dd : ℝ} (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    HasDerivAt eeSlopeD (-(8 / (1 + dd)^2)) dd := by
  have h1 : (1:ℝ) + dd ≠ 0 := ne_of_gt (by linarith [hdd.1] : (0:ℝ) < 1 + dd)
  have hden : HasDerivAt (fun t : ℝ => 1 + t) 1 dd := by
    simpa using (hasDerivAt_id dd).const_add 1
  have h := (hasDerivAt_const dd (8:ℝ)).fun_div hden h1
  convert h using 1
  ring

/-- FULL slope response at the witness point: `dc/dδ = −32/9` at
`δ = 1/2`. -/
theorem eeSlopeD_hasDerivAt_half : HasDerivAt eeSlopeD (-32/9) (1/2:ℝ) := by
  have h := eeSlopeD_hasDerivAt (dd := 1/2) ⟨by norm_num, by norm_num⟩
  convert h using 1
  norm_num

/-- FULL intercept response in `δ`: `db/dδ = +8/(1+δ)²` — the exact
mirror image of the slope response. -/
theorem eeInterceptD_hasDerivAt {dd : ℝ} (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    HasDerivAt eeInterceptD (8 / (1 + dd)^2) dd := by
  have h1 : (1:ℝ) + dd ≠ 0 := ne_of_gt (by linarith [hdd.1] : (0:ℝ) < 1 + dd)
  have hnum : HasDerivAt (fun t : ℝ => 8 * t) 8 dd := hasDerivAt_const_mul 8
  have hden : HasDerivAt (fun t : ℝ => 1 + t) 1 dd := by
    simpa using (hasDerivAt_id dd).const_add 1
  have h := (hnum.fun_div hden h1).const_add (3:ℝ)
  convert h using 1
  ring

/-- FULL intercept response at the witness point: `db/dδ = +32/9` at
`δ = 1/2`. -/
theorem eeInterceptD_hasDerivAt_half :
    HasDerivAt eeInterceptD (32/9) (1/2:ℝ) := by
  have h := eeInterceptD_hasDerivAt (dd := 1/2) ⟨by norm_num, by norm_num⟩
  convert h using 1
  norm_num

/-- **The δ-invariance at the derivative level**: the lock-in value map
`δ ↦ b(δ) + c(δ)` has derivative EXACTLY ZERO at every window `δ` —
slope and intercept responses offset one-for-one at the absorbing
state. -/
theorem eeCertD_lockin_hasDerivAt_zero {dd : ℝ}
    (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    HasDerivAt (fun t : ℝ => eeInterceptD t + eeSlopeD t) 0 dd := by
  have h := (eeInterceptD_hasDerivAt hdd).add (eeSlopeD_hasDerivAt hdd)
  convert h using 1
  ring

/-- **DIRECT effect of `δ` in closed form**: one Bellman application
with transition weight `δ` at the FROZEN old (`δ = 1/2`) pin `eeVSstar`
evaluates to `13/3 + (8/3)δ + (20/3 − (8/3)δ)·x` — direct slope response
`−8/3`, direct intercept response `+8/3`. -/
theorem eeCertD_direct_eval (dd : ℝ) (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3))
    (y : ↥(Sanctions.S : Set ℝ)) :
    (eeCertParamsD dd hdd).bellmanS_BCF (fun _ => 0) continuous_const
        eeVSstar y
      = 13/3 + 8/3 * dd + (20/3 - 8/3 * dd) * y.val := by
  refine Eq.trans (eeGen_bellmanS_image mem_half_Ico mem_910_Ico
    (eeD_δ_mem hdd) (by norm_num : (0:ℝ) ≤ 16/3) (mem_eeCarrierS_num eeVSstar_mem) y) ?_
  have hmem : (1 - dd) * y.val + dd ∈ Set.Icc (0:ℝ) 1 :=
    mem_affine_corner (eeD_δ_mem hdd) y.property
  simp only [eeVSstar, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  ring

/-- **DIRECT lock-in effect of `δ` is ALSO exactly zero**: the
frozen-value Bellman application at the absorbing state is `11`,
constant in `δ` — at `x = 1` the transition does not move
(`F(1,1) = 1`), so neither the direct nor the feedback channel can
shift the lock-in value. `0 = 0 + 0` split. -/
theorem eeCertD_direct_lockin_eval (dd : ℝ)
    (hdd : dd ∈ Set.Ico (3/7:ℝ) (2/3)) :
    (eeCertParamsD dd hdd).bellmanS_BCF (fun _ => 0) continuous_const
        eeVSstar (Sanctions.clipS' 1)
      = 11 := by
  rw [eeCertD_direct_eval dd hdd (Sanctions.clipS' 1),
      clipS'_val_of_mem (⟨by norm_num, le_refl 1⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
  ring

/-- **Split, `δ`-slope channel**: `−32/9 = −8/3 + (−8/9)` — the
feedback term amplifies the direct sign (both negative); at the
lock-in state the split is `0 = 0 + 0`. -/
theorem eeCertD_slope_split :
    (-32:ℝ)/9 = -8/3 + -8/9 ∧ (-8:ℝ)/9 < 0 ∧ (0:ℝ) = 0 + 0 := by
  norm_num

/-! ## 7. The general fgc corner cascade

Structural deviation recorded at `FourGroupCertWitness.lean:36` and
respected here: the microfounded `U_S` has no direct-`x` term, so the
Sender corner pin CANNOT hold at all compliance levels — it is proved
at the defiance policy `a = 0` ONLY, where the stage chord
`2 + x − (s₁+s₂)/2 ≥ 1 > 0` is parameter-free (hence the FULL `β_S`
window). The leader side is discharged by the chord decomposition of
the joint integrand, whose bracket condition `14/5 ≤ β_T·c_T·δ` IS the
window constraint of the Target channels. -/

/-- Sender dynamic objective strictly increasing at `a = 0`, for every
`(β_S, β_T, δ)` — parameter-free stage chord plus nonnegative
continuation. -/
theorem fgcGen_senderObj_strictMonoOn {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {c M : ℝ} (hc : 0 ≤ c) {V_S : Val} (hV_S : V_S ∈ valLipGainBall M c c 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    StrictMonoOn
      (fun s => (fgcParamsGen βS βT d hβS hβT hd).U_S x 0 s
        + (fgcParamsGen βS βT d hβS hβT hd).β_S
          * V_S (Sanctions.clipS'
              ((fgcParamsGen βS βT d hβS hβT hd).F x s)))
      Sanctions.I := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hmem₁ : (1 - d) * x + d * s₁ ∈ Set.Icc (0:ℝ) 1 :=
    AbstractGame.affineF_mem hd x s₁ hx hs₁
  have hmem₂ : (1 - d) * x + d * s₂ ∈ Set.Icc (0:ℝ) 1 :=
    AbstractGame.affineF_mem hd x s₂ hx hs₂
  have hdiff := gainBall_clip_diff hc hV_S hmem₁ hmem₂
  simp only [fgcParamsGen_U_S, fgcParamsGen_β_S, fgcParamsGen_F]
  have hVdiff : βS * (V_S (Sanctions.clipS' ((1 - d) * x + d * s₂))
        - V_S (Sanctions.clipS' ((1 - d) * x + d * s₁)))
      = βS * c * d * (s₂ - s₁) := by
    rw [hdiff]; ring
  have hVpos : (0:ℝ) ≤ βS * c * d * (s₂ - s₁) :=
    mul_nonneg (mul_nonneg (mul_nonneg hβS.1 hc) hd.1.le) (by linarith)
  have hcoef : (0:ℝ) < 2 + x - (s₁ + s₂)/2 := by
    linarith [hx.1, hs₁.2, hs₂.2]
  have hprod := mul_pos (show (0:ℝ) < s₂ - s₁ by linarith) hcoef
  nlinarith [hVdiff, hVpos, hprod]

/-- `σ_dyn(·, 0)` pinned at the corner `1` — the fgc defiance-policy pin
(parameter-free: holds on the FULL `β_S` window `[0,1)`). -/
theorem fgcGen_σ_dyn_zero_eq_one {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {c M : ℝ} (hc : 0 ≤ c) {V_S : Val} (hV_S : V_S ∈ valLipGainBall M c c 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (fgcParamsGen βS βT d hβS hβT hd).σ_dyn V_S x 0 = 1 :=
  WitnessKit.σ_dyn_eq_one_of_strictMonoOn
    (fgcGen_senderObj_strictMonoOn hβS hβT hd hc hV_S hx)

/-- State-local Sender argmax uniqueness on any slope-pinned carrier at
the fgc family (strictly concave parabola; no window condition). -/
theorem fgcGen_DAU_on_carrier {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {c M : ℝ} (hc : 0 ≤ c) {V_S : Val} (hV_S : V_S ∈ valLipGainBall M c c 0) :
    (fgcParamsGen βS βT d hβS hβT hd).DynamicArgmaxUnique V_S := by
  apply (fgcParamsGen βS βT d hβS hβT hd).dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  set c₀ := V_S (Sanctions.clipS' 0) with hc₀
  have hQ : ∀ s ∈ Sanctions.I,
      (fgcParamsGen βS βT d hβS hβT hd).U_S x a s
          + (fgcParamsGen βS βT d hβS hβT hd).β_S
            * V_S (Sanctions.clipS'
                ((fgcParamsGen βS βT d hβS hβT hd).F x s))
        = -(1/2) * s ^ 2 + (2 + x - 11/5 * a + βS * c * d) * s
          + (βS * c₀ + βS * c * (1 - d) * x) := by
    intro s hs
    have hmem : (1 - d) * x + d * s ∈ Set.Icc (0:ℝ) 1 :=
      AbstractGame.affineF_mem hd x s hx hs
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
    have hdiff := gainBall_clip_diff hc hV_S h0 hmem
    simp only [fgcParamsGen_U_S, fgcParamsGen_β_S, fgcParamsGen_F]
    rw [hc₀]
    linear_combination βS * hdiff
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne pp qq hp hq hpq
  have hq_eq : qq = 1 - pp := by linarith
  subst hq_eq
  have hmid : pp * s₁ + (1 - pp) * s₂ ∈ Sanctions.I :=
    ⟨by nlinarith [hs₁.1, hs₂.1, hp.le, hq.le],
     by nlinarith [hs₁.2, hs₂.2, hp.le, hq.le]⟩
  simp only [smul_eq_mul, hQ s₁ hs₁, hQ s₂ hs₂, hQ _ hmid]
  have hsq : (s₁ - s₂) ^ 2 > 0 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  nlinarith [mul_pos (mul_pos hp hq) hsq]

/-- fgc Sender Bellman image in closed form at the defiance policy:
`3/2 + x + β_S·W(clip((1−δ)x + δ))`. -/
theorem fgcGen_bellmanS_image {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {c M : ℝ} (hc : 0 ≤ c) {W : Val} (hW : W ∈ valLipGainBall M c c 0)
    (y : ↥(Sanctions.S : Set ℝ)) :
    (fgcParamsGen βS βT d hβS hβT hd).bellmanS_BCF (fun _ => 0)
        continuous_const W y
      = 3/2 + y.val + βS * W (Sanctions.clipS' ((1 - d) * y.val + d)) := by
  have h1I : (1:ℝ) ∈ Sanctions.I := ⟨by norm_num, le_refl 1⟩
  have hmono := fgcGen_senderObj_strictMonoOn hβS hβT hd hc hW y.property
  rw [WitnessKit.bellmanS_image_of_isMaxOn (α := fun _ => (0:ℝ))
      continuous_const W y h1I
      (isMaxOn_iff.mpr fun s hs => hmono.monotoneOn hs h1I hs.2)]
  rw [show (fgcParamsGen βS βT d hβS hβT hd).F y.val 1
        = (1 - d) * y.val + d by
      simp only [fgcParamsGen_F]; ring]
  simp only [fgcParamsGen_U_S, fgcParamsGen_β_S]
  ring

/-- fgc joint Target integrand evaluated through the closed forms
(dynamic Sender response kept symbolic). -/
theorem fgcGen_joint_T_integrand_eval {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1) (V_T V_S : Val) (x a : ℝ) :
    (fgcParamsGen βS βT d hβS hβT hd).joint_T_integrand V_T V_S x a
      = 3 * x - 1/5 * a
        + (fgcParamsGen βS βT d hβS hβT hd).σ_dyn V_S x a * (x - 14/5)
        + βT * V_T (Sanctions.clipS' ((1 - d) * x
            + d * (fgcParamsGen βS βT d hβS hβT hd).σ_dyn V_S x a)) := by
  simp only [AbstractGame.Params.joint_T_integrand, fgcParamsGen_U_T,
    fgcParamsGen_β_T, fgcParamsGen_F]

/-- **fgc chord decomposition (leader side)**: raising compliance from
`0` to `a` lowers the joint integrand by at least `(1/5)·a` whenever the
bracket condition `14/5 ≤ β_T·c_T·δ` holds — the sanction relief that
compliance might buy is worth negative to the Target on the carrier.
The bracket condition is exactly the binding constraint of the fgc
Target windows. -/
theorem fgcGen_joint_T_chord {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {cT MT : ℝ} (hcT : 0 ≤ cT) (hbracket : 14/5 ≤ βT * cT * d)
    {V_T : Val} (hV_T : V_T ∈ valLipGainBall MT cT cT 0)
    {cS MS : ℝ} (hcS : 0 ≤ cS) {V_S : Val} (hV_S : V_S ∈ valLipGainBall MS cS cS 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) {a : ℝ} (_ha : a ∈ Sanctions.I) :
    (fgcParamsGen βS βT d hβS hβT hd).joint_T_integrand V_T V_S x a
      ≤ (fgcParamsGen βS βT d hβS hβT hd).joint_T_integrand V_T V_S x 0
        - 1/5 * a := by
  have hσm := (fgcParamsGen βS βT d hβS hβT hd).σ_dyn_mem V_S x a
  have hσ0 := fgcGen_σ_dyn_zero_eq_one hβS hβT hd hcS hV_S hx
  have hmem₁ : (1 - d) * x
      + d * (fgcParamsGen βS βT d hβS hβT hd).σ_dyn V_S x a
      ∈ Set.Icc (0:ℝ) 1 :=
    AbstractGame.affineF_mem hd x _ hx hσm
  have hmem₂ : (1 - d) * x + d * 1 ∈ Set.Icc (0:ℝ) 1 :=
    AbstractGame.affineF_mem hd x 1 hx ⟨by norm_num, le_refl 1⟩
  have hdiff := gainBall_clip_diff hcT hV_T hmem₂ hmem₁
  rw [fgcGen_joint_T_integrand_eval hβS hβT hd V_T V_S x a,
      fgcGen_joint_T_integrand_eval hβS hβT hd V_T V_S x 0, hσ0]
  have hVdiff : βT * (V_T (Sanctions.clipS' ((1 - d) * x
          + d * (fgcParamsGen βS βT d hβS hβT hd).σ_dyn V_S x a))
        - V_T (Sanctions.clipS' ((1 - d) * x + d * 1)))
      = βT * cT * d
        * ((fgcParamsGen βS βT d hβS hβT hd).σ_dyn V_S x a - 1) := by
    rw [hdiff]; ring
  have hkey : (0:ℝ) ≤ (1 - (fgcParamsGen βS βT d hβS hβT hd).σ_dyn V_S x a)
      * (x - 14/5 + βT * cT * d) :=
    mul_nonneg (by linarith [hσm.2]) (by linarith [hbracket, hx.1])
  nlinarith [hVdiff, hkey]

/-- fgc: full defiance `a = 0` is the Target argmax at every physical
state (under the bracket condition). -/
theorem fgcGen_zero_isMaxOn_joint {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {cT MT : ℝ} (hcT : 0 ≤ cT) (hbracket : 14/5 ≤ βT * cT * d)
    {V_T : Val} (hV_T : V_T ∈ valLipGainBall MT cT cT 0)
    {cS MS : ℝ} (hcS : 0 ≤ cS) {V_S : Val} (hV_S : V_S ∈ valLipGainBall MS cS cS 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    IsMaxOn
      (fun a => (fgcParamsGen βS βT d hβS hβT hd).joint_T_integrand
        V_T V_S x a)
      Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  have h := fgcGen_joint_T_chord hβS hβT hd hcT hbracket hV_T hcS hV_S hx ha
  have := ha.1
  linarith

/-- fgc joint Target Bellman image in closed form: the sSup collapses
at the defiance corner (where `σ_dyn = 1`). -/
theorem fgcGen_jointTarget_image {βS βT d : ℝ}
    (hβS : βS ∈ Set.Ico (0:ℝ) 1) (hβT : βT ∈ Set.Ico (0:ℝ) 1)
    (hd : d ∈ Set.Ioo (0:ℝ) 1)
    {cT MT : ℝ} (hcT : 0 ≤ cT) (hbracket : 14/5 ≤ βT * cT * d)
    {V_T : Val} (hV_T : V_T ∈ valLipGainBall MT cT cT 0)
    {cS MS : ℝ} (hcS : 0 ≤ cS) {V_S : Val} (hV_S : V_S ∈ valLipGainBall MS cS cS 0)
    (hDAU : (fgcParamsGen βS βT d hβS hβT hd).DynamicArgmaxUnique V_S)
    (y : ↥(Sanctions.S : Set ℝ)) :
    (fgcParamsGen βS βT d hβS hβT hd).jointTarget_BCF_on_S V_T V_S hDAU.toOnI y
      = 4 * y.val - 14/5
        + βT * V_T (Sanctions.clipS' ((1 - d) * y.val + d)) := by
  rw [WitnessKit.jointTarget_image_of_isMaxOn V_T V_S hDAU.toOnI y
        (⟨le_refl 0, by norm_num⟩ : (0:ℝ) ∈ Sanctions.I)
        (fgcGen_zero_isMaxOn_joint hβS hβT hd hcT hbracket hV_T hcS hV_S
          y.property),
      fgcGen_joint_T_integrand_eval hβS hβT hd V_T V_S y.val 0,
      fgcGen_σ_dyn_zero_eq_one hβS hβT hd hcS hV_S y.property,
      show (1 - d) * y.val + d * (1:ℝ) = (1 - d) * y.val + d by ring]
  ring

/-! ## 8. The fgc Sender `β_S`-family on the FULL window `[0, 1)`

Pinned coefficients: `c(β) = 2/(2−β)`, `b(β) = (6−β)/(2(1−β)(2−β))`,
`V*(1;β) = (5/2)/(1−β)`. The window is the whole parameter space: the
`a = 0` corner pin is `β`-free, and the strict margin
`β·K_S·δ = β/(2−β) < 3/2 = m_S` crosses only at `β = 6/5 > 1`. -/

/-- **The fgc Sender `β_S`-family** (full parameter-space window). -/
def fgcParamsB (β : ℝ) (hβ : β ∈ Set.Ico (0:ℝ) 1) :
    AbstractGame.Params :=
  fgcParamsGen β (9/10) (1/2) hβ mem_910_Ico mem_half_Ioo

/-- fgc pinned Sender slope `c(β) = 2/(2−β)`. -/
def fgcSlopeB (β : ℝ) : ℝ := 2 / (2 - β)

/-- fgc pinned Sender intercept `b(β) = (6−β)/(2(1−β)(2−β))`. -/
def fgcInterceptB (β : ℝ) : ℝ := (6 - β) / (2 * (1 - β) * (2 - β))

/-- fgc pinned Sender lock-in value `V*(1;β) = (5/2)/(1−β)` (the
capitalized corner flow `U_S(1,0,1) = 5/2`). -/
def fgcLockinB (β : ℝ) : ℝ := (5/2) / (1 - β)

/-- The `β`-re-pinned fgc Sender carrier (tight radius `V*(1;β)`). -/
def fgcCarrierSB (β : ℝ) : Set Val :=
  valLipGainBall (fgcLockinB β) (fgcSlopeB β) (fgcSlopeB β) 0

/-- The fgc pinned Sender value family `V_S*(x;β) = b(β) + c(β)·x`. -/
def fgcVSstarB (β : ℝ) : Val :=
  affineInterceptBCF (fgcInterceptB β) (fgcSlopeB β)

theorem fgcSlopeB_nonneg {β : ℝ} (hβ : β ∈ Set.Ico (0:ℝ) 1) :
    0 ≤ fgcSlopeB β :=
  div_nonneg (by norm_num) (by linarith [hβ.2])

/-- **The fgc margin never binds below `β = 1`**: the strict certificate
margin `β·K_S·δ = β/(2−β) < 3/2 = m_S` holds on the WHOLE parameter
space (it would cross only at `β = 6/5 > 1`) — hence the full window,
in contrast to the eeCert `4/7` cap. -/
theorem fgcB_hS_margin {β : ℝ} (hβ : β ∈ Set.Ico (0:ℝ) 1) :
    β * fgcSlopeB β * (1/2) < 3/2 := by
  have h2 : (0:ℝ) < 2 - β := by linarith [hβ.2]
  have h2' : (2:ℝ) - β ≠ 0 := ne_of_gt h2
  have key : 3/2 - β * fgcSlopeB β * (1/2) = (6 - 5 * β) / (2 * (2 - β)) := by
    unfold fgcSlopeB
    field_simp
    ring
  have hpos : (0:ℝ) < (6 - 5 * β) / (2 * (2 - β)) :=
    div_pos (by linarith [hβ.2]) (by linarith)
  linarith [key, hpos]

/-- fgc defiance-policy corner pin at the family: `σ_dyn(·,0) = 1` for
every carrier member, every physical state, and EVERY `β ∈ [0,1)`. -/
theorem fgcB_σ_dyn_zero_eq_one (β : ℝ) (hβ : β ∈ Set.Ico (0:ℝ) 1)
    {V_S : Val} (hV_S : V_S ∈ fgcCarrierSB β)
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (fgcParamsB β hβ).σ_dyn V_S x 0 = 1 :=
  fgcGen_σ_dyn_zero_eq_one hβ mem_910_Ico mem_half_Ioo
    (fgcSlopeB_nonneg hβ) hV_S hx

/-- fgc Sender coefficients tile the lock-in value:
`b(β) + c(β) = (5/2)/(1−β)`. -/
theorem fgcB_lockin_identity {β : ℝ} (hβ : β ∈ Set.Ico (0:ℝ) 1) :
    fgcInterceptB β + fgcSlopeB β = fgcLockinB β := by
  have h1 : (1:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 1 - β)
  have h2 : (2:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 2 - β)
  unfold fgcInterceptB fgcSlopeB fgcLockinB
  field_simp
  ring

/-- The fgc pinned family value lives in the re-pinned carrier. -/
theorem fgcVSstarB_mem {β : ℝ} (hβ : β ∈ Set.Ico (0:ℝ) 1) :
    fgcVSstarB β ∈ fgcCarrierSB β := by
  have h1 : (0:ℝ) < 1 - β := by linarith [hβ.2]
  have h2 : (0:ℝ) < 2 - β := by linarith [hβ.2]
  have hden : (0:ℝ) < 2 * (1 - β) * (2 - β) := by
    nlinarith [mul_pos h1 h2]
  exact affineInterceptBCF_mem_gainBall
    (div_nonneg (by linarith [hβ.2]) hden.le)
    (fgcSlopeB_nonneg hβ)
    (le_of_eq (fgcB_lockin_identity hβ))

/-- **The fgc Sender parametrized pinned fixed point**: for EVERY
`β ∈ [0,1)`, the Sender Bellman operator at the defiance policy fixes
`V_S*(x;β) = (6−β)/(2(1−β)(2−β)) + 2/(2−β)·x` exactly. Reproduces the
shipped microfounded pin `(11/3, 4/3)` at `β = 1/2`. -/
theorem fgcB_VS_star_fixed (β : ℝ) (hβ : β ∈ Set.Ico (0:ℝ) 1) :
    (fgcParamsB β hβ).bellmanS_BCF (fun _ => 0) continuous_const
        (fgcVSstarB β)
      = fgcVSstarB β := by
  ext y
  refine Eq.trans (fgcGen_bellmanS_image hβ mem_910_Ico mem_half_Ioo
    (fgcSlopeB_nonneg hβ) (fgcVSstarB_mem hβ) y) ?_
  have h1 : (1:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 1 - β)
  have h2 : (2:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 2 - β)
  have hmem : ((1:ℝ) - 1/2) * y.val + 1/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [y.property.1], by linarith [y.property.2]⟩
  simp only [fgcVSstarB, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  unfold fgcInterceptB fgcSlopeB
  field_simp
  ring

/-- The fgc family reproduces the shipped `β = 1/2` pin (Rule 5). -/
theorem fgcVSstarB_half : fgcVSstarB (1/2) = fgcVSstar := by
  unfold fgcVSstarB fgcVSstar fgcInterceptB fgcSlopeB
  norm_num

/-- fgc FULL slope response: `dc/dβ = 2/(2−β)²`; `8/9` at `β = 1/2`. -/
theorem fgcSlopeB_hasDerivAt {β : ℝ} (hβ : β ∈ Set.Ico (0:ℝ) 1) :
    HasDerivAt fgcSlopeB (2 / (2 - β)^2) β := by
  have h2 : (2:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 2 - β)
  have hden : HasDerivAt (fun t : ℝ => 2 - t) (-1) β := by
    simpa using (hasDerivAt_id β).const_sub 2
  have h := (hasDerivAt_const β (2:ℝ)).fun_div hden h2
  convert h using 1
  ring

/-- fgc FULL slope response at the witness point: `dc/dβ = 8/9`. -/
theorem fgcSlopeB_hasDerivAt_half : HasDerivAt fgcSlopeB (8/9) (1/2:ℝ) := by
  have h := fgcSlopeB_hasDerivAt (β := 1/2) ⟨by norm_num, by norm_num⟩
  convert h using 1
  norm_num

/-- fgc FULL intercept response at the witness point: `db/dβ = 82/9`. -/
theorem fgcInterceptB_hasDerivAt_half :
    HasDerivAt fgcInterceptB (82/9) (1/2:ℝ) := by
  have hnum : HasDerivAt (fun t : ℝ => 6 - t) (-1) (1/2:ℝ) := by
    simpa using (hasDerivAt_id (1/2:ℝ)).const_sub 6
  have hden : HasDerivAt (fun t : ℝ => 2 * (1 - t) * (2 - t)) (-4) (1/2:ℝ) := by
    have hsub1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) (1/2:ℝ) := by
      simpa using (hasDerivAt_id (1/2:ℝ)).const_sub 1
    have h1 : HasDerivAt (fun t : ℝ => 2 * (1 - t)) (-2) (1/2:ℝ) := by
      have := hsub1.const_mul (2:ℝ)
      convert this using 1
      norm_num
    have h2 : HasDerivAt (fun t : ℝ => 2 - t) (-1) (1/2:ℝ) := by
      simpa using (hasDerivAt_id (1/2:ℝ)).const_sub 2
    have h := h1.mul h2
    convert h using 1
    norm_num
  have h := hnum.fun_div hden (by norm_num)
  convert h using 1
  norm_num

/-- fgc FULL lock-in response: `dV*(1)/dβ = (5/2)/(1−β)²`; `10` at
`β = 1/2`. -/
theorem fgcLockinB_hasDerivAt {β : ℝ} (hβ : β ∈ Set.Ico (0:ℝ) 1) :
    HasDerivAt fgcLockinB ((5/2) / (1 - β)^2) β := by
  have h1 : (1:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 1 - β)
  have hden : HasDerivAt (fun t : ℝ => 1 - t) (-1) β := by
    simpa using (hasDerivAt_id β).const_sub 1
  have h := (hasDerivAt_const β ((5:ℝ)/2)).fun_div hden h1
  convert h using 1
  ring

/-- fgc FULL lock-in response at the witness point: `dV*(1)/dβ = 10`. -/
theorem fgcLockinB_hasDerivAt_half : HasDerivAt fgcLockinB 10 (1/2:ℝ) := by
  have h := fgcLockinB_hasDerivAt (β := 1/2) ⟨by norm_num, by norm_num⟩
  convert h using 1
  norm_num

/-- fgc resolvent identity: `dV*(1)/dβ = V*(1;β)/(1−β)`. -/
theorem fgcLockinB_resolvent {β : ℝ} (hβ : β ∈ Set.Ico (0:ℝ) 1) :
    HasDerivAt fgcLockinB (fgcLockinB β / (1 - β)) β := by
  have h1 : (1:ℝ) - β ≠ 0 := ne_of_gt (by linarith [hβ.2] : (0:ℝ) < 1 - β)
  have h := fgcLockinB_hasDerivAt hβ
  rw [show fgcLockinB β / (1 - β) = (5/2) / (1 - β)^2 by
    unfold fgcLockinB
    field_simp]
  exact h

/-- fgc DIRECT effect in closed form: one Bellman application with
patience `β` at the FROZEN old pin `fgcVSstar` evaluates to
`3/2 + (13/3)β + (1 + (2/3)β)·x` — direct intercept response `13/3`,
direct slope response `2/3`. -/
theorem fgcB_direct_eval (β : ℝ) (hβ : β ∈ Set.Ico (0:ℝ) 1)
    (y : ↥(Sanctions.S : Set ℝ)) :
    (fgcParamsB β hβ).bellmanS_BCF (fun _ => 0) continuous_const
        fgcVSstar y
      = 3/2 + 13/3 * β + (1 + 2/3 * β) * y.val := by
  refine Eq.trans (fgcGen_bellmanS_image hβ mem_910_Ico mem_half_Ioo
    (by norm_num : (0:ℝ) ≤ 4/3) (mem_fgcCarrierS_num fgcVSstar_mem) y) ?_
  have hmem : ((1:ℝ) - 1/2) * y.val + 1/2 ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [y.property.1], by linarith [y.property.2]⟩
  simp only [fgcVSstar, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  ring

/-- fgc DIRECT effect at the absorbing state: `5/2 + 5β` — direct
lock-in response `5` per unit of patience. -/
theorem fgcB_direct_lockin_eval (β : ℝ) (hβ : β ∈ Set.Ico (0:ℝ) 1) :
    (fgcParamsB β hβ).bellmanS_BCF (fun _ => 0) continuous_const
        fgcVSstar (Sanctions.clipS' 1)
      = 5/2 + 5 * β := by
  rw [fgcB_direct_eval β hβ (Sanctions.clipS' 1),
      clipS'_val_of_mem (⟨by norm_num, le_refl 1⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
  ring

/-- **fgc splits (machine-checked)**: slope `8/9 = 2/3 + 2/9`,
intercept `82/9 = 13/3 + 43/9`, lock-in `10 = 5 + 5` with amplification
`10 = 5/(1 − 1/2)` — all feedback terms strictly positive. -/
theorem fgcB_splits :
    ((8:ℝ)/9 = 2/3 + 2/9 ∧ (0:ℝ) < 2/9)
      ∧ ((82:ℝ)/9 = 13/3 + 43/9 ∧ (0:ℝ) < 43/9)
      ∧ ((10:ℝ) = 5 + 5 ∧ (0:ℝ) < 5 ∧ (10:ℝ) = 5 / (1 - 1/2)) := by
  norm_num

/-- fgc exact finite-difference decomposition
`ΔV(x) = Δβ·V₂(F(x,1)) + β₁·ΔV(F(x,1))` (direct + feedback). -/
theorem fgcB_feedback_decomposition (β₁ β₂ : ℝ)
    (hβ₁ : β₁ ∈ Set.Ico (0:ℝ) 1) (hβ₂ : β₂ ∈ Set.Ico (0:ℝ) 1)
    (y : ↥(Sanctions.S : Set ℝ)) :
    fgcVSstarB β₂ y - fgcVSstarB β₁ y
      = (β₂ - β₁) * fgcVSstarB β₂ (Sanctions.clipS' ((y.val + 1)/2))
        + β₁ * (fgcVSstarB β₂ (Sanctions.clipS' ((y.val + 1)/2))
            - fgcVSstarB β₁ (Sanctions.clipS' ((y.val + 1)/2))) := by
  have h1a : (1:ℝ) - β₁ ≠ 0 := ne_of_gt (by linarith [hβ₁.2] : (0:ℝ) < 1 - β₁)
  have h1b : (2:ℝ) - β₁ ≠ 0 := ne_of_gt (by linarith [hβ₁.2] : (0:ℝ) < 2 - β₁)
  have h2a : (1:ℝ) - β₂ ≠ 0 := ne_of_gt (by linarith [hβ₂.2] : (0:ℝ) < 1 - β₂)
  have h2b : (2:ℝ) - β₂ ≠ 0 := ne_of_gt (by linarith [hβ₂.2] : (0:ℝ) < 2 - β₂)
  simp only [fgcVSstarB, affineInterceptBCF_apply,
    clipS'_val_of_mem (mem_half_shift y)]
  unfold fgcInterceptB fgcSlopeB
  field_simp
  ring

/-- fgc lock-in amplification identity
`(1−β₁)·ΔV*(1) = Δβ·V*(1;β₂)`. -/
theorem fgcB_lockin_amplification (β₁ β₂ : ℝ)
    (hβ₁ : β₁ ∈ Set.Ico (0:ℝ) 1) (hβ₂ : β₂ ∈ Set.Ico (0:ℝ) 1) :
    (1 - β₁) * (fgcLockinB β₂ - fgcLockinB β₁)
      = (β₂ - β₁) * fgcLockinB β₂ := by
  have h1 : (1:ℝ) - β₁ ≠ 0 := ne_of_gt (by linarith [hβ₁.2] : (0:ℝ) < 1 - β₁)
  have h2 : (1:ℝ) - β₂ ≠ 0 := ne_of_gt (by linarith [hβ₂.2] : (0:ℝ) < 1 - β₂)
  unfold fgcLockinB
  field_simp
  ring

/-- fgc Rule 16(a) ordered endpoints: at `β = 1/2 < 11/20`, slopes
`4/3 < 40/29` and lock-in values `5 < 50/9`. -/
theorem fgcB_rule16a :
    (1/2:ℝ) < 11/20
      ∧ (1/2:ℝ) ∈ Set.Ico (0:ℝ) 1 ∧ (11/20:ℝ) ∈ Set.Ico (0:ℝ) 1
      ∧ fgcSlopeB (1/2) = 4/3 ∧ fgcSlopeB (11/20) = 40/29
      ∧ fgcLockinB (1/2) = 5 ∧ fgcLockinB (11/20) = 50/9
      ∧ fgcSlopeB (1/2) < fgcSlopeB (11/20)
      ∧ fgcLockinB (1/2) < fgcLockinB (11/20) := by
  unfold fgcSlopeB fgcLockinB
  norm_num [Set.mem_Ico]

/-! ## 9. The fgc Target `β_T`-family on `[14/17, 1)`

Pinned coefficients: `c_T(γ) = 8/(2−γ)`,
`b_T(γ) = (34γ−28)/(5(1−γ)(2−γ))`, `V_T*(1;γ) = (6/5)/(1−γ)`.
NOTE: at fgc the leader chord-decomposition coefficient
`γ·c_T(γ)·δ = 4γ/(2−γ) ≥ 14/5` IS the loss-margin quantity of
`hT_loss_margin` — one binding constraint serves both the defiance pin
and the Target loss-offset margin, binding exactly at `γ = 14/17`. (Since
round BJ1.4, 2026-10-07, that margin is no longer a certificate field; it is
the margin input of the standalone discharger
`Target_combined_chord_of_decomposition_lowerChord_affine`.) -/

/-- The fgc `β_T` window sits inside the parameter space `[0,1)`. -/
theorem fgcBT_βT_mem {γ : ℝ} (hγ : γ ∈ Set.Ico (14/17:ℝ) 1) :
    γ ∈ Set.Ico (0:ℝ) 1 :=
  ⟨by linarith [hγ.1], hγ.2⟩

/-- **The fgc Target `β_T`-family** on the chord/loss-margin window. -/
def fgcParamsBT (γ : ℝ) (hγ : γ ∈ Set.Ico (14/17:ℝ) 1) :
    AbstractGame.Params :=
  fgcParamsGen (1/2) γ (1/2) mem_half_Ico (fgcBT_βT_mem hγ) mem_half_Ioo

/-- fgc pinned Target slope `c_T(γ) = 8/(2−γ)`. -/
def fgcSlopeT (γ : ℝ) : ℝ := 8 / (2 - γ)

/-- fgc pinned Target intercept `b_T(γ) = (34γ−28)/(5(1−γ)(2−γ))`. -/
def fgcInterceptT (γ : ℝ) : ℝ := (34 * γ - 28) / (5 * (1 - γ) * (2 - γ))

/-- fgc pinned Target lock-in value `V_T*(1;γ) = (6/5)/(1−γ)` (the
capitalized corner flow `U_T(1,0,1) = 6/5`). -/
def fgcLockinT (γ : ℝ) : ℝ := (6/5) / (1 - γ)

/-- The `γ`-re-pinned fgc Target carrier (tight radius `V_T*(1;γ)`). -/
def fgcCarrierTB (γ : ℝ) : Set Val :=
  valLipGainBall (fgcLockinT γ) (fgcSlopeT γ) (fgcSlopeT γ) 0

/-- The fgc pinned Target value family `V_T*(x;γ) = b_T(γ) + c_T(γ)·x`. -/
def fgcVTstarT (γ : ℝ) : Val :=
  affineInterceptBCF (fgcInterceptT γ) (fgcSlopeT γ)

theorem fgcSlopeT_nonneg {γ : ℝ} (hγ : γ ∈ Set.Ico (14/17:ℝ) 1) :
    0 ≤ fgcSlopeT γ :=
  div_nonneg (by norm_num) (by linarith [hγ.2])

/-- **The fgc Target window constraint (chord = loss margin)**:
`14/5 ≤ γ·c_T(γ)·δ = 4γ/(2−γ)` exactly at `γ ≥ 14/17` (closed endpoint
admissible: the chord bound and the loss-offset margin `hT_loss_margin` are
both non-strict). -/
theorem fgcBT_chord {γ : ℝ} (hγ : γ ∈ Set.Ico (14/17:ℝ) 1) :
    14/5 ≤ γ * fgcSlopeT γ * (1/2) := by
  have h2 : (0:ℝ) < 2 - γ := by linarith [hγ.2]
  have h2' : (2:ℝ) - γ ≠ 0 := ne_of_gt h2
  have key : γ * fgcSlopeT γ * (1/2) - 14/5
      = (34 * γ - 28) / (5 * (2 - γ)) := by
    unfold fgcSlopeT
    field_simp
    ring
  have hnn : (0:ℝ) ≤ (34 * γ - 28) / (5 * (2 - γ)) :=
    div_nonneg (by linarith [hγ.1]) (by linarith)
  linarith [key, hnn]

/-- fgc Target coefficients tile the lock-in value:
`b_T(γ) + c_T(γ) = (6/5)/(1−γ)`. -/
theorem fgcBT_lockin_identity {γ : ℝ} (hγ : γ ∈ Set.Ico (14/17:ℝ) 1) :
    fgcInterceptT γ + fgcSlopeT γ = fgcLockinT γ := by
  have h1 : (1:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 1 - γ)
  have h2 : (2:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 2 - γ)
  unfold fgcInterceptT fgcSlopeT fgcLockinT
  field_simp
  ring

/-- The fgc pinned Target family value lives in the `γ`-carrier (the
intercept is nonnegative EXACTLY on the window: `34γ − 28 ≥ 0` at
`γ ≥ 14/17`, zero at the closed endpoint). -/
theorem fgcVTstarT_mem {γ : ℝ} (hγ : γ ∈ Set.Ico (14/17:ℝ) 1) :
    fgcVTstarT γ ∈ fgcCarrierTB γ := by
  have h1 : (0:ℝ) < 1 - γ := by linarith [hγ.2]
  have h2 : (0:ℝ) < 2 - γ := by linarith [hγ.2]
  have hden : (0:ℝ) < 5 * (1 - γ) * (2 - γ) := by
    nlinarith [mul_pos h1 h2]
  exact affineInterceptBCF_mem_gainBall
    (div_nonneg (by linarith [hγ.1]) hden.le)
    (fgcSlopeT_nonneg hγ)
    (le_of_eq (fgcBT_lockin_identity hγ))

/-- **The fgc Target parametrized pinned fixed point (`β_T`-channel)**:
for every `γ` in the window, the joint Target Bellman operator (Sender
input = the shipped `β_S = 1/2` pin `fgcVSstar`) fixes
`V_T*(x;γ) = b_T(γ) + c_T(γ)·x` exactly. Reproduces the shipped
microfounded pin `(52/11, 80/11)` at `γ = 9/10`. -/
theorem fgcBT_VT_star_fixed (γ : ℝ) (hγ : γ ∈ Set.Ico (14/17:ℝ) 1)
    (y : ↥(Sanctions.S : Set ℝ)) :
    (fgcParamsBT γ hγ).jointTarget_BCF_on_S (fgcVTstarT γ) fgcVSstar
        (fgcGen_DAU_on_carrier mem_half_Ico (fgcBT_βT_mem hγ) mem_half_Ioo
          (by norm_num : (0:ℝ) ≤ 4/3) (mem_fgcCarrierS_num fgcVSstar_mem)).toOnI y
      = fgcVTstarT γ y := by
  refine Eq.trans (fgcGen_jointTarget_image mem_half_Ico (fgcBT_βT_mem hγ)
    mem_half_Ioo (fgcSlopeT_nonneg hγ) (fgcBT_chord hγ) (fgcVTstarT_mem hγ)
    (by norm_num : (0:ℝ) ≤ 4/3) (mem_fgcCarrierS_num fgcVSstar_mem)
    (fgcGen_DAU_on_carrier mem_half_Ico (fgcBT_βT_mem hγ) mem_half_Ioo
      (by norm_num : (0:ℝ) ≤ 4/3) (mem_fgcCarrierS_num fgcVSstar_mem)) y) ?_
  rw [show ((1:ℝ) - 1/2) * y.val + 1/2 = (y.val + 1)/2 by ring]
  have h1 : (1:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 1 - γ)
  have h2 : (2:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 2 - γ)
  simp only [fgcVTstarT, affineInterceptBCF_apply,
    clipS'_val_of_mem (mem_half_shift y)]
  unfold fgcInterceptT fgcSlopeT
  field_simp
  ring

/-- The fgc Target family reproduces the shipped `γ = 9/10` pin
`V_T* = 52/11 + (80/11)x` (Rule 5). -/
theorem fgcVTstarT_910 : fgcVTstarT (9/10) = fgcVTstar := by
  unfold fgcVTstarT fgcVTstar fgcInterceptT fgcSlopeT
  norm_num

/-- **The fgc pinned Target family solves the Target corner Bellman equation
pointwise.** Repackages `fgcBT_VT_star_fixed` through the closed-form joint
Target image `fgcGen_jointTarget_image`: at every state,
`V_T*(y;γ) = U_T(y, 0, 1) + γ·V_T*(F(y, 1);γ)` in the family economy — the Sender
at full sanction, the Target at full defiance (`a = 0`), with the corner flow
`4y − 14/5` and successor `(y+1)/2` (BH6.3, 2026-10-07). -/
theorem fgcBT_VT_star_cornerBellman (γ : ℝ) (hγ : γ ∈ Set.Ico (14 / 17 : ℝ) 1)
    (y : ↥(Sanctions.S : Set ℝ)) :
    fgcVTstarT γ y = (fgcParamsBT γ hγ).U_T y.val 0 1
      + γ * fgcVTstarT γ (Sanctions.clipS' ((fgcParamsBT γ hγ).F y.val 1)) := by
  have hpin : fgcVTstarT γ y = 4 * y.val - 14/5
      + γ * fgcVTstarT γ (Sanctions.clipS' ((1 - 1/2) * y.val + 1/2)) :=
    (fgcBT_VT_star_fixed γ hγ y).symm.trans
      (fgcGen_jointTarget_image mem_half_Ico (fgcBT_βT_mem hγ)
        mem_half_Ioo (fgcSlopeT_nonneg hγ) (fgcBT_chord hγ) (fgcVTstarT_mem hγ)
        (by norm_num : (0:ℝ) ≤ 4/3) (mem_fgcCarrierS_num fgcVSstar_mem)
        (fgcGen_DAU_on_carrier mem_half_Ico (fgcBT_βT_mem hγ) mem_half_Ioo
          (by norm_num : (0:ℝ) ≤ 4/3) (mem_fgcCarrierS_num fgcVSstar_mem)) y)
  have hU : (fgcParamsBT γ hγ).U_T y.val 0 1 = 4 * y.val - 14/5 := by
    simp only [fgcParamsBT, fgcParamsGen_U_T]
    ring
  have hF : (fgcParamsBT γ hγ).F y.val 1 = (1 - 1/2) * y.val + 1/2 := by
    simp only [fgcParamsBT, fgcParamsGen_F]
    ring
  rw [hU, hF]
  exact hpin

/-- The fgc pinned Target family at the lock-in state is the pinned lock-in
value: `V_T*(1;γ) = b_T(γ) + c_T(γ) = (6/5)/(1−γ)`. -/
theorem fgcVTstarT_lockin {γ : ℝ} (hγ : γ ∈ Set.Ico (14 / 17 : ℝ) 1) :
    fgcVTstarT γ (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
      = fgcLockinT γ := by
  change fgcInterceptT γ + fgcSlopeT γ * 1 = fgcLockinT γ
  rw [mul_one]
  exact fgcBT_lockin_identity hγ

/-- fgc FULL Target lock-in response: `dV_T*(1)/dγ = (6/5)/(1−γ)²`;
`120` at `γ = 9/10`. -/
theorem fgcLockinT_hasDerivAt {γ : ℝ} (hγ : γ ∈ Set.Ico (14/17:ℝ) 1) :
    HasDerivAt fgcLockinT ((6/5) / (1 - γ)^2) γ := by
  have h1 : (1:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 1 - γ)
  have hden : HasDerivAt (fun t : ℝ => 1 - t) (-1) γ := by
    simpa using (hasDerivAt_id γ).const_sub 1
  have h := (hasDerivAt_const γ ((6:ℝ)/5)).fun_div hden h1
  convert h using 1
  ring

/-- fgc FULL Target lock-in response at the witness point:
`dV_T*(1)/dβ_T = 120` at `γ = 9/10`. -/
theorem fgcLockinT_hasDerivAt_910 : HasDerivAt fgcLockinT 120 (9/10:ℝ) := by
  have h := fgcLockinT_hasDerivAt (γ := 9/10) ⟨by norm_num, by norm_num⟩
  convert h using 1
  norm_num

/-- fgc Target resolvent identity: `dV_T*(1)/dγ = V_T*(1;γ)/(1−γ)`. -/
theorem fgcLockinT_resolvent {γ : ℝ} (hγ : γ ∈ Set.Ico (14/17:ℝ) 1) :
    HasDerivAt fgcLockinT (fgcLockinT γ / (1 - γ)) γ := by
  have h1 : (1:ℝ) - γ ≠ 0 := ne_of_gt (by linarith [hγ.2] : (0:ℝ) < 1 - γ)
  have h := fgcLockinT_hasDerivAt hγ
  rw [show fgcLockinT γ / (1 - γ) = (6/5) / (1 - γ)^2 by
    unfold fgcLockinT
    field_simp]
  exact h

/-- fgc DIRECT Target effect at the absorbing state: one joint Target
Bellman application with patience `γ` at the FROZEN old pin `fgcVTstar`
is `6/5 + 12γ` — direct lock-in response `12` per unit of patience.
(The frozen slope-`80/11` carrier keeps the defiance pin on the window:
`γ·(80/11)·δ = 40γ/11 ≥ 14/5` from `γ ≥ 14/17 > 77/100`.) -/
theorem fgcBT_direct_lockin_eval (γ : ℝ)
    (hγ : γ ∈ Set.Ico (14/17:ℝ) 1) :
    (fgcParamsBT γ hγ).jointTarget_BCF_on_S fgcVTstar fgcVSstar
        (fgcGen_DAU_on_carrier mem_half_Ico (fgcBT_βT_mem hγ) mem_half_Ioo
          (by norm_num : (0:ℝ) ≤ 4/3) (mem_fgcCarrierS_num fgcVSstar_mem)).toOnI
        (Sanctions.clipS' 1)
      = 6/5 + 12 * γ := by
  refine Eq.trans (fgcGen_jointTarget_image mem_half_Ico (fgcBT_βT_mem hγ)
    mem_half_Ioo (by norm_num : (0:ℝ) ≤ 80/11)
    (by linarith [hγ.1] : (14:ℝ)/5 ≤ γ * (80/11) * (1/2)) (mem_fgcCarrierT_num fgcVTstar_mem)
    (by norm_num : (0:ℝ) ≤ 4/3) (mem_fgcCarrierS_num fgcVSstar_mem)
    (fgcGen_DAU_on_carrier mem_half_Ico (fgcBT_βT_mem hγ) mem_half_Ioo
      (by norm_num : (0:ℝ) ≤ 4/3) (mem_fgcCarrierS_num fgcVSstar_mem)) (Sanctions.clipS' 1)) ?_
  rw [clipS'_val_of_mem (⟨by norm_num, le_refl 1⟩ :
    (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
  have hmem : ((1:ℝ) - 1/2) * 1 + 1/2 ∈ Set.Icc (0:ℝ) 1 := by
    constructor <;> norm_num
  simp only [fgcVTstar, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  ring

/-- **fgc Target split (machine-checked)**: `120 = 12 + 108` with
amplification `120 = 12/(1 − 9/10)` (factor 10); feedback `108`
strictly positive. -/
theorem fgcBT_lockin_split :
    (120:ℝ) = 12 + 108 ∧ (0:ℝ) < 108 ∧ (120:ℝ) = 12 / (1 - 9/10) := by
  norm_num

/-- fgc Target lock-in amplification identity
`(1−γ₁)·ΔV_T*(1) = Δγ·V_T*(1;γ₂)`.

Since BH6.3 (2026-10-07) an instance of the general-`F`
`targetValue_lockin_amplification_of_bellman` at the pinned fgc Target fixed
points (`fgcBT_VT_star_cornerBellman`, `fgcVTstarT_lockin`); it used to be a
`field_simp` computation on the closed form `fgcLockinT`. Statement unchanged. -/
theorem fgcBT_lockin_amplification (γ₁ γ₂ : ℝ)
    (hγ₁ : γ₁ ∈ Set.Ico (14/17:ℝ) 1) (hγ₂ : γ₂ ∈ Set.Ico (14/17:ℝ) 1) :
    (1 - γ₁) * (fgcLockinT γ₂ - fgcLockinT γ₁)
      = (γ₂ - γ₁) * fgcLockinT γ₂ := by
  have h := (fgcParamsBT γ₁ hγ₁).targetValue_lockin_amplification_of_bellman 0
    (fgcBT_VT_star_cornerBellman γ₁ hγ₁) (fgcBT_VT_star_cornerBellman γ₂ hγ₂)
  rwa [fgcVTstarT_lockin hγ₁, fgcVTstarT_lockin hγ₂] at h

/-- fgc Target Rule 16(a) ordered endpoints: at `γ = 9/10 < 23/25`,
lock-in values `12 < 15`. -/
theorem fgcBT_rule16a :
    (9/10:ℝ) < 23/25
      ∧ (9/10:ℝ) ∈ Set.Ico (14/17:ℝ) 1
      ∧ (23/25:ℝ) ∈ Set.Ico (14/17:ℝ) 1
      ∧ fgcLockinT (9/10) = 12 ∧ fgcLockinT (23/25) = 15
      ∧ fgcLockinT (9/10) < fgcLockinT (23/25) := by
  unfold fgcLockinT
  norm_num [Set.mem_Ico]

/-! ## 10. The fgc `δ`-family on `[7/27, 1)`: BOTH lock-in values
`δ`-invariant

Sender: `c(δ) = 2/(1+δ)`, `b(δ) = 3 + 2δ/(1+δ)`, `V_S*(1;δ) ≡ 5`.
Target: `c_T(δ) = 40/(1+9δ)`, `b_T(δ) = −28 + 360δ/(1+9δ)`,
`V_T*(1;δ) ≡ 12`. The window's binding constraint is the Target-side
chord/loss-margin `36δ/(1+9δ) ≥ 14/5` at `δ ≥ 7/27` (which is ALSO
exactly where `b_T(δ) ≥ 0`, so the carrier membership is tight). -/

/-- The fgc `δ` window sits inside the parameter space `(0,1)`. -/
theorem fgcD_δ_mem {dd : ℝ} (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    dd ∈ Set.Ioo (0:ℝ) 1 :=
  ⟨by linarith [hdd.1], hdd.2⟩

/-- **The fgc `δ`-family** on the Target chord/loss-margin window. -/
def fgcParamsD (dd : ℝ) (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    AbstractGame.Params :=
  fgcParamsGen (1/2) (9/10) dd mem_half_Ico mem_910_Ico (fgcD_δ_mem hdd)

/-- fgc pinned Sender slope in `δ`: `c(δ) = 2/(1+δ)`. -/
def fgcSlopeSD (dd : ℝ) : ℝ := 2 / (1 + dd)

/-- fgc pinned Sender intercept in `δ`: `b(δ) = 3 + 2δ/(1+δ)`. -/
def fgcInterceptSD (dd : ℝ) : ℝ := 3 + 2 * dd / (1 + dd)

/-- The `δ`-re-pinned fgc Sender carrier (radius `5`, the invariant
lock-in value; tight). -/
def fgcCarrierSD (dd : ℝ) : Set Val :=
  valLipGainBall 5 (fgcSlopeSD dd) (fgcSlopeSD dd) 0

/-- The fgc pinned Sender value family in `δ`. -/
def fgcVSstarD (dd : ℝ) : Val :=
  affineInterceptBCF (fgcInterceptSD dd) (fgcSlopeSD dd)

theorem fgcSlopeSD_nonneg {dd : ℝ} (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    0 ≤ fgcSlopeSD dd :=
  div_nonneg (by norm_num) (by linarith [hdd.1])

/-- **fgc Sender δ-invariance of the lock-in value**:
`b(δ) + c(δ) = 5` for every window `δ` — `dV_S*(1)/dδ = 0` exactly (the
capitalized `δ`-free corner flow `(5/2)/(1/2)`). Cross-reference (BH6.3): the
general-`F` `senderValue_lockin_capitalised_of_bellman` predicts this for every
transition; the lemma is kept as the pinned-fixed-point coefficient algebra. -/
theorem fgcD_VS_lockin_invariant {dd : ℝ}
    (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    fgcInterceptSD dd + fgcSlopeSD dd = 5 := by
  have h1 : (1:ℝ) + dd ≠ 0 := ne_of_gt (by linarith [hdd.1] : (0:ℝ) < 1 + dd)
  unfold fgcInterceptSD fgcSlopeSD
  field_simp
  ring

/-- The fgc `δ`-family Sender value lives in its carrier. -/
theorem fgcVSstarD_mem {dd : ℝ} (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    fgcVSstarD dd ∈ fgcCarrierSD dd := by
  have h1 : (0:ℝ) < 1 + dd := by linarith [hdd.1]
  have hb : 0 ≤ fgcInterceptSD dd := by
    have : (0:ℝ) ≤ 2 * dd / (1 + dd) :=
      div_nonneg (by linarith [hdd.1]) h1.le
    unfold fgcInterceptSD
    linarith
  exact affineInterceptBCF_mem_gainBall hb (fgcSlopeSD_nonneg hdd)
    (le_of_eq (fgcD_VS_lockin_invariant hdd))

/-- **The fgc Sender pinned fixed point (`δ`-channel)**: for every `δ`
in the window the Sender Bellman operator fixes
`V_S*(x;δ) = 3 + 2δ/(1+δ) + 2/(1+δ)·x` exactly (pin `(11/3, 4/3)` at
`δ = 1/2`). -/
theorem fgcD_VS_star_fixed (dd : ℝ) (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    (fgcParamsD dd hdd).bellmanS_BCF (fun _ => 0) continuous_const
        (fgcVSstarD dd)
      = fgcVSstarD dd := by
  ext y
  refine Eq.trans (fgcGen_bellmanS_image mem_half_Ico mem_910_Ico
    (fgcD_δ_mem hdd) (fgcSlopeSD_nonneg hdd) (fgcVSstarD_mem hdd) y) ?_
  have h1 : (1:ℝ) + dd ≠ 0 := ne_of_gt (by linarith [hdd.1] : (0:ℝ) < 1 + dd)
  have hmem : (1 - dd) * y.val + dd ∈ Set.Icc (0:ℝ) 1 :=
    mem_affine_corner (fgcD_δ_mem hdd) y.property
  simp only [fgcVSstarD, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  unfold fgcInterceptSD fgcSlopeSD
  field_simp
  ring

/-- The fgc `δ`-family reproduces the shipped Sender pin at
`δ = 1/2` (Rule 5). -/
theorem fgcVSstarD_half : fgcVSstarD (1/2) = fgcVSstar := by
  unfold fgcVSstarD fgcVSstar fgcInterceptSD fgcSlopeSD
  norm_num

/-- Game-tied form: the fgc Sender pinned value at the absorbing state
is `5` for every window `δ`. -/
theorem fgcVSstarD_lockin_eval {dd : ℝ} (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    fgcVSstarD dd (Sanctions.clipS' 1) = 5 := by
  simp only [fgcVSstarD, affineInterceptBCF_apply,
    clipS'_val_of_mem (⟨by norm_num, le_refl 1⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
  rw [mul_one]
  exact fgcD_VS_lockin_invariant hdd

/-- fgc Sender δ-invariance at the derivative level: the lock-in map
`δ ↦ b(δ) + c(δ)` has derivative exactly zero on the window. -/
theorem fgcD_VS_lockin_hasDerivAt_zero {dd : ℝ}
    (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    HasDerivAt (fun t : ℝ => fgcInterceptSD t + fgcSlopeSD t) 0 dd := by
  have h1 : (1:ℝ) + dd ≠ 0 := ne_of_gt (by linarith [hdd.1] : (0:ℝ) < 1 + dd)
  have hden : HasDerivAt (fun t : ℝ => 1 + t) 1 dd := by
    simpa using (hasDerivAt_id dd).const_add 1
  have hb : HasDerivAt fgcInterceptSD (2 / (1 + dd)^2) dd := by
    have hnum : HasDerivAt (fun t : ℝ => 2 * t) 2 dd := hasDerivAt_const_mul 2
    have h := (hnum.fun_div hden h1).const_add (3:ℝ)
    convert h using 1
    ring
  have hc : HasDerivAt fgcSlopeSD (-(2 / (1 + dd)^2)) dd := by
    have h := (hasDerivAt_const dd (2:ℝ)).fun_div hden h1
    convert h using 1
    ring
  have h := hb.add hc
  convert h using 1
  ring

/-! ### fgc Target `δ`-channel -/

/-- fgc pinned Target slope in `δ`: `c_T(δ) = 40/(1+9δ)`. -/
def fgcSlopeTD (dd : ℝ) : ℝ := 40 / (1 + 9 * dd)

/-- fgc pinned Target intercept in `δ`: `b_T(δ) = −28 + 360δ/(1+9δ)`. -/
def fgcInterceptTD (dd : ℝ) : ℝ := -28 + 360 * dd / (1 + 9 * dd)

/-- The `δ`-re-pinned fgc Target carrier (radius `12`, the invariant
lock-in value; tight). -/
def fgcCarrierTD (dd : ℝ) : Set Val :=
  valLipGainBall 12 (fgcSlopeTD dd) (fgcSlopeTD dd) 0

/-- The fgc pinned Target value family in `δ`. -/
def fgcVTstarD (dd : ℝ) : Val :=
  affineInterceptBCF (fgcInterceptTD dd) (fgcSlopeTD dd)

theorem fgcSlopeTD_nonneg {dd : ℝ} (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    0 ≤ fgcSlopeTD dd :=
  div_nonneg (by norm_num) (by linarith [hdd.1])

/-- **The fgc `δ`-window constraint (Target chord = loss margin)**:
`14/5 ≤ β_T·c_T(δ)·δ = 36δ/(1+9δ)` exactly at `δ ≥ 7/27`. -/
theorem fgcD_chord {dd : ℝ} (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    14/5 ≤ 9/10 * fgcSlopeTD dd * dd := by
  have h1 : (0:ℝ) < 1 + 9 * dd := by linarith [hdd.1]
  have h1' : (1:ℝ) + 9 * dd ≠ 0 := ne_of_gt h1
  have key : 9/10 * fgcSlopeTD dd * dd - 14/5
      = (54 * dd - 14) / (5 * (1 + 9 * dd)) := by
    unfold fgcSlopeTD
    field_simp
    ring
  have hnn : (0:ℝ) ≤ (54 * dd - 14) / (5 * (1 + 9 * dd)) :=
    div_nonneg (by linarith [hdd.1]) (by linarith)
  linarith [key, hnn]

/-- **fgc Target δ-invariance of the lock-in value**:
`b_T(δ) + c_T(δ) = 12` for every window `δ` — `dV_T*(1)/dδ = 0` exactly
(the capitalized `δ`-free corner flow `(6/5)/(1/10)`). Cross-reference
(BH6.3): the general-`F` `targetValue_lockin_capitalised_of_bellman` predicts
`V_T*(1) = U_T(1,0,1)/(1−β_T)` for every transition; the lemma is kept as the
pinned-fixed-point coefficient algebra. -/
theorem fgcD_VT_lockin_invariant {dd : ℝ}
    (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    fgcInterceptTD dd + fgcSlopeTD dd = 12 := by
  have h1 : (0:ℝ) < 1 + 9 * dd := by linarith [hdd.1]
  have key : 360 * dd / (1 + 9 * dd) + 40 / (1 + 9 * dd) = 40 := by
    rw [← add_div, div_eq_iff (ne_of_gt h1)]
    ring
  unfold fgcInterceptTD fgcSlopeTD
  linarith [key]

/-- The fgc `δ`-family Target value lives in its carrier — the
intercept is nonnegative EXACTLY on the window (`108δ − 28 ≥ 0` at
`δ ≥ 7/27`, zero at the closed endpoint). -/
theorem fgcVTstarD_mem {dd : ℝ} (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    fgcVTstarD dd ∈ fgcCarrierTD dd := by
  have h1 : (0:ℝ) < 1 + 9 * dd := by linarith [hdd.1]
  have hb : 0 ≤ fgcInterceptTD dd := by
    have h28 : (28:ℝ) ≤ 360 * dd / (1 + 9 * dd) := by
      rw [le_div_iff₀ h1]
      linarith [hdd.1]
    unfold fgcInterceptTD
    linarith
  exact affineInterceptBCF_mem_gainBall hb (fgcSlopeTD_nonneg hdd)
    (le_of_eq (fgcD_VT_lockin_invariant hdd))

/-- **The fgc Target pinned fixed point (`δ`-channel)**: for every `δ`
in the window the joint Target Bellman operator (Sender input = the
`δ`-re-pinned `fgcVSstarD δ`) fixes
`V_T*(x;δ) = −28 + 360δ/(1+9δ) + 40/(1+9δ)·x` exactly (pin
`(52/11, 80/11)` at `δ = 1/2`). -/
theorem fgcD_VT_star_fixed (dd : ℝ) (hdd : dd ∈ Set.Ico (7/27:ℝ) 1)
    (y : ↥(Sanctions.S : Set ℝ)) :
    (fgcParamsD dd hdd).jointTarget_BCF_on_S (fgcVTstarD dd) (fgcVSstarD dd)
        (fgcGen_DAU_on_carrier mem_half_Ico mem_910_Ico (fgcD_δ_mem hdd)
          (fgcSlopeSD_nonneg hdd) (fgcVSstarD_mem hdd)).toOnI y
      = fgcVTstarD dd y := by
  refine Eq.trans (fgcGen_jointTarget_image mem_half_Ico mem_910_Ico
    (fgcD_δ_mem hdd) (fgcSlopeTD_nonneg hdd) (fgcD_chord hdd)
    (fgcVTstarD_mem hdd) (fgcSlopeSD_nonneg hdd) (fgcVSstarD_mem hdd)
    (fgcGen_DAU_on_carrier mem_half_Ico mem_910_Ico (fgcD_δ_mem hdd)
      (fgcSlopeSD_nonneg hdd) (fgcVSstarD_mem hdd)) y) ?_
  have h1 : (1:ℝ) + 9 * dd ≠ 0 :=
    ne_of_gt (by linarith [hdd.1] : (0:ℝ) < 1 + 9 * dd)
  have hmem : (1 - dd) * y.val + dd ∈ Set.Icc (0:ℝ) 1 :=
    mem_affine_corner (fgcD_δ_mem hdd) y.property
  simp only [fgcVTstarD, affineInterceptBCF_apply, clipS'_val_of_mem hmem]
  unfold fgcInterceptTD fgcSlopeTD
  field_simp
  ring

/-- The fgc Target `δ`-family reproduces the shipped pin at `δ = 1/2`
(Rule 5). -/
theorem fgcVTstarD_half : fgcVTstarD (1/2) = fgcVTstar := by
  unfold fgcVTstarD fgcVTstar fgcInterceptTD fgcSlopeTD
  norm_num

/-- Game-tied form: the fgc Target pinned value at the absorbing state
is `12` for every window `δ`. -/
theorem fgcVTstarD_lockin_eval {dd : ℝ} (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    fgcVTstarD dd (Sanctions.clipS' 1) = 12 := by
  simp only [fgcVTstarD, affineInterceptBCF_apply,
    clipS'_val_of_mem (⟨by norm_num, le_refl 1⟩ : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)]
  rw [mul_one]
  exact fgcD_VT_lockin_invariant hdd

/-- fgc Target δ-invariance at the derivative level: the lock-in map
`δ ↦ b_T(δ) + c_T(δ)` has derivative exactly zero on the window. -/
theorem fgcD_VT_lockin_hasDerivAt_zero {dd : ℝ}
    (hdd : dd ∈ Set.Ico (7/27:ℝ) 1) :
    HasDerivAt (fun t : ℝ => fgcInterceptTD t + fgcSlopeTD t) 0 dd := by
  have h1 : (1:ℝ) + 9 * dd ≠ 0 :=
    ne_of_gt (by linarith [hdd.1] : (0:ℝ) < 1 + 9 * dd)
  have hden : HasDerivAt (fun t : ℝ => 1 + 9 * t) 9 dd := by
    simpa using (hasDerivAt_const_mul (9:ℝ) (x := dd)).const_add 1
  have hb : HasDerivAt fgcInterceptTD (360 / (1 + 9 * dd)^2) dd := by
    have hnum : HasDerivAt (fun t : ℝ => 360 * t) 360 dd :=
      hasDerivAt_const_mul 360
    have h := ((hnum.fun_div hden h1).const_add (-28:ℝ))
    convert h using 1
    field_simp
    ring
  have hc : HasDerivAt fgcSlopeTD (-(360 / (1 + 9 * dd)^2)) dd := by
    have h := (hasDerivAt_const dd (40:ℝ)).fun_div hden h1
    convert h using 1
    field_simp
    ring
  have h := hb.add hc
  convert h using 1
  ring

/-! ## 11. Axiom hygiene (Rule 10) -/

end -- noncomputable section

#print axioms eeCertB_VS_star_fixed
#print axioms eeCertB_σ_dyn_top_eq_one
#print axioms eeCertB_hS_margin
#print axioms eeSlopeB_hasDerivAt_half
#print axioms eeInterceptB_hasDerivAt_half
#print axioms eeLockinB_hasDerivAt_half
#print axioms eeLockinB_resolvent
#print axioms eeCertB_direct_lockin_eval
#print axioms eeCertB_slope_split
#print axioms eeCertB_intercept_split
#print axioms eeCertB_lockin_split
#print axioms eeCertB_feedback_decomposition
#print axioms eeCertB_feedback_lockin_pos
#print axioms eeCertB_lockin_amplification
#print axioms eeCertB_rule16a
#print axioms eeCertD_VS_star_fixed
#print axioms eeCertD_lockin_value_invariant
#print axioms eeCertD_lockin_hasDerivAt_zero
#print axioms eeCertD_direct_lockin_eval
#print axioms eeCertB_VT_star_fixed
#print axioms eeCertB_VT_star_βS_invariant
#print axioms eeCertBT_VT_star_fixed
#print axioms eeLockinT_hasDerivAt_910
#print axioms eeCertBT_direct_lockin_eval
#print axioms eeCertBT_lockin_split
#print axioms fgcB_VS_star_fixed
#print axioms fgcB_splits
#print axioms fgcB_feedback_decomposition
#print axioms fgcLockinB_hasDerivAt_half
#print axioms fgcBT_VT_star_fixed
#print axioms fgcLockinT_hasDerivAt_910
#print axioms fgcBT_direct_lockin_eval
#print axioms fgcBT_lockin_split
#print axioms fgcD_VS_star_fixed
#print axioms fgcD_VS_lockin_invariant
#print axioms fgcD_VS_lockin_hasDerivAt_zero
#print axioms fgcD_VT_star_fixed
#print axioms fgcD_VT_lockin_invariant
#print axioms fgcD_VT_lockin_hasDerivAt_zero
#print axioms AbstractGame.Params.cornerValue_lockin_amplification_of_bellman
#print axioms AbstractGame.Params.cornerValue_lockin_capitalised_of_bellman
#print axioms AbstractGame.Params.cornerValue_lockin_strict_iff_of_bellman
#print axioms AbstractGame.Params.targetValue_lockin_amplification_of_bellman
#print axioms AbstractGame.Params.targetValue_lockin_capitalised_of_bellman
#print axioms AbstractGame.Params.targetValue_lockin_strict_iff_of_bellman
#print axioms eeCertBT_lockin_amplification
#print axioms fgcBT_lockin_amplification

end Examples

end Sanctions
