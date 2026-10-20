/-
Sanctions/Examples/MechanismWitnessShocked.lean

**Constructed purified existence at the mechanism-active witness P3.**

At `mechanismWitnessParams` (P3), deterministic best-response iteration is order-reversing
and exhibits a period-two cycle; that refutes the proposed iterative construction, not
existence of a deterministic equilibrium. This file constructs the **purified** (atomless box-shock) equilibrium
of P3 via the project's shocked-purification engine — a genuine Banach fixed point on the
smeared operator (Rule-15: constructed, not consumed), where the smear upgrades the
Hölder-½ leader response to Lipschitz so the operator contracts.

The purified P3 parameter point is `mwShocked hh = movAvgShockedParams mechanismWitnessParams hh`
(a uniform box noise of half-width `h`). The free-leader theorem
`mechanismWitnessParams_purified_existence` specializes the *numeric parameters* at the P3
coefficients (`c_T = 2`, the `U_S` action-Lipschitz constant `L_Ua = 1` from
`∂U_S/∂a = 1 − s/2`, and the contraction margin
`β_S + L_Ua·(2·L_lead/c_T) < 1`, i.e. `1/2 + L_lead < 1`).  It is a
compatibility corollary of the canonical-leader theorems, and the persistence payoff
`mechanismWitnessParams_purified_persistence` uses the canonical leader at any modulus
`c_T > 0`.  The stronger headline
`mechanismWitnessParams_purified_existence_canonical_leader` constructs the leader by
compact argmax and derives its continuity, feasibility, and pointwise optimality.  Its
remaining analytic surface is exactly three hypotheses: joint continuity of the shocked
Sender selector (`hσc`), strong concavity `sc` of the real composite Target objective,
and the Stackelberg-coupling regularity `h_obj_diff`.  The value `c_T = 2` is not
a discharge of `sc`: the exact theorem
`mwStaticLeaderComposite_not_strongConcave_two` below shows that even the
static composite through the clipped P3 response fails `2`-strong concavity.
The last condition is the coupling condition
that the feedback-Stackelberg literature assumes rather than derives — Montrucchio 1987 Thm 3.1 (the exact condition:
Lipschitz argmax `L/α` from strong concavity + Lipschitz objective-derivative),
Hinderer 2005 Thm 4.2(i′), Curtat 1996 Thm 4.5, He-Liu-Chen 2025 Lemma 4.1,
Li et al. 2024 Thm 4.3.

This **upgrades** the status quo: the equilibrium is now *constructed* via purification
(Banach on the smeared operator), conditional only on the standard leader regularity —
NOT on the row-contraction Schur margins that provably FAIL at P3. The deterministic P3
is the `h → 0` (zero-noise) limit; this is purified (shocked-game) existence, never
deterministic existence.

**Why `h_obj_diff` stays named (Level-3 derivation does not close — precise obstruction).**
Deriving `h_obj_diff` reduces to showing `a ↦ J(V,a) − J(W,a)` is `(L_lead·dist V W)`-Lipschitz,
which needs `∂_a[σ_dyn_top(smear V) − σ_dyn_top(smear W)] ∝ dist(V,W)`. At P3 the *single-V* part
derives cleanly (`∂²U_S/∂s∂a = −1/2` is constant, so by Montrucchio 1987 Thm 3.1 the response is
Lipschitz in `a`; the smear continuation has no `a`-dependence). But the mixed `(a,V)` bound runs
through `∂²Φ/∂s²`, whose `V`-difference requires the **second derivative of the smeared
continuation** — and the moving-average smear of a bounded-continuous value is only **C¹, not C²**
(`d/dz = (V(z+h) − V(z−h))/2h` is continuous, but `d²/dz²` needs `V ∈ C¹`). The IFT/envelope route
needs a derivative that does not exist. This is the concrete form of Hinderer 2005's `w = s + a²`
obstruction (purification regularises the *state*, never the *action*), and is exactly why the
feedback-Stackelberg literature *assumes* this regularity.  At P3 the attempted C²/kernel-width
discharge is also quantitatively impossible within the required contraction window.  Thus
`h_obj_diff` remains one member of the explicit three-condition analytic package; it is not
the whole remaining package.
-/

import Sanctions.Theory.Shocked.ShockedLeaderLipschitz
import Sanctions.Theory.Shocked.ShockedDominance
import Sanctions.Theory.Shocked.MovingAverageShock
import Sanctions.Theory.Equilibrium.BasinCornerExistence
import Sanctions.Examples.EatonEngersWitness
import Sanctions.Examples.MechanismWitness

namespace Sanctions
namespace Examples

open Set Filter
open AbstractGame
open scoped NNReal Topology
open BoundedContinuousFunction

/-- **The purified P3 parameter point**: the atomless box-shock (moving-average,
half-width `h`) realisation of `mechanismWitnessParams` as a `ShockedParams`. -/
noncomputable def mwShocked {h : ℝ} (hh : 0 < h) : AbstractGame.ShockedParams :=
  AbstractGame.movAvgShockedParams mechanismWitnessParams hh

@[simp] theorem mwShocked_toParams {h : ℝ} (hh : 0 < h) :
    (mwShocked hh).toParams = mechanismWitnessParams := rfl

/-- **The primitive Target curvature does not transfer through the clipped
Sender response at any nonnegative strong-concavity modulus.**  The exact
three-point violation straddles the lower clip kink at
`(x,a) = (5/12, 37/40)`, using endpoints `9/10` and `19/20`.  The middle
composite payoff lies strictly below the chord, so the composite is not even
concave; adding a nonnegative strong-concavity correction only strengthens the
violated inequality.

Consequently the `sc` hypothesis for the real Stackelberg objective cannot
be discharged merely by citing `∂²U_T/∂a² = -2`; the curvature of the
composed Sender response and continuation is load-bearing. -/
theorem mwStaticLeaderComposite_not_strongConcave_of_nonneg
    {c_T : ℝ} (hcT : 0 ≤ c_T) :
    ¬ StrongConcaveOn Sanctions.I c_T
      (fun a => mwU_T (5 / 12) a (mwσ (5 / 12) a)) := by
  intro hsc
  unfold StrongConcaveOn UniformConcaveOn at hsc
  have h := hsc.2
    (show (9 / 10 : ℝ) ∈ Sanctions.I by constructor <;> norm_num)
    (show (19 / 20 : ℝ) ∈ Sanctions.I by constructor <;> norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  norm_num [mwU_T, mwσ, Sanctions.I] at h
  nlinarith

/-- The formerly headline-facing modulus-`2` obstruction is the direct
specialization of the stronger nonconcavity result. -/
theorem mwStaticLeaderComposite_not_strongConcave_two :
    ¬ StrongConcaveOn Sanctions.I 2
      (fun a => mwU_T (5 / 12) a (mwσ (5 / 12) a)) :=
  mwStaticLeaderComposite_not_strongConcave_of_nonneg (by norm_num)

/-- **The full-interval strong-rally route cannot discharge P3 monotonicity
on a basin containing `x = 1/2`.**  For every feasible leader action, the
Sender's stage chord from `s = 0` to `s = 1` at `x = 1/2` equals
`-1/40 - a/2 < 0`.  Hence no positive lower-slope constant can hold on the
whole sanction interval there.  This does not refute monotonicity by every
possible route; it proves that the existing strict-increase/strong-rally gate
cannot supply P3's `hDynReg` on `[1/2,1]`. -/
theorem mwSenderStage_no_positive_lowerSlope_at_half
    {a m : ℝ} (ha : a ∈ Sanctions.I) (hm : 0 < m) :
    ¬ AbstractGame.Params.LowerSlopeOn
      (fun s => mwU_S (1 / 2) a s) Sanctions.I m := by
  intro hsl
  have h := hsl 0 (by constructor <;> norm_num) 1
    (by constructor <;> norm_num) (by norm_num)
  simp only [mwU_S] at h
  nlinarith [ha.1]

/-! ## Physical-state Sender uniqueness and selector continuity

The shocked existence wrapper below historically asks for a selector continuous
on all of `ℝ × ℝ`.  For a clipped interior economy that is stronger than the
Bellman problem needs: outside `S = [0,1]`, the clip can create a convex kink and
destroy uniqueness.  The natural restricted-carrier fact is state-local.

The following chord predicate caps the upward curvature of the *smeared*
continuation on the physical state space.  At P3, `F` has sanction slope `1/5`
and `β_S = 1/2`; hence a semiconcavity constant `c < 60` leaves the Sender
objective strictly concave:

`3/5 - (1/2)(c/2)(1/5)^2 = 3/5 - c/100 > 0`.

Thus the dynamic Sender argmax is unique at every physical `(x,a)`, and the
state-local Berge theorem makes the greatest selector jointly continuous on
`↥S × ℝ`.  This genuinely discharges the physical-state `hσc` obligation on
the restricted carrier; invariance of such a carrier under the slaved shocked
operator is a separate requirement and is not asserted here. -/

/-- Chord-form `c`-semiconcavity of P3's smeared Sender continuation on
the physical state space. -/
def mwSmearedSemiconcaveOn {h : ℝ} (hh : 0 < h) (V : SBCF) (c : ℝ) : Prop :=
  ∀ (y₁ y₂ m : ↥(Sanctions.S : Set ℝ)) (t : ℝ), 0 ≤ t → t ≤ 1 →
    m.val = t * y₁.val + (1 - t) * y₂.val →
    t * (mwShocked hh).smear V y₁ + (1 - t) * (mwShocked hh).smear V y₂
        - (mwShocked hh).smear V m
      ≤ c / 2 * (t * (1 - t) * (y₁.val - y₂.val) ^ 2)

/-- **The full-width P3 smear has zero semiconcavity defect.**
At half-width `1`, every moving-average continuation is affine on the physical
state interval, regardless of the curvature of the unsmoothed bounded-continuous
value. Thus the restricted-carrier hypothesis is automatic with `c = 0`. -/
theorem mwSmearedSemiconcaveOn_one (V : SBCF) :
    mwSmearedSemiconcaveOn one_pos V 0 := by
  intro y₁ y₂ m t _ht _ht1 hm
  change t * Sanctions.movAvgBCF one_pos V y₁ +
      (1 - t) * Sanctions.movAvgBCF one_pos V y₂ -
        Sanctions.movAvgBCF one_pos V m ≤
      0 / 2 * (t * (1 - t) * (y₁.val - y₂.val) ^ 2)
  rw [Sanctions.movAvgBCF_one_affine_chord V y₁ y₂ m t hm]
  norm_num

/-- **P3 Sender argmax uniqueness on a smeared-semiconcave carrier.**
Any curvature cap `c < 60` is sufficient; the compliance action enters the
Sender objective only linearly in the sanction, so the result is uniform in
the unrestricted real action `a`. -/
theorem mechanismWitnessParams_dynamicArgmaxUnique_of_smearedSemiconcave
    {h : ℝ} (hh : 0 < h) {V : SBCF} {c : ℝ} (hc : c < 60)
    (hV : mwSmearedSemiconcaveOn hh V c) :
    mechanismWitnessParams.DynamicArgmaxUnique ((mwShocked hh).smear V) := by
  apply mechanismWitnessParams.dynamicArgmaxUnique_of_strictConcaveOn
  intro x hx a
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s₁ hs₁ s₂ hs₂ hne p q hp hq hpq
  have hq_eq : q = 1 - p := by linarith
  subst hq_eq
  have hz₁ : mechanismWitnessParams.F x s₁ ∈ Set.Icc (0 : ℝ) 1 :=
    mechanismWitnessParams.F_mem x s₁ hx hs₁
  have hz₂ : mechanismWitnessParams.F x s₂ ∈ Set.Icc (0 : ℝ) 1 :=
    mechanismWitnessParams.F_mem x s₂ hx hs₂
  have hsm : p * s₁ + (1 - p) * s₂ ∈ Sanctions.I :=
    ⟨by nlinarith [hs₁.1, hs₂.1, hp.le, hq.le],
     by nlinarith [hs₁.2, hs₂.2, hp.le, hq.le]⟩
  have hzm : mechanismWitnessParams.F x (p * s₁ + (1 - p) * s₂)
      ∈ Set.Icc (0 : ℝ) 1 :=
    mechanismWitnessParams.F_mem x _ hx hsm
  have hcombo :
      (Sanctions.clipS'
        (mechanismWitnessParams.F x (p * s₁ + (1 - p) * s₂))).val
        = p * (Sanctions.clipS' (mechanismWitnessParams.F x s₁)).val
          + (1 - p) * (Sanctions.clipS' (mechanismWitnessParams.F x s₂)).val := by
    rw [Sanctions.clipS'_val_eq_of_mem hzm, Sanctions.clipS'_val_eq_of_mem hz₁,
      Sanctions.clipS'_val_eq_of_mem hz₂]
    simp only [mechanismWitnessParams_F, Sanctions.AbstractGame.affineF]
    ring
  have hV_sc := hV
    (Sanctions.clipS' (mechanismWitnessParams.F x s₁))
    (Sanctions.clipS' (mechanismWitnessParams.F x s₂))
    (Sanctions.clipS'
      (mechanismWitnessParams.F x (p * s₁ + (1 - p) * s₂)))
    p hp.le (by linarith) hcombo
  rw [Sanctions.clipS'_val_eq_of_mem hz₁,
    Sanctions.clipS'_val_eq_of_mem hz₂] at hV_sc
  have hFdiff : mechanismWitnessParams.F x s₁
      - mechanismWitnessParams.F x s₂ = (s₁ - s₂) / 5 := by
    simp only [mechanismWitnessParams_F, Sanctions.AbstractGame.affineF]
    ring
  rw [hFdiff] at hV_sc
  simp only [smul_eq_mul, mechanismWitnessParams_U_S, mwU_S,
    mechanismWitnessParams_β_S]
  have hsq : (0 : ℝ) < (s₁ - s₂) ^ 2 := by
    have hne0 : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  nlinarith [hV_sc, mul_pos (mul_pos hp hq) hsq]

/-- **Unconditional physical-state Sender uniqueness at the full-width P3 shock.**
The half-width-`1` smear is affine on `S`, so the primitive quadratic Sender
curvature makes the dynamic sanction maximizer unique for every bounded-continuous
continuation value. -/
theorem mechanismWitnessParams_dynamicArgmaxUnique_one (V : SBCF) :
    mechanismWitnessParams.DynamicArgmaxUnique ((mwShocked one_pos).smear V) :=
  mechanismWitnessParams_dynamicArgmaxUnique_of_smearedSemiconcave
    one_pos (by norm_num) (mwSmearedSemiconcaveOn_one V)

/-- **The physical-state `hσc` discharge at P3.**  Smeared
semiconcavity with any `c < 60` implies joint continuity of the greatest
shocked Sender selector on `↥S × ℝ`. -/
theorem mwSigmaDynTop_continuous_subtype_of_smearedSemiconcave
    {h : ℝ} (hh : 0 < h) {V : SBCF} {c : ℝ} (hc : c < 60)
    (hV : mwSmearedSemiconcaveOn hh V c) :
    Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      (mwShocked hh).toParams.σ_dyn_top
        ((mwShocked hh).smear V) xa.1.val xa.2) := by
  rw [mwShocked_toParams]
  exact mechanismWitnessParams.σ_dyn_top_continuous_subtype_of_unique_on
    ((mwShocked hh).smear V)
    (mechanismWitnessParams_dynamicArgmaxUnique_of_smearedSemiconcave hh hc hV)

/-- **Unconditional physical-state `hσc` at the full-width P3 shock.**
For every bounded-continuous Sender value, the greatest dynamic sanction selector
is jointly continuous in the physical state and the Target action. -/
theorem mwSigmaDynTop_continuous_subtype_one (V : SBCF) :
    Continuous (fun xa : ↥(Sanctions.S : Set ℝ) × ℝ =>
      (mwShocked one_pos).toParams.σ_dyn_top
        ((mwShocked one_pos).smear V) xa.1.val xa.2) :=
  mwSigmaDynTop_continuous_subtype_of_smearedSemiconcave
    one_pos (by norm_num) (mwSmearedSemiconcaveOn_one V)

/-! ## Canonical leader selector from the real shocked objective

The interior-existence theorem below historically accepted a leader map together
with three separate certificates: continuity, feasibility, and pointwise
optimality.  Those certificates are not primitive once the theorem's own
joint-continuity and strong-concavity hypotheses are available.  The following
Berge construction chooses the unique maximizer on the compact action interval,
proves continuity on the physical state space, and extends it continuously to
all real states by clamping.  Consequently the canonical wrapper below consumes
only the genuinely analytic remainder: `hσc`, `sc`, and `h_obj_diff` (plus the
coupling constant and its contraction margin).
-/

/-- The real Target objective used by the slaved shocked leader problem. -/
noncomputable def mwLeaderObjective {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (V : SBCF) (x a : ℝ) : ℝ :=
  (mwShocked hh).toParams.joint_T_top_integrand
    ((mwShocked hh).smear ((mwShocked hh).V_T_dyn_shock V (hσc V)))
    ((mwShocked hh).smear V) x a

/-- Joint `(x,a)` continuity of the real shocked leader objective. -/
theorem mwLeaderObjective_continuous {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (V : SBCF) :
    Continuous (fun xa : ℝ × ℝ => mwLeaderObjective hh hσc V xa.1 xa.2) := by
  unfold mwLeaderObjective AbstractGame.Params.joint_T_top_integrand
  let σc : Continuous (fun xa : ℝ × ℝ =>
      (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2) := hσc V
  apply Continuous.add
  · exact (mwShocked hh).toParams.U_T_continuous.comp
      (continuous_fst.prodMk (continuous_snd.prodMk σc))
  · apply Continuous.mul continuous_const
    exact ((mwShocked hh).smear
        ((mwShocked hh).V_T_dyn_shock V (hσc V))).continuous.comp
      (Sanctions.clipS'_continuous.comp
        ((mwShocked hh).toParams.F_continuous.comp (continuous_fst.prodMk σc)))

/-- The real shocked leader objective attains a maximum on `[0,1]`. -/
theorem mwLeaderObjective_isMaxOn_exists {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)) :
    ∃ a ∈ Sanctions.I,
      IsMaxOn (fun a => mwLeaderObjective hh hσc V x.val a) Sanctions.I a := by
  have hcont_a : Continuous (fun a : ℝ => mwLeaderObjective hh hσc V x.val a) :=
    (mwLeaderObjective_continuous hh hσc V).comp
      (continuous_const.prodMk continuous_id)
  exact IsCompact.exists_isMaxOn isCompact_Icc ⟨0, by simp⟩ hcont_a.continuousOn

/-- The canonical shocked leader maximizer on the physical state subtype. -/
noncomputable def mwLeaderOnS {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)) : ℝ :=
  Classical.choose (mwLeaderObjective_isMaxOn_exists hh hσc V x)

theorem mwLeaderOnS_mem {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)) :
    mwLeaderOnS hh hσc V x ∈ Sanctions.I :=
  (Classical.choose_spec (mwLeaderObjective_isMaxOn_exists hh hσc V x)).1

theorem mwLeaderOnS_isMaxOn {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)) :
    IsMaxOn (fun a => mwLeaderObjective hh hσc V x.val a) Sanctions.I
      (mwLeaderOnS hh hσc V x) :=
  (Classical.choose_spec (mwLeaderObjective_isMaxOn_exists hh hσc V x)).2

/-- Strong concavity at any positive modulus makes the real shocked leader
maximizer unique. -/
theorem mwLeaderObjective_isMaxOn_unique {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    {c_T : ℝ} (hcT : 0 < c_T)
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T
        (fun a => mwLeaderObjective hh hσc V x.val a))
    (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)) {a₁ a₂ : ℝ}
    (ha₁ : a₁ ∈ Sanctions.I) (ha₂ : a₂ ∈ Sanctions.I)
    (h₁ : IsMaxOn (fun a => mwLeaderObjective hh hσc V x.val a) Sanctions.I a₁)
    (h₂ : IsMaxOn (fun a => mwLeaderObjective hh hσc V x.val a) Sanctions.I a₂) :
    a₁ = a₂ :=
  AbstractGame.Params.isMaxOn_unique_of_strictConcaveOn
    ((sc V x).strictConcaveOn hcT) ha₁ ha₂ h₁ h₂

/-- Berge continuity of the unique canonical leader maximizer on `↥S`. -/
theorem mwLeaderOnS_continuous {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    {c_T : ℝ} (hcT : 0 < c_T)
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T
        (fun a => mwLeaderObjective hh hσc V x.val a))
    (V : SBCF) :
    Continuous (fun x : ↥(Sanctions.S : Set ℝ) => mwLeaderOnS hh hσc V x) := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  by_contra h_neg
  push Not at h_neg
  choose x_seq h_close h_far using fun n : ℕ =>
    h_neg (1 / (n + 1)) (by positivity)
  have h_x_tendsto : Tendsto x_seq atTop (𝓝 x₀) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    calc dist (x_seq n) x₀
        < 1 / (n + 1) := h_close n
      _ ≤ 1 / (N + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hn 1
      _ < δ := hN
  set a_seq : ℕ → ℝ := fun n => mwLeaderOnS hh hσc V (x_seq n) with ha_def
  have ha_mem : ∀ n, a_seq n ∈ Sanctions.I :=
    fun n => mwLeaderOnS_mem hh hσc V _
  obtain ⟨aStar, haStar_mem, φ, hφ_mono, h_sub_tendsto⟩ :=
    (isCompact_Icc : IsCompact (Sanctions.I : Set ℝ)).tendsto_subseq ha_mem
  have h_x_sub_tendsto : Tendsto (x_seq ∘ φ) atTop (𝓝 x₀) :=
    h_x_tendsto.comp hφ_mono.tendsto_atTop
  have h_a_max_sub : ∀ n, IsMaxOn
      (fun a => mwLeaderObjective hh hσc V (x_seq (φ n)).val a)
      Sanctions.I (a_seq (φ n)) :=
    fun n => mwLeaderOnS_isMaxOn hh hσc V _
  have h_aStar_max :
      IsMaxOn (fun a => mwLeaderObjective hh hσc V x₀.val a) Sanctions.I aStar := by
    intro a' ha'
    have hcont := mwLeaderObjective_continuous hh hσc V
    have h_ptn : ∀ n,
        mwLeaderObjective hh hσc V (x_seq (φ n)).val a'
          ≤ mwLeaderObjective hh hσc V (x_seq (φ n)).val (a_seq (φ n)) :=
      fun n => h_a_max_sub n ha'
    have h_lhs := (hcont.tendsto (x₀.val, a')).comp
      (((continuous_subtype_val.tendsto x₀).comp h_x_sub_tendsto).prodMk_nhds
        (tendsto_const_nhds (x := a')))
    have h_rhs := (hcont.tendsto (x₀.val, aStar)).comp
      (((continuous_subtype_val.tendsto x₀).comp h_x_sub_tendsto).prodMk_nhds
        h_sub_tendsto)
    exact le_of_tendsto_of_tendsto' h_lhs h_rhs h_ptn
  have h_eq : aStar = mwLeaderOnS hh hσc V x₀ :=
    mwLeaderObjective_isMaxOn_unique hh hσc hcT sc V x₀
      haStar_mem (mwLeaderOnS_mem hh hσc V x₀) h_aStar_max
      (mwLeaderOnS_isMaxOn hh hσc V x₀)
  rw [h_eq] at h_sub_tendsto
  have h_far_sub : ∀ n,
      ε ≤ dist (a_seq (φ n)) (mwLeaderOnS hh hσc V x₀) := by
    intro n
    rw [ha_def]
    linarith [h_far (φ n)]
  have h_tendsto_zero :
      Tendsto (fun n => dist (a_seq (φ n)) (mwLeaderOnS hh hσc V x₀))
        atTop (𝓝 0) := by
    rw [show (0 : ℝ) = dist (mwLeaderOnS hh hσc V x₀)
        (mwLeaderOnS hh hσc V x₀) from (dist_self _).symm]
    exact (continuous_id.dist continuous_const).continuousAt.tendsto.comp h_sub_tendsto
  have h_zero_ge_ε : ε ≤ 0 := by
    apply ge_of_tendsto h_tendsto_zero
    exact Filter.Eventually.of_forall h_far_sub
  linarith

/-- Globally continuous canonical leader policy, obtained by clamping the state. -/
noncomputable def mwCanonicalLeader {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (V : SBCF) (x : ℝ) : ℝ :=
  mwLeaderOnS hh hσc V (Sanctions.clipS' x)

theorem mwCanonicalLeader_continuous {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    {c_T : ℝ} (hcT : 0 < c_T)
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T
        (fun a => mwLeaderObjective hh hσc V x.val a))
    (V : SBCF) : Continuous (mwCanonicalLeader hh hσc V) :=
  (mwLeaderOnS_continuous hh hσc hcT sc V).comp Sanctions.clipS'_continuous

theorem mwCanonicalLeader_mem {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (V : SBCF) (x : ℝ) : mwCanonicalLeader hh hσc V x ∈ Sanctions.I :=
  mwLeaderOnS_mem hh hσc V (Sanctions.clipS' x)

theorem mwCanonicalLeader_isMaxOn {h : ℝ} (hh : 0 < h)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)) :
    IsMaxOn (fun a => mwLeaderObjective hh hσc V x.val a) Sanctions.I
      (mwCanonicalLeader hh hσc V x.val) := by
  have hclip : Sanctions.clipS' x.val = x := by
    apply Subtype.ext
    change Sanctions.clipS x.val = x.val
    unfold Sanctions.clipS
    rw [min_eq_right x.property.2, max_eq_right x.property.1]
  unfold mwCanonicalLeader
  rw [hclip]
  exact mwLeaderOnS_isMaxOn hh hσc V x

/-- **Symbolic canonical-leader existence at the mechanism witness.**
For any positive composite Target curvature `c_T`, nonnegative
objective-difference modulus `L_lead`, and the corresponding contraction
margin, the genuine Target objective canonically determines a continuous,
feasible, pointwise-optimal leader and the shocked feedback-Stackelberg
equilibrium exists.

The theorem derives the witness's Sender action-Lipschitz bound directly from
`mwU_S`; it does not hard-code the former curvature value `2` or the equivalent
threshold `L_lead < 1/2`.  Those values survive below only as an optional
specialization. -/
theorem mechanismWitnessParams_purified_existence_canonical_leader_symbolic
    {h : ℝ} (hh : 0 < h) {c_T L_lead : ℝ}
    (hcT : 0 < c_T) (hLlead : 0 ≤ L_lead)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T
        (fun a => mwLeaderObjective hh hσc V x.val a))
    (h_obj_diff : ∀ (V W : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      |(mwLeaderObjective hh hσc V x.val (mwCanonicalLeader hh hσc V x.val)
          - mwLeaderObjective hh hσc W x.val (mwCanonicalLeader hh hσc V x.val))
        - (mwLeaderObjective hh hσc V x.val (mwCanonicalLeader hh hσc W x.val)
          - mwLeaderObjective hh hσc W x.val (mwCanonicalLeader hh hσc W x.val))|
        ≤ (L_lead * dist V W) *
            |mwCanonicalLeader hh hσc V x.val - mwCanonicalLeader hh hσc W x.val|)
    (hmargin : (mwShocked hh).toParams.β_S + 2 * L_lead / c_T < 1) :
    Nonempty (mwShocked hh).ShockedFeedbackStackelbergEquilibriumTop := by
  refine (mwShocked hh).shockedFeedbackStackelbergTop_interior_discharged_canonical
    (mwCanonicalLeader hh hσc)
    (mwCanonicalLeader_continuous hh hσc hcT sc)
    (fun V x _hx => mwCanonicalLeader_mem hh hσc V x)
    (c_T := c_T) (L_lead := L_lead) (L_Ua := 1)
    hcT hLlead hσc ?_ ?_ ?_ ?_ ?_
  · intro V x
    simpa [mwLeaderObjective] using sc V x
  · intro V x
    simpa [mwLeaderObjective] using mwCanonicalLeader_isMaxOn hh hσc V x
  · intro V W x
    simpa [mwLeaderObjective] using h_obj_diff V W x
  · intro x a a' _ha _ha' s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hkey : (mwShocked hh).toParams.U_S x.val a s
          - (mwShocked hh).toParams.U_S x.val a' s = (a - a') * (1 - s / 2) := by
      simp only [mwShocked_toParams, mechanismWitnessParams_U_S, mwU_S]
      ring
    rw [hkey, abs_mul]
    have h2 : |1 - s / 2| ≤ 1 := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s / 2)]
      linarith
    nlinarith [h2, abs_nonneg (a - a')]
  · simpa using hmargin

/-- **Purified P3 existence with the leader selector derived.** Joint
continuity of the follower selector and strong concavity of the real Target
objective canonically determine a feasible, continuous, pointwise-optimal
leader policy via Berge's maximum theorem.  Unlike
`mechanismWitnessParams_purified_existence`, this wrapper therefore has no
free `lead`, `lead_cont`, `lead_mem`, or `lopt_obj` inputs.  The remaining
`h_obj_diff` is stated at the derived canonical leader.  This numerical form
is retained only as a compatibility corollary of the symbolic theorem above. -/
theorem mechanismWitnessParams_purified_existence_canonical_leader
    {h : ℝ} (hh : 0 < h) {L_lead : ℝ}
    (hLlead : 0 ≤ L_lead) (hmarg : L_lead < 1 / 2)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I 2
        (fun a => mwLeaderObjective hh hσc V x.val a))
    (h_obj_diff : ∀ (V W : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      |(mwLeaderObjective hh hσc V x.val (mwCanonicalLeader hh hσc V x.val)
          - mwLeaderObjective hh hσc W x.val (mwCanonicalLeader hh hσc V x.val))
        - (mwLeaderObjective hh hσc V x.val (mwCanonicalLeader hh hσc W x.val)
          - mwLeaderObjective hh hσc W x.val (mwCanonicalLeader hh hσc W x.val))|
        ≤ (L_lead * dist V W) *
            |mwCanonicalLeader hh hσc V x.val - mwCanonicalLeader hh hσc W x.val|) :
    Nonempty (mwShocked hh).ShockedFeedbackStackelbergEquilibriumTop := by
  refine mechanismWitnessParams_purified_existence_canonical_leader_symbolic
    hh (c_T := 2) (L_lead := L_lead) (by norm_num) hLlead hσc sc h_obj_diff ?_
  have hβ : (mwShocked hh).toParams.β_S = 1 / 2 := rfl
  rw [hβ]
  linarith

/-- **Constructed purified existence at P3 with a free leader** (Level 2;
compatibility corollary).  A purified feedback-Stackelberg equilibrium of the
box-shocked mechanism witness exists, given a free leader map `lead` with
feasibility `lead_mem` and pointwise optimality `lopt_obj`, joint continuity
`hσc` of the follower selector, strong concavity `sc` of the real Target
integrand at the fixed modulus `c_T = 2`, the Montrucchio/Hinderer coupling
bound `h_obj_diff` stated at `lead`, and the margin `L_lead < 1/2` (that is,
`β_S + 2·L_lead/2 < 1`).  No Schur margin is consumed.  Witness-specific: P3
has the affine transition `affineF (1/5)`; nothing here is general in `F`.

It is proved as a corollary of
`mechanismWitnessParams_purified_existence_canonical_leader`.  Strong
concavity makes the Target maximizer unique, so on every physical state the
free leader *is* the canonical leader `mwCanonicalLeader`, and the coupling
bound at `lead` is the coupling bound at the canonical leader.  The continuity
certificate `_lead_cont` is not used (the equilibrium is built from the
canonical leader, whose continuity Berge's theorem derives); it is kept only so
positional callers typecheck.  The general form, at any `c_T > 0`, is
`mechanismWitnessParams_purified_existence_canonical_leader_symbolic`. -/
theorem mechanismWitnessParams_purified_existence {h : ℝ} (hh : 0 < h)
    (lead : (SBCF) → (ℝ → ℝ))
    (_lead_cont : ∀ V, Continuous (lead V))
    (lead_mem : ∀ V, ∀ x ∈ Sanctions.S, lead V x ∈ Sanctions.I)
    {L_lead : ℝ} (hLlead : 0 ≤ L_lead) (hmarg : L_lead < 1 / 2)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I 2 (fun a => (mwShocked hh).toParams.joint_T_top_integrand
        ((mwShocked hh).smear ((mwShocked hh).V_T_dyn_shock V (hσc V)))
        ((mwShocked hh).smear V) x.val a))
    (lopt_obj : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      IsMaxOn (fun a => (mwShocked hh).toParams.joint_T_top_integrand
        ((mwShocked hh).smear ((mwShocked hh).V_T_dyn_shock V (hσc V)))
        ((mwShocked hh).smear V) x.val a)
        Sanctions.I (lead V x.val))
    (h_obj_diff : ∀ (V W : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      |((mwShocked hh).toParams.joint_T_top_integrand
            ((mwShocked hh).smear ((mwShocked hh).V_T_dyn_shock V (hσc V)))
            ((mwShocked hh).smear V) x.val (lead V x.val)
          - (mwShocked hh).toParams.joint_T_top_integrand
            ((mwShocked hh).smear ((mwShocked hh).V_T_dyn_shock W (hσc W)))
            ((mwShocked hh).smear W) x.val (lead V x.val))
        - ((mwShocked hh).toParams.joint_T_top_integrand
            ((mwShocked hh).smear ((mwShocked hh).V_T_dyn_shock V (hσc V)))
            ((mwShocked hh).smear V) x.val (lead W x.val)
          - (mwShocked hh).toParams.joint_T_top_integrand
            ((mwShocked hh).smear ((mwShocked hh).V_T_dyn_shock W (hσc W)))
            ((mwShocked hh).smear W) x.val (lead W x.val))|
        ≤ (L_lead * dist V W) * |lead V x.val - lead W x.val|) :
    Nonempty (mwShocked hh).ShockedFeedbackStackelbergEquilibriumTop := by
  -- On physical states the free leader is the unique maximizer, i.e. the canonical leader.
  have hagree : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      lead V x.val = mwCanonicalLeader hh hσc V x.val := fun V x =>
    mwLeaderObjective_isMaxOn_unique hh hσc (c_T := 2) (by norm_num) sc V x
      (lead_mem V x.val x.property) (mwCanonicalLeader_mem hh hσc V x.val)
      (lopt_obj V x) (mwCanonicalLeader_isMaxOn hh hσc V x)
  refine mechanismWitnessParams_purified_existence_canonical_leader hh hLlead hmarg
    hσc sc ?_
  intro V W x
  rw [← hagree V x, ← hagree W x]
  exact h_obj_diff V W x

/-! ## Full-width state-local canonical leader

At shock half-width `1`, the preceding physical-state Sender-uniqueness theorem
lets us use the generic state-local Berge selector directly.  This removes the
global follower-continuity input from the concrete P3 existence theorem while
leaving the two genuinely leader-side analytic obligations (`sc` and
`h_obj_diff`) explicit.
-/

/-- The smeared Target continuation used by the state-local full-width P3
leader problem. -/
noncomputable def mwTargetValueOne (V : SBCF) : SBCF :=
  (mwShocked one_pos).smear
    ((mwShocked one_pos).V_T_dyn_shock_local V
      (mwSigmaDynTop_continuous_subtype_one V))

/-- The smeared Sender continuation at full shock half-width. -/
noncomputable def mwSenderValueOne (V : SBCF) : SBCF :=
  (mwShocked one_pos).smear V

/-- The real upper-selector Target objective for the full-width, state-local
P3 construction. -/
noncomputable def mwLeaderObjectiveOne (V : SBCF) (x a : ℝ) : ℝ :=
  mechanismWitnessParams.joint_T_top_integrand
    (mwTargetValueOne V) (mwSenderValueOne V) x a

/-- The canonical full-width leader policy.  On physical states this is the
actual Target argmax; outside the physical interval it is the continuous
state-clamped extension supplied by `Params.α_on_ext`. -/
noncomputable def mwCanonicalLeaderOne (V : SBCF) (x : ℝ) : ℝ :=
  mechanismWitnessParams.α_on_ext
    (mwTargetValueOne V) (mwSenderValueOne V)
    (mechanismWitnessParams_dynamicArgmaxUnique_one V).toOnI x

/-- On physical states, Sender uniqueness identifies the upper-selector and
ordinary joint Target integrands. -/
theorem mwLeaderObjectiveOne_eq_joint (V : SBCF)
    {x : ℝ} (hx : x ∈ Sanctions.S) (a : ℝ) :
    mwLeaderObjectiveOne V x a =
      mechanismWitnessParams.joint_T_integrand
        (mwTargetValueOne V) (mwSenderValueOne V) x a := by
  exact mechanismWitnessParams.joint_T_top_integrand_eq_joint_T_integrand_of_unique
    (mechanismWitnessParams_dynamicArgmaxUnique_one V) hx a

theorem mwCanonicalLeaderOne_mem (V : SBCF) (x : ℝ) :
    mwCanonicalLeaderOne V x ∈ Sanctions.I := by
  exact mechanismWitnessParams.α_on_ext_mem
    (mwTargetValueOne V) (mwSenderValueOne V)
    (mechanismWitnessParams_dynamicArgmaxUnique_one V).toOnI x

theorem mwCanonicalLeaderOne_isMaxOn (V : SBCF)
    (x : ↥(Sanctions.S : Set ℝ)) :
    IsMaxOn (fun a => mwLeaderObjectiveOne V x.val a) Sanctions.I
      (mwCanonicalLeaderOne V x.val) := by
  have h := mechanismWitnessParams.α_on_ext_isMaxOn_of_mem
    (mwTargetValueOne V) (mwSenderValueOne V)
    (mechanismWitnessParams_dynamicArgmaxUnique_one V).toOnI x.property
  intro a ha
  change mwLeaderObjectiveOne V x.val a ≤
    mwLeaderObjectiveOne V x.val (mwCanonicalLeaderOne V x.val)
  rw [mwLeaderObjectiveOne_eq_joint V x.property a,
    mwLeaderObjectiveOne_eq_joint V x.property (mwCanonicalLeaderOne V x.val)]
  exact h ha

/-- Strong concavity at any positive modulus gives the upper-selector
uniqueness input required by the generic state-local Berge theorem. -/
theorem mwLeaderObjectiveOne_isMaxOn_unique
    {c_T : ℝ} (hcT : 0 < c_T)
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T
        (fun a => mwLeaderObjectiveOne V x.val a))
    (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)) {a₁ a₂ : ℝ}
    (ha₁ : a₁ ∈ Sanctions.I) (ha₂ : a₂ ∈ Sanctions.I)
    (h₁ : IsMaxOn
      (fun a => mechanismWitnessParams.joint_T_integrand
        (mwTargetValueOne V) (mwSenderValueOne V) x.val a)
      Sanctions.I a₁)
    (h₂ : IsMaxOn
      (fun a => mechanismWitnessParams.joint_T_integrand
        (mwTargetValueOne V) (mwSenderValueOne V) x.val a)
      Sanctions.I a₂) :
    a₁ = a₂ := by
  apply AbstractGame.Params.isMaxOn_unique_of_strictConcaveOn
    ((sc V x).strictConcaveOn hcT) ha₁ ha₂
  · intro a ha
    change mwLeaderObjectiveOne V x.val a ≤ mwLeaderObjectiveOne V x.val a₁
    rw [mwLeaderObjectiveOne_eq_joint V x.property a,
      mwLeaderObjectiveOne_eq_joint V x.property a₁]
    exact h₁ ha
  · intro a ha
    change mwLeaderObjectiveOne V x.val a ≤ mwLeaderObjectiveOne V x.val a₂
    rw [mwLeaderObjectiveOne_eq_joint V x.property a,
      mwLeaderObjectiveOne_eq_joint V x.property a₂]
    exact h₂ ha

/-- Berge continuity of the canonical full-width leader, obtained from the
already-proved physical-state Sender uniqueness and Target strong concavity. -/
theorem mwCanonicalLeaderOne_continuous
    {c_T : ℝ} (hcT : 0 < c_T)
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T
        (fun a => mwLeaderObjectiveOne V x.val a))
    (V : SBCF) :
    Continuous (mwCanonicalLeaderOne V) := by
  apply mechanismWitnessParams.α_on_ext_continuous
    (mwTargetValueOne V) (mwSenderValueOne V)
    (mechanismWitnessParams_dynamicArgmaxUnique_one V).toOnI
  intro x hx a₁ a₂ ha₁ ha₂ h₁ h₂
  exact mwLeaderObjectiveOne_isMaxOn_unique hcT sc V ⟨x, hx⟩
    ha₁ ha₂ h₁ h₂

/-- **Symbolic full-width canonical-leader existence.**  The exact affine-smear
theorem at half-width `1` discharges physical-state Sender uniqueness and
continuity for every continuation value.  At any positive composite Target
curvature `c_T`, existence therefore follows from the objective-difference
estimate and the symbolic contraction margin. -/
theorem mechanismWitnessParams_purified_existence_canonical_leader_one_local_symbolic
    {c_T L_lead : ℝ}
    (hcT : 0 < c_T) (hLlead : 0 ≤ L_lead)
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T
        (fun a => mwLeaderObjectiveOne V x.val a))
    (h_obj_diff : ∀ (V W : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      |(mwLeaderObjectiveOne V x.val (mwCanonicalLeaderOne V x.val)
          - mwLeaderObjectiveOne W x.val (mwCanonicalLeaderOne V x.val))
        - (mwLeaderObjectiveOne V x.val (mwCanonicalLeaderOne W x.val)
          - mwLeaderObjectiveOne W x.val (mwCanonicalLeaderOne W x.val))|
        ≤ (L_lead * dist V W) *
            |mwCanonicalLeaderOne V x.val - mwCanonicalLeaderOne W x.val|)
    (hmargin : (mwShocked one_pos).toParams.β_S + 2 * L_lead / c_T < 1) :
    Nonempty (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop := by
  refine (mwShocked one_pos).shockedFeedbackStackelbergTop_interior_discharged_canonical_local
      mwCanonicalLeaderOne
      (mwCanonicalLeaderOne_continuous hcT sc)
      (fun V x _hx => mwCanonicalLeaderOne_mem V x)
      (c_T := c_T) (L_lead := L_lead) (L_Ua := 1)
      hcT hLlead (by norm_num)
      mwSigmaDynTop_continuous_subtype_one ?_ ?_ ?_ ?_ ?_
  · intro V x
    simpa [mwLeaderObjectiveOne, mwTargetValueOne, mwSenderValueOne] using sc V x
  · intro V x
    simpa [mwLeaderObjectiveOne, mwTargetValueOne, mwSenderValueOne] using
      mwCanonicalLeaderOne_isMaxOn V x
  · intro V W x
    simpa [mwLeaderObjectiveOne, mwTargetValueOne, mwSenderValueOne] using
      h_obj_diff V W x
  · intro x a a' _ha _ha' s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hkey : (mwShocked one_pos).toParams.U_S x.val a s
          - (mwShocked one_pos).toParams.U_S x.val a' s =
        (a - a') * (1 - s / 2) := by
      simp only [mwShocked_toParams, mechanismWitnessParams_U_S, mwU_S]
      ring
    rw [hkey, abs_mul]
    have h2 : |1 - s / 2| ≤ 1 := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s / 2)]
      linarith
    nlinarith [h2, abs_nonneg (a - a')]
  · simpa using hmargin

/-- The former fixed-modulus full-width theorem is retained as a compatibility
corollary of the symbolic state-local theorem. -/
theorem mechanismWitnessParams_purified_existence_canonical_leader_one_local
    {L_lead : ℝ}
    (hLlead : 0 ≤ L_lead) (hmarg : L_lead < 1 / 2)
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I 2
        (fun a => mwLeaderObjectiveOne V x.val a))
    (h_obj_diff : ∀ (V W : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      |(mwLeaderObjectiveOne V x.val (mwCanonicalLeaderOne V x.val)
          - mwLeaderObjectiveOne W x.val (mwCanonicalLeaderOne V x.val))
        - (mwLeaderObjectiveOne V x.val (mwCanonicalLeaderOne W x.val)
          - mwLeaderObjectiveOne W x.val (mwCanonicalLeaderOne W x.val))|
        ≤ (L_lead * dist V W) *
            |mwCanonicalLeaderOne V x.val - mwCanonicalLeaderOne W x.val|) :
    Nonempty (mwShocked one_pos).ShockedFeedbackStackelbergEquilibriumTop := by
  refine mechanismWitnessParams_purified_existence_canonical_leader_one_local_symbolic
    (c_T := 2) (L_lead := L_lead) (by norm_num) hLlead sc h_obj_diff ?_
  have hβ : (mwShocked one_pos).toParams.β_S = 1 / 2 := rfl
  rw [hβ]
  linarith

/-- **Purified persistence / dynamic-over-myopic dominance at P3** (the economic payoff).
At a *constructed* purified equilibrium `E` of the box-shocked mechanism witness, on the
high basin `[xbar, 1]` the forward-looking realised sanction dominates the myopic stage
response for every period — metastable lock-in at a genuinely-existing, mechanism-active
equilibrium.  Composes `mechanismWitnessParams_purified_existence_canonical_leader_symbolic`
(existence, via purification and the derived canonical leader) with
`shocked_dynamicTopSanctions_ge_myopic_on_basin` (the proved shocked Goal-2 dominance),
applied at the equilibrium's own `E.V_S`, `E.α`.  Witness-specific: P3 has the affine
transition `affineF (1/5)`; only the dominance step is the general shocked theorem.

The Target's policy is not an input: the leader is the canonical leader
`mwCanonicalLeader`, the unique maximizer, so no free leader map and none of its certificates
(`lead`, `lead_cont`, `lead_mem`, `lopt_obj`) are assumed.  The composite Target curvature
`c_T` is any positive number, not the fixed modulus `2`, and the contraction condition is the
symbolic margin `β_S + 2·L_lead/c_T < 1`, not `L_lead < 1/2`; the coupling bound
`h_obj_diff` is stated at the canonical leader.  The free-leader inputs of
`mechanismWitnessParams_purified_existence` imply these (strong concavity makes the free
leader equal the canonical leader on physical states).  Conditional surface: `hσc`, `sc` and
`h_obj_diff` (existence) plus the basin regime conditions — the myopic comparator stays
in/below the basin (`hMyo_basin`, `hMyoCeiling`), and the dynamic rule is basin-monotone and
floored (`hDynReg`, an input: the full-interval strong-rally gate cannot supply it on a
basin containing `x = 1/2`, see `mwSenderStage_no_positive_lowerSlope_at_half`).
**No Schur margin.** -/
theorem mechanismWitnessParams_purified_persistence {h : ℝ} (hh : 0 < h)
    {c_T L_lead : ℝ} (hcT : 0 < c_T) (hLlead : 0 ≤ L_lead)
    (hσc : ∀ V : SBCF,
      Continuous (fun xa : ℝ × ℝ =>
        (mwShocked hh).toParams.σ_dyn_top ((mwShocked hh).smear V) xa.1 xa.2))
    (sc : ∀ (V : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      StrongConcaveOn Sanctions.I c_T
        (fun a => mwLeaderObjective hh hσc V x.val a))
    (h_obj_diff : ∀ (V W : SBCF) (x : ↥(Sanctions.S : Set ℝ)),
      |(mwLeaderObjective hh hσc V x.val (mwCanonicalLeader hh hσc V x.val)
          - mwLeaderObjective hh hσc W x.val (mwCanonicalLeader hh hσc V x.val))
        - (mwLeaderObjective hh hσc V x.val (mwCanonicalLeader hh hσc W x.val)
          - mwLeaderObjective hh hσc W x.val (mwCanonicalLeader hh hσc W x.val))|
        ≤ (L_lead * dist V W) *
            |mwCanonicalLeader hh hσc V x.val - mwCanonicalLeader hh hσc W x.val|)
    (hmargin : (mwShocked hh).toParams.β_S + 2 * L_lead / c_T < 1)
    (M : (mwShocked hh).toParams.MyopicFeedbackEquilibrium) {xbar sbar x₀ : ℝ}
    (hMyo_basin : ∀ x ∈ Set.Icc xbar 1,
      (mwShocked hh).toParams.σ x (M.α x) ∈ Set.Icc xbar 1)
    (hMyoCeiling : ∀ x ∈ Set.Icc xbar 1,
      (mwShocked hh).toParams.σ x (M.α x) ≤ max x sbar)
    (hx₀ : x₀ ∈ Set.Icc xbar 1)
    (hDynReg : ∀ E : (mwShocked hh).ShockedFeedbackStackelbergEquilibriumTop,
      MonotoneOn ((mwShocked hh).toParams.dynamicTopRealizedRule
          ((mwShocked hh).smear E.V_S) E.α) (Set.Icc xbar 1)
      ∧ ∀ x ∈ Set.Icc xbar 1, max x sbar ≤
          (mwShocked hh).toParams.dynamicTopRealizedRule
            ((mwShocked hh).smear E.V_S) E.α x) :
    ∃ E : (mwShocked hh).ShockedFeedbackStackelbergEquilibriumTop, ∀ n,
      (mwShocked hh).toParams.ruleSanctions
          (fun x => (mwShocked hh).toParams.σ x (M.α x)) x₀ n
        ≤ (mwShocked hh).toParams.ruleSanctions
            ((mwShocked hh).toParams.dynamicTopRealizedRule
              ((mwShocked hh).smear E.V_S) E.α) x₀ n := by
  obtain ⟨E⟩ := mechanismWitnessParams_purified_existence_canonical_leader_symbolic hh
    hcT hLlead hσc sc h_obj_diff hmargin
  exact ⟨E, (mwShocked hh).shocked_dynamicTopSanctions_ge_myopic_on_basin
    hMyo_basin (hDynReg E).1 (hDynReg E).2 hMyoCeiling hx₀⟩

end Examples

namespace AbstractGame

/-- **A concrete, closed `ShockedParams` term** — the Eaton-Engers witness shocked
by the uniform box kernel of half-width `1`. Inhabiting the class discharges the
Rule-9 vacuity exposure: every shocked existence theorem (corner and interior) is
no longer conditional on a possibly-empty parameter class.

Lives here in `Examples/` (instantiating the parametric box-smear wiring layer
`Theory/Shocked/MovingAverageShock.lean` at the `Examples/` Eaton-Engers
parameter point) so that the Theory layer never imports `Examples/`; the
namespace is `Sanctions.AbstractGame`, matching the wiring layer, so the
identifier cited by the paper and register resolves unchanged. -/
noncomputable def eatonEngersMovAvgShock : ShockedParams :=
  movAvgShockedParams Sanctions.Examples.eatonEngersParams (h := 1) one_pos

end AbstractGame

end Sanctions
