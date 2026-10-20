/-
Sanctions/Theory/Equilibrium/DefianceCore.lean

**The defiance core over an arbitrary economy** (round BB, 2026-09-28; doc 110
items G1 and R12a, on the user's word).

Over any `Params` — both stage payoffs abstract, the transition general — take a
top-selector feedback Stackelberg equilibrium whose **realised sanction rule is
nondecreasing in the state**. Suppose:

* the transition rises at least at rate `g_lo` in the state and at least at rate
  `d_lo` in the sanction (two lower chords; no sign on `d_lo` is needed);
* the Sender's stage payoff has decreasing differences in (sanction; compliance)
  against full defiance: at any compliance `a`, the gain from a higher sanction
  is at most its gain at `a = 0`, so a concession never raises the marginal
  return to sanctioning above its level under defiance (placation, as a sign);
* at full defiance the Target's stage payoff loses at most `c` per unit of
  sanction and gains at least `v ≥ 0` per unit of state, and compliance is weakly
  costly at every sanction, `U_T(x, a, s) ≤ U_T(x, 0, s)`;
* the unrefined loss-offset margin `c ≤ β_T·d_lo·g⁰`, where `g⁰ = v/(1 − β_T·g_lo)`.

Then the Target's value rises at least at rate `g⁰` in the state
(`FeedbackStackelbergEquilibriumTop.lowerSlope_of_rule_monotone`), and, when
compliance is strictly costly (`U_T(x, a, s) < U_T(x, 0, s)` for `a > 0`), the
Target defies at every state (`…policy_eq_zero_of_rule_monotone_of_costSign`). The
pinned `…policy_eq_zero_of_rule_monotone` is its corollary at a per-unit compliance
cost `ℓ > 0`, under decreasing differences over all compliance pairs and `0 ≤ d_lo`.

**What is new against `PlacableSenderUniqueness.lean`.** That file proved the same
two conclusions on the chord economy (`ChordEconomy`, 78 fields) and required the
policy to be nonincreasing as well as the rule nondecreasing. Here:

1. **No policy condition.** The one-step comparison sets the higher state's value
   against its own deviation to full defiance (`α_opt_top`), instead of against
   its policy. That deviation raises the sanction above the lower state's
   (decreasing differences plus the monotone rule), so the successor pair stays
   ordered and the discounted-extremum argument closes with no monotonicity of
   the policy.
2. **No chord-economy structure.** The Sender's curvature, the carrier, the
   Riccati closure, interiority and the stage-relief margin are never read. What
   remains is two transition chords, one sign on the Sender's payoff (against
   full defiance), two Target rates at full defiance, and the sign of the
   Target's compliance cost.
3. **The Target conditions are needed at full defiance only** (compliance `0`),
   plus the sign of the cost of compliance against `0`.

`β_T·g_lo < 1` is derived from the state chord, the diagonal and feasibility
(`βT_mul_lowerChord_lt_one`), not assumed. `g_lo + d_lo ≤ 1`
(`lowerChords_add_le_one`) also holds, but the core no longer reads it.

Round BG (2026-10-06; renovation item BG2.9): the core's hypotheses were weakened
in place. The slope bound `β_T·g_lo < 1` no longer takes the sanction chord or
`0 ≤ d_lo`; the cost of compliance is a sign, not a per-unit rate `ℓ`; and
decreasing differences are required only against full defiance
(`σ_dyn_top_le_zero_of_DD0`). The pinned headline
`policy_eq_zero_of_rule_monotone` keeps its statement and is derived from the
weaker sibling (`DD0_of_decreasingDifferencesOn`, `strictCost_of_linearCost`).

**Scope.** A statement about every equilibrium of the top-selector class
(continuous Target policies) whose realised rule is nondecreasing: a restriction
on the quantifier, not an assumption about the economy. Equilibria whose rule
falls somewhere are not covered, and whether any exist is open. Rule 9B: this
generalises the chord class, and every member of that class satisfies the
hypotheses (`Examples/PlacableSenderDefianceCore.lean`). A member *outside* the chord
class at which the core applies is exhibited in
`Examples/DefianceCoreOutsideChordWitness.lean` (`defiance_core_outside_chord_class`: its
Target's compliance cost is not monotone), so the extra generality is witnessed, as an
existence statement only. Rule 22: general in `F`. Rule 3: each hypothesis restates a
consequence of a chord-class field or theorem hypothesis at the `Params` level (T2 at
compliance `0`, as a sign; T4 and T6 at full defiance; S10 as a sign, against full
defiance; the two lower chords; `LossOffset₀`); none is new.
-/
import Sanctions.Theory.Equilibrium.CertifiedEquilibria
import Sanctions.Theory.Certificates.TargetSanctionLossOffset
import Sanctions.Foundations.DiscountedExtremum
import Sanctions.Foundations.TransitionChords

namespace Sanctions
namespace AbstractGame
namespace Params

open Set Filter Topology BoundedContinuousFunction

noncomputable section

variable (p : Params)

/-- **The lower chords sum to at most one.** A lower state chord `g_lo` at the
full sanction and a lower sanction chord `d_lo` at the zero state, read across
the diagonal `F(0,0) = 0`, `F(1,1) = 1`. -/
theorem lowerChords_add_le_one {gl dl : ℝ}
    (hband : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s)
    (hSlo : Sanctions.TransitionChords.SanctionLowerChord p.F dl) :
    gl + dl ≤ 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hb := hband 1 h1 0 h0 1 h1 zero_le_one
  have hs := hSlo h0 h0 h1 zero_le_one
  have e0 := p.F_diag 0
  have e1 := p.F_diag 1
  linarith

/-- With the lower state chord, the Target discounts the state's rise strictly:
`β_T·g_lo < 1`. General in `F`.

Round BG (2026-10-06): the sanction lower chord `hSlo` and its sign `0 ≤ d_lo` were
dropped. The state chord at the full sanction, read across the diagonal
`F(1,1) = 1` and the feasibility `F(0,1) ≥ 0`, already gives `g_lo ≤ 1`: the state
cannot rise faster than one for one over the whole square. Then `β_T < 1` does the
rest. -/
theorem βT_mul_lowerChord_lt_one {gl : ℝ}
    (hband : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s) :
    p.β_T * gl < 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hb := hband 1 h1 0 h0 1 h1 zero_le_one
  have e1 := p.F_diag 1
  have hF01 := (p.F_mem 0 1 h0 h1).1
  have hgl : gl ≤ 1 := by linarith
  have hβ0 := p.β_T_mem.1
  have hβ1 := p.β_T_mem.2
  rcases le_or_gt gl 0 with hg | hg
  · have : p.β_T * gl ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ0 hg
    linarith
  · have : p.β_T * gl ≤ p.β_T * 1 := mul_le_mul_of_nonneg_left hgl hβ0
    linarith

/-- The defiance slope `g⁰ = v/(1 − β_T·g_lo)`. -/
def defianceSlope (gl v : ℝ) : ℝ := v / (1 - p.β_T * gl)

/-- **Decreasing differences against full defiance bound the greatest Sender
selector by its value at full defiance.** General in `F`. Suppose that at the
state `x`, for every compliance `a` and every ordered sanction pair `s ≤ s'`, the
Sender's stage gain from the higher sanction at `a` is at most its gain at `a = 0`.
Then, for any continuation value, the greatest forward-looking best response to `a`
is at most the greatest best response to full defiance.

This is the only consequence of decreasing differences that the defiance core
reads. `σ_dyn_top_antitoneOn_a_of_DD` gets the whole antitone profile in `a`, but
needs decreasing differences over every pair of compliance levels; here only the
pairs `(0, a)` are required. Proof: if the response to `a` were above the response
to `0`, the differences would carry its gain over to `a = 0`, making it a best
response to `0` too, above the greatest one. -/
theorem σ_dyn_top_le_zero_of_DD0 (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) {x a : ℝ}
    (hDD0 : ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, s ≤ s' →
      p.U_S x a s' - p.U_S x a s ≤ p.U_S x 0 s' - p.U_S x 0 s)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    p.σ_dyn_top V_S x a ≤ p.σ_dyn_top V_S x 0 := by
  rcases le_total (p.σ_dyn_top V_S x a) (p.σ_dyn_top V_S x 0) with h | h
  · exact h
  · have haI := p.σ_dyn_top_mem_I V_S x a
    have h0I := p.σ_dyn_top_mem_I V_S x 0
    -- the response to `a` beats the response to `0` at compliance `a`
    have hmaxa : p.U_S x a (p.σ_dyn_top V_S x 0)
          + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x 0)))
        ≤ p.U_S x a (p.σ_dyn_top V_S x a)
          + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x a))) :=
      isMaxOn_iff.mp (p.σ_dyn_top_isMaxOn V_S x a) _ h0I
    -- and the differences carry that gain over to full defiance
    have hd := hDD0 a ha _ h0I _ haI h
    have hJ : p.U_S x 0 (p.σ_dyn_top V_S x 0)
          + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x 0)))
        ≤ p.U_S x 0 (p.σ_dyn_top V_S x a)
          + p.β_S * V_S (Sanctions.clipS' (p.F x (p.σ_dyn_top V_S x a))) := by
      linarith
    have hmem : p.σ_dyn_top V_S x a ∈ p.dynamicArgmaxSet V_S x 0 :=
      ⟨haI, isMaxOn_iff.mpr fun y hy =>
        le_trans (isMaxOn_iff.mp (p.σ_dyn_top_isMaxOn V_S x 0) y hy) hJ⟩
    exact le_csSup (p.dynamicArgmaxSet_bddAbove V_S x 0) hmem

/-- Decreasing differences over every pair of compliance levels give decreasing
differences against full defiance, the form `σ_dyn_top_le_zero_of_DD0` reads.
General in `F` (no transition is read; a statement about the Sender's stage payoff
only). -/
theorem DD0_of_decreasingDifferencesOn {x : ℝ}
    (hDD : Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
      (fun s a => p.U_S x a s)) :
    ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, s ≤ s' →
      p.U_S x a s' - p.U_S x a s ≤ p.U_S x 0 s' - p.U_S x 0 s :=
  fun _ ha _ hs _ hs' hss => hDD hs hs' hss ⟨le_rfl, zero_le_one⟩ ha ha.1

/-- A compliance cost of at least `ℓ ≥ 0` per unit makes compliance weakly costly:
`U_T(x, a, s) ≤ U_T(x, 0, s)`, the sign the defiance core reads. General in `F` (no
transition is read; a statement about the Target's stage payoff only). -/
theorem weakCost_of_linearCost {ℓ : ℝ}
    (hcost : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
      ℓ * a ≤ p.U_T x 0 s - p.U_T x a s)
    (hℓ : 0 ≤ ℓ) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
      p.U_T x a s ≤ p.U_T x 0 s := by
  intro x hx s hs a ha
  have h := hcost x hx s hs a ha
  have h' : 0 ≤ ℓ * a := mul_nonneg hℓ ha.1
  linarith

/-- A compliance cost of at least `ℓ > 0` per unit makes any positive compliance
strictly costly: `U_T(x, a, s) < U_T(x, 0, s)` for `a > 0`. General in `F` (no
transition is read; a statement about the Target's stage payoff only). -/
theorem strictCost_of_linearCost {ℓ : ℝ}
    (hcost : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
      ℓ * a ≤ p.U_T x 0 s - p.U_T x a s)
    (hℓ : 0 < ℓ) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, 0 < a →
      p.U_T x a s < p.U_T x 0 s := by
  intro x hx s hs a ha hpos
  have h := hcost x hx s hs a ha
  have h' : 0 < ℓ * a := mul_pos hℓ hpos
  linarith

/-- Strictly costly positive compliance makes compliance weakly costly at every
level (with equality at `a = 0`). General in `F` (no transition is read; a statement
about the Target's stage payoff only). -/
theorem weakCost_of_strictCost
    (hcost : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, 0 < a →
      p.U_T x a s < p.U_T x 0 s) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
      p.U_T x a s ≤ p.U_T x 0 s := by
  intro x hx s hs a ha
  rcases ha.1.eq_or_lt with h | h
  · subst h
    exact le_rfl
  · exact (hcost x hx s hs a ha h).le

namespace FeedbackStackelbergEquilibriumTop

variable {p}

/-- The deficit of the Target's value below the slope `g` at an ordered pair of
states. -/
def slopeDeficit (Eq : p.FeedbackStackelbergEquilibriumTop) (g : ℝ)
    (q : {q : ↥(Sanctions.S : Set ℝ) × ↥(Sanctions.S : Set ℝ) // q.1 ≤ q.2}) : ℝ :=
  Eq.V_T q.1.2 - Eq.V_T q.1.1 - g * (q.1.2.val - q.1.1.val)

/-- The successor pair: the lower state moves under its own realised sanction,
the higher state under the sanction its deviation to full defiance would draw.
General in `F`. Round BG (2026-10-06): the ordering of the pair reads decreasing
differences against full defiance only (`hDD0`, via `σ_dyn_top_le_zero_of_DD0`),
not over every pair of compliance levels. -/
def defianceSuccessor (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hrule : MonotoneOn (p.dynamicEquilibriumRule Eq) Sanctions.S)
    (hDD0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ s' ∈ Icc (0 : ℝ) 1, s ≤ s' → p.U_S x a s' - p.U_S x a s ≤ p.U_S x 0 s' - p.U_S x 0 s)
    (q : {q : ↥(Sanctions.S : Set ℝ) × ↥(Sanctions.S : Set ℝ) // q.1 ≤ q.2}) :
    {q : ↥(Sanctions.S : Set ℝ) × ↥(Sanctions.S : Set ℝ) // q.1 ≤ q.2} :=
  ⟨(Sanctions.clipS' (p.F q.1.1.val (p.σ_dyn_top Eq.V_S q.1.1.val (Eq.α q.1.1.val))),
    Sanctions.clipS' (p.F q.1.2.val (p.σ_dyn_top Eq.V_S q.1.2.val 0))), by
    have hy₁ := q.1.1.property
    have hy₂ := q.1.2.property
    have hle : q.1.1.val ≤ q.1.2.val := q.2
    have hα₂ := Eq.α_mem q.1.2.val hy₂
    have hr : p.σ_dyn_top Eq.V_S q.1.1.val (Eq.α q.1.1.val)
        ≤ p.σ_dyn_top Eq.V_S q.1.2.val (Eq.α q.1.2.val) := hrule hy₁ hy₂ hle
    have hd : p.σ_dyn_top Eq.V_S q.1.2.val (Eq.α q.1.2.val) ≤ p.σ_dyn_top Eq.V_S q.1.2.val 0 :=
      p.σ_dyn_top_le_zero_of_DD0 Eq.V_S (hDD0 _ hy₂) hα₂
    exact Sanctions.clipS'_mono
      ((p.F_mono_s _ (hr.trans hd)).trans (p.F_mono_x _ hle))⟩

/-- **The one-step deficit inequality, with no policy condition.** General in `F`.
Round BG (2026-10-06): weakened in place. The sign `0 ≤ d_lo` was dropped (the slope
bound no longer reads it); the per-unit compliance cost `(ℓ, hcost, hℓ)` was replaced
by the weak cost sign `U_T(x, a, s) ≤ U_T(x, 0, s)`, which is all the step reads at
the lower state; and decreasing differences are required only against full
defiance. -/
theorem slopeDeficit_step {gl dl c v : ℝ}
    (hband : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s)
    (hSlo : Sanctions.TransitionChords.SanctionLowerChord p.F dl)
    (hDD0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ s' ∈ Icc (0 : ℝ) 1, s ≤ s' → p.U_S x a s' - p.U_S x a s ≤ p.U_S x 0 s' - p.U_S x 0 s)
    (hcost : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
      p.U_T x a s ≤ p.U_T x 0 s)
    (hpain : ∀ x ∈ Icc (0 : ℝ) 1, LowerLossSlopeOn (fun s => p.U_T x 0 s) (Icc (0 : ℝ) 1) c)
    (hstate : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 s - p.U_T y₁ 0 s)
    (hv : 0 ≤ v)
    (hTM : c ≤ p.β_T * dl * p.defianceSlope gl v)
    (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hrule : MonotoneOn (p.dynamicEquilibriumRule Eq) Sanctions.S)
    (q : {q : ↥(Sanctions.S : Set ℝ) × ↥(Sanctions.S : Set ℝ) // q.1 ≤ q.2}) :
    p.β_T * Eq.slopeDeficit (p.defianceSlope gl v) (Eq.defianceSuccessor hrule hDD0 q)
      ≤ Eq.slopeDeficit (p.defianceSlope gl v) q := by
  obtain ⟨⟨y₁, y₂⟩, hle⟩ := q
  have hy₁ : y₁.val ∈ Icc (0 : ℝ) 1 := y₁.property
  have hy₂ : y₂.val ∈ Icc (0 : ℝ) 1 := y₂.property
  have hyle : y₁.val ≤ y₂.val := hle
  have hα₁ := Eq.α_mem y₁.val hy₁
  have hα₂ := Eq.α_mem y₂.val hy₂
  set s₁ := p.σ_dyn_top Eq.V_S y₁.val (Eq.α y₁.val) with hs₁def
  set s₂ := p.σ_dyn_top Eq.V_S y₂.val 0 with hs₂def
  have hs₁I : s₁ ∈ Icc (0 : ℝ) 1 := p.σ_dyn_top_mem_I _ _ _
  have hs₂I : s₂ ∈ Icc (0 : ℝ) 1 := p.σ_dyn_top_mem_I _ _ _
  have hr : s₁ ≤ p.σ_dyn_top Eq.V_S y₂.val (Eq.α y₂.val) := hrule hy₁ hy₂ hyle
  have hd : p.σ_dyn_top Eq.V_S y₂.val (Eq.α y₂.val) ≤ s₂ :=
    p.σ_dyn_top_le_zero_of_DD0 Eq.V_S (hDD0 _ hy₂) hα₂
  have hs : s₁ ≤ s₂ := hr.trans hd
  have hF₁ := p.F_mem _ _ hy₁ hs₁I
  have hF₂ := p.F_mem _ _ hy₂ hs₂I
  -- the value at the lower state is its integrand at its policy
  have hV₁ : Eq.V_T y₁ = p.U_T y₁.val (Eq.α y₁.val) s₁
      + p.β_T * Eq.V_T (Sanctions.clipS' (p.F y₁.val s₁)) := by
    rw [FeedbackStackelbergEquilibriumTop.V_T_eq_at_policy p Eq y₁]; rfl
  -- the value at the higher state is at least its integrand at full defiance
  have hV₂ : p.U_T y₂.val 0 s₂ + p.β_T * Eq.V_T (Sanctions.clipS' (p.F y₂.val s₂))
      ≤ Eq.V_T y₂ := by
    have hopt := Eq.α_opt_top y₂.val hy₂ (show (0 : ℝ) ∈ Sanctions.I from ⟨le_rfl, zero_le_one⟩)
    simp only [Set.mem_setOf_eq] at hopt
    rw [FeedbackStackelbergEquilibriumTop.V_T_eq_at_policy p Eq y₂]
    exact hopt
  -- the stage: compliance weakly costly at the lower state
  have hc₁ := hcost y₁.val hy₁ s₁ hs₁I (Eq.α y₁.val) hα₁
  -- pain at most `c` at the higher state; state rate at least `v` at the lower sanction
  have hp := hpain y₂.val hy₂ s₁ hs₁I s₂ hs₂I hs
  simp only at hp
  have hst := hstate s₁ hs₁I y₁.val hy₁ y₂.val hy₂ hyle
  -- the successor rises at least `g_lo·Δy + d_lo·Δs`
  have hb := hband s₂ hs₂I y₁.val hy₁ y₂.val hy₂ hyle
  have hsc := hSlo hy₁ hs₁I hs₂I hs
  -- the slope `g⁰`
  have hβgl := p.βT_mul_lowerChord_lt_one hband
  set g := p.defianceSlope gl v with hgdef
  have hgmul : g * (1 - p.β_T * gl) = v := by
    rw [hgdef, defianceSlope]; exact div_mul_cancel₀ _ (by linarith)
  have hg0 : 0 ≤ g := by rw [hgdef, defianceSlope]; exact div_nonneg hv (by linarith)
  have hβ := p.β_T_mem.1
  have hβg : 0 ≤ p.β_T * g := mul_nonneg hβ hg0
  have hsucc := mul_le_mul_of_nonneg_left
    (show gl * (y₂.val - y₁.val) + dl * (s₂ - s₁) ≤ p.F y₂.val s₂ - p.F y₁.val s₁ by linarith)
    hβg
  have hΔs : 0 ≤ (p.β_T * dl * g - c) * (s₂ - s₁) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hs)
  have hgΔ : g * (y₂.val - y₁.val)
      = v * (y₂.val - y₁.val) + p.β_T * g * (gl * (y₂.val - y₁.val)) := by
    rw [← hgmul]; ring
  simp only [slopeDeficit, defianceSuccessor]
  rw [Sanctions.clipS'_val_eq_of_mem hF₁, Sanctions.clipS'_val_eq_of_mem hF₂]
  nlinarith [hV₁, hV₂, hc₁, hp, hst, hsucc, hΔs, hgΔ]

/-- **The Target's value has lower slope `g⁰`** at every equilibrium of the
top-selector class whose realised rule is nondecreasing, under the unrefined
loss-offset margin. No condition on the policy. General in `F`.

Round BG (2026-10-06): weakened in place, as in `slopeDeficit_step`. The sign
`0 ≤ d_lo` was dropped; compliance need only be weakly costly,
`U_T(x, a, s) ≤ U_T(x, 0, s)`, instead of costing at least `ℓ ≥ 0` per unit; and the
Sender's stage payoff needs decreasing differences only against full defiance. -/
theorem lowerSlope_of_rule_monotone {gl dl c v : ℝ}
    (hband : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s)
    (hSlo : Sanctions.TransitionChords.SanctionLowerChord p.F dl)
    (hDD0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ s' ∈ Icc (0 : ℝ) 1, s ≤ s' → p.U_S x a s' - p.U_S x a s ≤ p.U_S x 0 s' - p.U_S x 0 s)
    (hcost : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
      p.U_T x a s ≤ p.U_T x 0 s)
    (hpain : ∀ x ∈ Icc (0 : ℝ) 1, LowerLossSlopeOn (fun s => p.U_T x 0 s) (Icc (0 : ℝ) 1) c)
    (hstate : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 s - p.U_T y₁ 0 s)
    (hv : 0 ≤ v)
    (hTM : c ≤ p.β_T * dl * p.defianceSlope gl v)
    (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hrule : MonotoneOn (p.dynamicEquilibriumRule Eq) Sanctions.S) :
    LowerSlopeOnValue Eq.V_T (p.defianceSlope gl v) := by
  set g := p.defianceSlope gl v with hgdef
  have hβgl := p.βT_mul_lowerChord_lt_one hband
  have hg0 : 0 ≤ g := by rw [hgdef, defianceSlope]; exact div_nonneg hv (by linarith)
  have hbdd : BddBelow (Set.range (Eq.slopeDeficit g)) := by
    refine ⟨-(2 * ‖Eq.V_T‖ + g), ?_⟩
    rintro _ ⟨⟨⟨y₁, y₂⟩, hle⟩, rfl⟩
    simp only [slopeDeficit]
    have h1 := BoundedContinuousFunction.norm_coe_le_norm Eq.V_T y₁
    have h2 := BoundedContinuousFunction.norm_coe_le_norm Eq.V_T y₂
    rw [Real.norm_eq_abs] at h1 h2
    have hy₁ := y₁.property
    have hy₂ := y₂.property
    have h3 : g * (y₂.val - y₁.val) ≤ g := by
      have : y₂.val - y₁.val ≤ 1 := by linarith [hy₁.1, hy₂.2]
      calc g * (y₂.val - y₁.val) ≤ g * 1 := mul_le_mul_of_nonneg_left this hg0
        _ = g := mul_one g
    have h4 := abs_le.mp h1
    have h5 := abs_le.mp h2
    linarith
  intro y₁ y₂ hle
  have h := Sanctions.Foundations.DiscountedExtremum.nonneg_of_mul_comp_le p.β_T_mem.1 p.β_T_mem.2
    hbdd (Eq.slopeDeficit_step hband hSlo hDD0 hcost hpain hstate hv hTM hrule)
    ⟨(y₁, y₂), hle⟩
  simp only [slopeDeficit] at h
  have hyle : y₁.val ≤ y₂.val := hle
  have hd : dist y₁ y₂ = y₂.val - y₁.val := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hd]
  linarith

/-- **The Target defies at every state**, at every equilibrium of the
top-selector class whose realised rule is nondecreasing, under the unrefined
loss-offset margin and strictly costly compliance. No condition on the policy.
General in `F`.

The weak sibling of the pinned `policy_eq_zero_of_rule_monotone` (round BG,
2026-10-06). Against it, three hypotheses are weaker: the per-unit compliance cost
`ℓ > 0` becomes the sign `U_T(x, a, s) < U_T(x, 0, s)` for every positive compliance
`a` (any positive concession costs the Target something today, at no stated rate);
decreasing differences of the Sender's stage payoff are required only against full
defiance; and `0 ≤ d_lo` is dropped. -/
theorem policy_eq_zero_of_rule_monotone_of_costSign {gl dl c v : ℝ}
    (hband : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s)
    (hSlo : Sanctions.TransitionChords.SanctionLowerChord p.F dl)
    (hDD0 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ s' ∈ Icc (0 : ℝ) 1, s ≤ s' → p.U_S x a s' - p.U_S x a s ≤ p.U_S x 0 s' - p.U_S x 0 s)
    (hcost : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1, 0 < a →
      p.U_T x a s < p.U_T x 0 s)
    (hpain : ∀ x ∈ Icc (0 : ℝ) 1, LowerLossSlopeOn (fun s => p.U_T x 0 s) (Icc (0 : ℝ) 1) c)
    (hstate : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 s - p.U_T y₁ 0 s)
    (hv : 0 ≤ v)
    (hTM : c ≤ p.β_T * dl * p.defianceSlope gl v)
    (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hrule : MonotoneOn (p.dynamicEquilibriumRule Eq) Sanctions.S)
    {x : ℝ} (hx : x ∈ Sanctions.I) : Eq.α x = 0 := by
  have hslope := Eq.lowerSlope_of_rule_monotone hband hSlo hDD0 (p.weakCost_of_strictCost hcost)
    hpain hstate hv hTM hrule
  set g := p.defianceSlope gl v with hgdef
  have hβgl := p.βT_mul_lowerChord_lt_one hband
  have hg0 : 0 ≤ g := by rw [hgdef, defianceSlope]; exact div_nonneg hv (by linarith)
  have hαI := Eq.α_mem x hx
  by_contra hne
  have hpos : 0 < Eq.α x := lt_of_le_of_ne hαI.1 (Ne.symm hne)
  have hopt := Eq.α_opt_top x hx (show (0 : ℝ) ∈ Sanctions.I from ⟨le_rfl, zero_le_one⟩)
  simp only [Set.mem_setOf_eq] at hopt
  set s₀ := p.σ_dyn_top Eq.V_S x 0 with hs₀def
  set sα := p.σ_dyn_top Eq.V_S x (Eq.α x) with hsαdef
  have hs : sα ≤ s₀ := p.σ_dyn_top_le_zero_of_DD0 Eq.V_S (hDD0 x hx) hαI
  have hs₀I : s₀ ∈ Icc (0 : ℝ) 1 := p.σ_dyn_top_mem_I _ _ _
  have hsαI : sα ∈ Icc (0 : ℝ) 1 := p.σ_dyn_top_mem_I _ _ _
  have hF₀ := p.F_mem _ _ hx hs₀I
  have hFα := p.F_mem _ _ hx hsαI
  have hz : p.F x sα ≤ p.F x s₀ := p.F_mono_s x hs
  have hchord : dl * (s₀ - sα) ≤ p.F x s₀ - p.F x sα := hSlo hx hsαI hs₀I hs
  -- the continuation gain of the deviation, through the value's lower slope
  have hsl : g * (p.F x s₀ - p.F x sα)
      ≤ Eq.V_T (Sanctions.clipS' (p.F x s₀)) - Eq.V_T (Sanctions.clipS' (p.F x sα)) := by
    have h := hslope (Sanctions.clipS' (p.F x sα)) (Sanctions.clipS' (p.F x s₀))
      (Sanctions.clipS'_mono hz)
    have hdist : dist (Sanctions.clipS' (p.F x sα)) (Sanctions.clipS' (p.F x s₀))
        = p.F x s₀ - p.F x sα := by
      rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hFα,
        Sanctions.clipS'_val_eq_of_mem hF₀, abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hdist] at h
    exact h
  have hβ := p.β_T_mem.1
  have hA : p.β_T * (g * (dl * (s₀ - sα)))
      ≤ p.β_T * (Eq.V_T (Sanctions.clipS' (p.F x s₀)) - Eq.V_T (Sanctions.clipS' (p.F x sα))) :=
    mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hchord hg0).trans hsl) hβ
  have hB : 0 ≤ (s₀ - sα) * (p.β_T * dl * g - c) :=
    mul_nonneg (sub_nonneg.mpr hs) (by linarith)
  -- the stage: pain at most `c` per unit at full defiance, positive compliance costly
  have hp := hpain x hx sα hsαI s₀ hs₀I hs
  simp only at hp
  have hc := hcost x hx sα hsαI (Eq.α x) hαI hpos
  unfold Params.joint_T_top_integrand at hopt
  have hopt' : p.U_T x 0 s₀ + p.β_T * Eq.V_T (Sanctions.clipS' (p.F x s₀))
      ≤ p.U_T x (Eq.α x) sα + p.β_T * Eq.V_T (Sanctions.clipS' (p.F x sα)) := hopt
  nlinarith [hopt', hA, hB, hp, hc]

/-- **The Target defies at every state**, at every equilibrium of the
top-selector class whose realised rule is nondecreasing, under the unrefined
loss-offset margin and a positive compliance cost. No condition on the policy.
General in `F`.

Pinned headline (Rule 18): the statement is kept as it was. Since round BG
(2026-10-06) it is a corollary of `policy_eq_zero_of_rule_monotone_of_costSign`: a
per-unit cost `ℓ > 0` makes positive compliance strictly costly
(`strictCost_of_linearCost`), and decreasing differences over every pair of
compliance levels give them against full defiance (`DD0_of_decreasingDifferencesOn`).
The sign `0 ≤ d_lo` is no longer read, and since the closing round of the renovation
(2026-10-08, the author's decision; a Rule 18 re-pin) it is not a binder. -/
theorem policy_eq_zero_of_rule_monotone {gl dl c v ℓ : ℝ}
    (hband : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      gl * (y₂ - y₁) ≤ p.F y₂ s - p.F y₁ s)
    (hSlo : Sanctions.TransitionChords.SanctionLowerChord p.F dl)
    (hDD : ∀ x ∈ Icc (0 : ℝ) 1, Sanctions.MilgromShannon.DecreasingDifferencesOn
      Sanctions.I Sanctions.I (fun s a => p.U_S x a s))
    (hcost : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ a ∈ Icc (0 : ℝ) 1,
      ℓ * a ≤ p.U_T x 0 s - p.U_T x a s)
    (hℓ : 0 < ℓ)
    (hpain : ∀ x ∈ Icc (0 : ℝ) 1, LowerLossSlopeOn (fun s => p.U_T x 0 s) (Icc (0 : ℝ) 1) c)
    (hstate : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      v * (y₂ - y₁) ≤ p.U_T y₂ 0 s - p.U_T y₁ 0 s)
    (hv : 0 ≤ v)
    (hTM : c ≤ p.β_T * dl * p.defianceSlope gl v)
    (Eq : p.FeedbackStackelbergEquilibriumTop)
    (hrule : MonotoneOn (p.dynamicEquilibriumRule Eq) Sanctions.S)
    {x : ℝ} (hx : x ∈ Sanctions.I) : Eq.α x = 0 :=
  Eq.policy_eq_zero_of_rule_monotone_of_costSign hband hSlo
    (fun y hy => p.DD0_of_decreasingDifferencesOn (hDD y hy))
    (p.strictCost_of_linearCost hcost hℓ) hpain hstate hv hTM hrule hx

end FeedbackStackelbergEquilibriumTop

end

end Params
end AbstractGame
end Sanctions

-- The axiom report below names declarations in full; several names pass the
-- 100-character line limit, which is accepted for these report lines only.
set_option linter.style.longLine false

#print axioms Sanctions.AbstractGame.Params.lowerChords_add_le_one
#print axioms Sanctions.AbstractGame.Params.βT_mul_lowerChord_lt_one
#print axioms Sanctions.AbstractGame.Params.σ_dyn_top_le_zero_of_DD0
#print axioms Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.slopeDeficit_step
#print axioms Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.lowerSlope_of_rule_monotone
#print axioms Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone_of_costSign
#print axioms Sanctions.AbstractGame.Params.FeedbackStackelbergEquilibriumTop.policy_eq_zero_of_rule_monotone
