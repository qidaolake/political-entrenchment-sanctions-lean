/-
Sanctions/Examples/PlacableSenderEquilibrium.lean

**The chord economy, part two: the Sender's response on the carrier, the
Sender's constructed equilibrium value, and the Target side** (ported to
`ChordEconomy` in round AV, 2026-09-25, doc 104: both stage payoffs abstract;
through round AS these were the placable family's theorems over the quadratic
Sender cost and the linear Target payoff, which is now one instance,
`PlacableEconomyF.toChord`).

`ChordEconomy.lean` proves the Sender carrier Bellman-invariant at the defiance
policy and the Sender argmax unique on it. This file:

1. records what the Sender's realised response does on the carrier — it agrees
   with the top selector, it is antitone in compliance, it is **zero at full
   compliance** (placability), it dominates the stage response, and it is
   continuous in the state;
2. constructs the Sender's value `VSstar` against the candidate defiance policy
   as the Banach fixed point of the Sender Bellman operator on the carrier
   (Rule 15), and proves it unique there;
3. proves the **Sender channel active at that value**: at every state, no
   forward-looking maximiser is a stage maximiser. The chord step above the
   stage argmax `σ(x,0)` loses at most `(Q̄/2)ε²` — the quadratic lower support
   of a `Q̄`-semiconvex payoff at an interior maximiser, where the quadratic
   family lost exactly `(q/2)ε²` at its vertex;
4. on the Target side, proves **full defiance the strict unique Target argmax**
   at every pair of carrier values under the loss-offset margin, and that **the
   stage rewards full compliance** there under the endpoint stage flip
   `ℓ_hi < b·p_lo` (`b = σ(0,0)` the sanction floor), so the Target channel is
   active over the two carriers;
5. constructs the Target's equilibrium value and packages a
   `FeedbackStackelbergEquilibriumTop`, conditional on a monotone response;
   section 6 **discharges it** on the two-sided carrier given the rally margin
   `β_S(σ_C·g_hi·d_hi + (K_S + 2σ_C)·M_mix) ≤ r_lo` (at a flat transition and a
   Sender payoff convex in the state, `τ_x = M_cx = M_mix = 0`, it reads
   `0 ≤ r_lo`); section 7 adds that the response is Lipschitz in the state with
   the constant `L_resp/μ`. Both read the two-sided curvature data, so since
   renovation item BJ3.1 (2026-10-07) the two-sided carrier's value, the margin
   route and `L_resp` are stated on `ChordEconomyTwoSided`.

Every Target comparison moves one coordinate at a time through a mixed point
(`UT_sub_le`, `UT_sub_ge`, `UT_state_chord_ge`): no separability and no Target
curvature are read anywhere.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation item BH3.1 (2026-10-06): the Sender-channel results of section 3 and the
two-channel results read interiority only through its stage part `u_hi < q`
(`ChordEconomy.uhi_lt_q`), so they take that stage appetite as the binder `hS`. The
pinned `both_channels_active_of_margin` keeps `hInt` and is a corollary of
`both_channels_active_of_margin_stage`.
-/
import Sanctions.Examples.ChordEconomy
import Sanctions.Foundations.SemiconvexArgmaxShift
import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Theory.LockIn.ResponseStateMonotone
import Sanctions.Theory.LockIn.TwoSidedForwardLooking
import Sanctions.Theory.Equilibrium.BergeContinuity
import Sanctions.Theory.Equilibrium.StackelbergFeedback
import Sanctions.Theory.Bellman.BellmanT
import Sanctions.Theory.Basin.JointPreferenceBasin

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame Sanctions.Semiconcave
  Sanctions.TransitionChords

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 1. The Sender's realised response on the carrier -/

/-- The realised (forward-looking) Sender response. -/
def response (V : Val) (x a : ℝ) : ℝ := E.toParams.σ_dyn V x a

theorem response_mem (V : Val) (x a : ℝ) : E.response V x a ∈ Sanctions.I :=
  E.toParams.σ_dyn_mem V x a

/-- The Sender's dynamic objective at a value. -/
def senderObj (V : Val) (x a s : ℝ) : ℝ :=
  E.toParams.U_S x a s + E.toParams.β_S * V (Sanctions.clipS' (E.toParams.F x s))

theorem response_isMaxOn (V : Val) (x a : ℝ) :
    IsMaxOn (fun s => E.senderObj V x a s) Sanctions.I (E.response V x a) :=
  E.toParams.σ_dyn_isMaxOn V x a

/-- On the carrier the choice-based and top selectors agree. -/
theorem response_eq_top {V : Val} (hV : V ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I)
    (a : ℝ) : E.response V x a = E.toParams.σ_dyn_top V x a :=
  E.toParams.σ_dyn_eq_σ_dyn_top_of_unique V x a
    (fun s₁ s₂ hs₁ hs₂ h₁ h₂ => E.DAU_on_carrier hV x hx a s₁ s₂ hs₁ hs₂ h₁ h₂)

/-- Strict-form uniqueness: every non-argmax sanction is strictly worse. -/
theorem response_unique_strict {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) :
    ∀ a ∈ Sanctions.I, ∀ s ∈ Sanctions.I, s ≠ E.toParams.σ_dyn_top V x a →
      E.toParams.U_S x a s + E.toParams.β_S * V (Sanctions.clipS' (E.toParams.F x s))
        < E.toParams.U_S x a (E.toParams.σ_dyn_top V x a)
          + E.toParams.β_S * V (Sanctions.clipS' (E.toParams.F x (E.toParams.σ_dyn_top V x a))) := by
  intro a _ s hs hne
  have htop := E.toParams.σ_dyn_top_isMaxOn V x a
  have htop_mem := E.toParams.σ_dyn_top_mem_I V x a
  by_contra hcon
  push_neg at hcon
  have hs_max : IsMaxOn (fun s' => E.toParams.U_S x a s'
      + E.toParams.β_S * V (Sanctions.clipS' (E.toParams.F x s'))) Sanctions.I s := by
    intro t ht
    exact le_trans (htop ht) hcon
  exact hne (E.DAU_on_carrier hV x hx a s _ hs htop_mem hs_max htop)

/-- **The response is antitone in compliance** on the carrier: more compliance,
weakly less sanction. -/
theorem response_antitoneOn_a {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) :
    AntitoneOn (fun a => E.response V x a) Sanctions.I := by
  have h := E.toParams.σ_dyn_top_antitoneOn_a_of_SenderActionDD V x
    (E.stage_decreasingDifferences x hx) (E.response_unique_strict hV hx)
  intro a₁ ha₁ a₂ ha₂ hle
  show E.response V x a₂ ≤ E.response V x a₁
  rw [E.response_eq_top hV hx, E.response_eq_top hV hx]
  exact h ha₁ ha₂ hle

/-- **Placability: a fully compliant Target is not sanctioned.** At `a = 1`
the dynamic objective is strictly decreasing in the sanction, by placability (`hP`). -/
theorem response_at_one (hP : E.Placable) {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) : E.response V x 1 = 0 := by
  have hdec : ∀ s ∈ Sanctions.I, 0 < s →
      E.senderObj V x 1 s < E.senderObj V x 1 0 := by
    intro s hs hpos
    unfold senderObj
    have hF0 : E.F x 0 ∈ Icc (0:ℝ) 1 := E.F_mem _ _ hx ⟨le_refl 0, zero_le_one⟩
    have hFs : E.F x s ∈ Icc (0:ℝ) 1 := E.F_mem _ _ hx hs
    have hlip := E.clip_lip hV.1 _ hFs _ hF0
    have hchord : |E.F x s - E.F x 0| ≤ E.dhi * |s - 0| :=
      abs_sub_le_of_sanctionChords E.hdlo0.le E.hSlo E.hShi hx hs ⟨le_refl 0, zero_le_one⟩
    rw [sub_zero, abs_of_pos hpos] at hchord
    have hcont : V (Sanctions.clipS' (E.F x s)) - V (Sanctions.clipS' (E.F x 0))
        ≤ E.KS * (E.dhi * s) :=
      (le_abs_self _).trans (hlip.trans (mul_le_mul_of_nonneg_left hchord E.KS_pos.le))
    -- The stage: the appetite at defiance, then placation from `0` to `1`.
    have happ := E.hUS_appetite x hx 0 zero_mem_I s hs hs.1
    have hdd := E.hUS_placLo x hx 0 zero_mem_I 1 one_mem_I 0 zero_mem_I s hs zero_le_one hs.1
    have hP' : E.uhi + E.β_S * E.KS * E.dhi ≤ E.klo := hP
    have hq : 0 < E.q / 2 * s ^ 2 := mul_pos (by linarith [E.hq]) (pow_pos hpos 2)
    have hβ := E.hβS0
    nlinarith [mul_le_mul_of_nonneg_left hcont hβ.le, mul_le_mul_of_nonneg_left hP' hpos.le,
      happ, hdd, hq]
  by_contra hne
  have hpos : 0 < E.response V x 1 :=
    lt_of_le_of_ne (E.response_mem V x 1).1 (Ne.symm hne)
  have h1 := hdec _ (E.response_mem V x 1) hpos
  have h2 := E.response_isMaxOn V x 1 (show (0:ℝ) ∈ Sanctions.I from ⟨le_refl 0, zero_le_one⟩)
  exact absurd h2 (not_le.mpr h1)

/-- The continuation is monotone in the sanction on the carrier. -/
theorem senderContinuationMonotoneAt {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) : E.toParams.SenderContinuationMonotoneAt V x := by
  intro s₁ hs₁ s₂ hs₂ hle
  exact E.clip_mono hV.1 _ (E.F_mem _ _ hx hs₁) _ (E.F_mem _ _ hx hs₂) (E.F_mono_s x hle)

/-- **The forward-looking response dominates the stage response** (Rung 1,
weak form). -/
theorem response_ge_stage {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Sanctions.I) (a : ℝ) :
    E.toParams.σ x a ≤ E.response V x a := by
  rw [E.response_eq_top hV hx]
  exact E.toParams.sigma_dyn_top_ge_sigma_of_senderContinuationMonotoneAt V
    (E.senderContinuationMonotoneAt hV hx) a

/-! ## 2. The Sender's equilibrium value: a Banach fixed point on the carrier -/

instance carrierS_completeSpace : CompleteSpace E.carrierS :=
  E.carrierS_isClosed.completeSpace_coe

instance carrierS_nonempty_inst : Nonempty E.carrierS :=
  E.carrierS_nonempty.to_subtype

/-- The Sender Bellman operator at the defiance policy, restricted to the
carrier. -/
def senderOp : E.carrierS → E.carrierS :=
  fun V => ⟨E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V.1, E.bellmanS_mem V.2⟩

theorem senderOp_contracting : ContractingWith E.toParams.β_S_nnreal E.senderOp := by
  refine ⟨E.toParams.β_S_nnreal_lt_one, ?_⟩
  intro V W
  have h := (E.toParams.bellmanS_BCF_contracting (α := fun _ => 0) continuous_const).2 V.1 W.1
  simpa [senderOp, Subtype.edist_eq] using h

/-- **The Sender's value against the defiance policy**, constructed: the Banach
fixed point of the Sender Bellman operator at `α ≡ 0` on the carrier. It is the
Sender's *equilibrium* value once section 5 assembles the equilibrium whose
Target policy is that defiance (`equilibriumTop`); until then it is the fixed
point against a candidate policy (wording corrected 2026-09-11, the reader's
C17). -/
def VSstar : Val :=
  (ContractingWith.fixedPoint E.senderOp E.senderOp_contracting).1

theorem VSstar_mem : E.VSstar ∈ E.carrierS :=
  (ContractingWith.fixedPoint E.senderOp E.senderOp_contracting).2

theorem VSstar_fix :
    E.toParams.bellmanS_BCF (fun _ => 0) continuous_const E.VSstar = E.VSstar := by
  have h := ContractingWith.fixedPoint_isFixedPt E.senderOp_contracting
  have h' := congrArg Subtype.val h
  exact h'

/-- **Uniqueness in the carrier**: any carrier fixed point is `VSstar`. -/
theorem VSstar_unique {V : Val} (hV : V ∈ E.carrierS)
    (hfix : E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V = V) :
    V = E.VSstar := by
  have hfp : Function.IsFixedPt E.senderOp ⟨V, hV⟩ := Subtype.ext hfix
  have := E.senderOp_contracting.fixedPoint_unique hfp
  exact congrArg Subtype.val this

end ChordEconomy

/-! ### The two-sided carrier contains the equilibrium value (Rung 3)

On the two-sided extension since renovation item BJ3.1 (2026-10-07): the carrier
`carrierS2` reads the two-sided curvature data. General in `F`. -/

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

instance : Nonempty E.carrierS2 := E.carrierS2_nonempty.to_subtype
instance : CompleteSpace E.carrierS2 := E.carrierS2_isClosed.completeSpace_coe

/-- The Bellman operator restricted to the two-sided carrier. -/
def senderOp2 : E.carrierS2 → E.carrierS2 :=
  fun V => ⟨E.toParams.bellmanS_BCF (fun _ => 0) continuous_const V.1, E.bellmanS_mem2 V.2⟩

theorem senderOp2_contracting : ContractingWith E.toParams.β_S_nnreal E.senderOp2 := by
  refine ⟨E.toParams.β_S_nnreal_lt_one, ?_⟩
  intro V W
  have h := (E.toParams.bellmanS_BCF_contracting (α := fun _ => 0) continuous_const).2 V.1 W.1
  simpa [senderOp2, Subtype.edist_eq] using h

/-- **`VSstar` lies in the two-sided carrier**: that carrier is closed, nonempty
and invariant, so it has its own Banach fixed point, which is a carrier fixed
point and hence `VSstar` by uniqueness. -/
theorem VSstar_mem2 : E.VSstar ∈ E.carrierS2 := by
  obtain ⟨hfp, hfpfix⟩ : ∃ V : E.carrierS2, E.senderOp2 V = V :=
    ⟨_, ContractingWith.fixedPoint_isFixedPt E.senderOp2_contracting⟩
  have hfix : E.toParams.bellmanS_BCF (fun _ => 0) continuous_const hfp.1 = hfp.1 :=
    congrArg Subtype.val hfpfix
  have heq := E.VSstar_unique hfp.2.1 hfix
  rw [← heq]
  exact hfp.2

end ChordEconomyTwoSided

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 3. The Sender channel is active at the equilibrium value -/

/-- The stage argmax at defiance is interior: `0 < σ(x,0) < 1`. General in `F`;
under the stage appetite `u_hi < q` (BH3.1: until 2026-10-06 the stronger
interiority `A < q`, of which only `u_hi < q` is read). -/
theorem stage_argmax_mem_Ioo (hS : E.uhi < E.q) {x : ℝ} (hx : x ∈ Sanctions.I) :
    0 < E.σ x 0 ∧ E.σ x 0 < 1 := ⟨E.stage_argmax_pos hx, E.stage_argmax_lt_one hS hx⟩

/-- The step above the stage argmax at which the chord is verified. -/
def chordStep (x : ℝ) : ℝ := min (1 - E.σ x 0) (E.β_S * E.gS * E.dlo / E.Qbar)

/-- The chord step is positive. General in `F`; under the stage appetite `u_hi < q`
(BH3.1: the binder was interiority `A < q`, read only through `u_hi < q`). -/
theorem chordStep_pos (hS : E.uhi < E.q) {x : ℝ} (hx : x ∈ Sanctions.I) :
    0 < E.chordStep x := by
  unfold chordStep
  apply lt_min
  · linarith [E.stage_argmax_lt_one hS hx]
  · exact div_pos (mul_pos (mul_pos E.hβS0 E.gS_pos) E.hdlo0) E.Qbar_pos

/-- **The Sender channel is active** at every carrier value and every state:
no forward-looking maximiser is a stage maximiser (Rung 1's strict theorem,
with the chord verified one `chordStep` above the vertex). General in `F`. It
needs only the stage appetite `u_hi < q`, which keeps the stage vertex below one
so that there is room to sanction more (BH3.1, 2026-10-06: the binder was
interiority `A < q`; the dynamic part `β_S·K_S·d_hi` of the appetite is not read). -/
theorem sender_channel_active_on_carrier (hS : E.uhi < E.q) {V : Val} (hV : V ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toParams.ContinuationChangesSenderChoiceAt V x 0 := by
  intro sD hsD hdyn hstage
  -- The stage maximiser is the stage selector.
  have hsD_eq : sD = E.σ x 0 := E.stage_argmax_eq hx 0 hsD hstage
  set v := E.σ x 0 with hv_def
  have hv0 : 0 < v := E.stage_argmax_pos hx
  have hv1 : v < 1 := E.stage_argmax_lt_one hS hx
  have hvmem : v ∈ Sanctions.I := ⟨hv0.le, hv1.le⟩
  -- The chord point.
  set ε := E.chordStep x with hε
  have hε_pos : 0 < ε := E.chordStep_pos hS hx
  have hε_le1 : ε ≤ 1 - v := min_le_left _ _
  have hε_le2 : ε ≤ E.β_S * E.gS * E.dlo / E.Qbar := min_le_right _ _
  have hs'_mem : v + ε ∈ Sanctions.I := ⟨by linarith, by linarith⟩
  -- Wedge strictly increasing.
  have hwedge : ∀ s₁ ∈ Sanctions.I, ∀ s₂ ∈ Sanctions.I, s₁ < s₂ →
      E.toParams.senderSanctionContinuation V x s₁
        < E.toParams.senderSanctionContinuation V x s₂ :=
    E.toParams.senderSanctionContinuation_strictMono_of_separated_primitives V hx
      (fun s₁ hs₁ s₂ hs₂ hlt => by
        have := E.hSlo hx hs₁ hs₂ hlt.le
        have : 0 < E.dlo * (s₂ - s₁) := mul_pos E.hdlo0 (by linarith)
        linarith)
      (fun y₁ hy₁ y₂ hy₂ hlt => E.clip_strictMono hV.1 y₁ hy₁ y₂ hy₂ hlt)
  -- The chord: the stage loses at most `(Q̄/2)ε²` (the quadratic support of a
  -- `Q̄`-semiconvex payoff at its interior maximiser), the wedge gains at least
  -- `g_S·dlo·ε`, and `ε ≤ β_S·g_S·dlo/Q̄` makes the loss strictly smaller.
  have hchord : E.toParams.U_S x 0 v - E.toParams.U_S x 0 (v + ε)
      < E.toParams.β_S * (E.toParams.senderSanctionContinuation V x (v + ε)
          - E.toParams.senderSanctionContinuation V x v) := by
    have hsup : E.U_S x 0 v - E.Qbar / 2 * (v + ε - v) ^ 2 ≤ E.U_S x 0 (v + ε) :=
      Sanctions.SemiconvexArgmaxShift.quadratic_support_right_of_semiconvex_interior_max
        E.Qbar_pos (E.hUS_convex x hx 0 zero_mem_I) (E.σ_isMaxOn_U_S x 0) hv0
        (y := v + ε) (by linarith) hs'_mem.2
    have hloss : E.toParams.U_S x 0 v - E.toParams.U_S x 0 (v + ε) ≤ E.Qbar / 2 * ε ^ 2 := by
      have he : v + ε - v = ε := by ring
      rw [he] at hsup
      change E.U_S x 0 v - E.U_S x 0 (v + ε) ≤ E.Qbar / 2 * ε ^ 2
      linarith
    have hFle : E.F x v ≤ E.F x (v + ε) := E.F_mono_s x (by linarith)
    have hFchord : E.dlo * ε ≤ E.F x (v + ε) - E.F x v := by
      have := E.hSlo hx hvmem hs'_mem (by linarith)
      simpa using this
    have hF1 : E.F x v ∈ Icc (0:ℝ) 1 := E.F_mem _ _ hx hvmem
    have hF2 : E.F x (v + ε) ∈ Icc (0:ℝ) 1 := E.F_mem _ _ hx hs'_mem
    have hgain : E.gS * (E.F x (v + ε) - E.F x v)
        ≤ E.toParams.senderSanctionContinuation V x (v + ε)
          - E.toParams.senderSanctionContinuation V x v := by
      unfold AbstractGame.Params.senderSanctionContinuation
      exact E.clip_lowerSlope hV.1 _ hF1 _ hF2 hFle
    have hgain' : E.gS * (E.dlo * ε)
        ≤ E.toParams.senderSanctionContinuation V x (v + ε)
          - E.toParams.senderSanctionContinuation V x v :=
      (mul_le_mul_of_nonneg_left hFchord E.gS_pos.le).trans hgain
    have hkey : E.Qbar / 2 * ε ^ 2 < E.β_S * (E.gS * (E.dlo * ε)) := by
      have h1 : E.Qbar * ε ≤ E.β_S * E.gS * E.dlo := by
        calc E.Qbar * ε ≤ E.Qbar * (E.β_S * E.gS * E.dlo / E.Qbar) :=
              mul_le_mul_of_nonneg_left hε_le2 E.Qbar_pos.le
          _ = E.β_S * E.gS * E.dlo := by field_simp [E.Qbar_pos.ne']
      have h2 : 0 < E.β_S * E.gS * E.dlo := mul_pos (mul_pos E.hβS0 E.gS_pos) E.hdlo0
      nlinarith [mul_le_mul_of_nonneg_left h1 hε_pos.le, h2, hε_pos]
    have hg2 := mul_le_mul_of_nonneg_left hgain' E.hβS0.le
    change E.U_S x 0 v - E.U_S x 0 (v + ε)
      < E.β_S * (E.toParams.senderSanctionContinuation V x (v + ε)
          - E.toParams.senderSanctionContinuation V x v)
    change E.U_S x 0 v - E.U_S x 0 (v + ε) ≤ E.Qbar / 2 * ε ^ 2 at hloss
    linarith
  -- Rung 1: the forward-looking maximiser is strictly above the stage one.
  have hlt := E.toParams.sender_dynamic_sanctions_gt_myopic_at_same_action V
    (x := x) (a := 0) (sM := sD) (sD := sD) (s' := v + ε)
    hsD hsD hs'_mem hstage (by
      have h := hdyn
      unfold AbstractGame.Params.senderSanctionContinuation
      exact h)
    E.hβS0 hwedge (by rw [hsD_eq]; exact hchord)
  exact lt_irrefl _ hlt

/-- **The Sender channel is active at the constructed equilibrium value**, at
every state. General in `F`; under the stage appetite `u_hi < q` (BH3.1: the
binder was interiority `A < q`). -/
theorem sender_channel_active (hS : E.uhi < E.q) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toParams.ContinuationChangesSenderChoiceAt E.VSstar x 0 :=
  E.sender_channel_active_on_carrier hS E.VSstar_mem hx

/-! ## 4. The Target side: defiance is the unique leader argmax, and the stage
disagrees -/

/-- `M_T = 2·M_T₀/(1 − β_T)`, the Target carrier's sup-norm radius (`M_T₀` the
supremum of `|U_T|` over the cube, sign-off M1). -/
def MT : ℝ := 2 * E.MT₀ / (1 - E.β_T)

theorem MT_nonneg : 0 ≤ E.MT :=
  div_nonneg (by linarith [E.MT₀_nonneg]) (by linarith [E.hβT1])

/-- The floor-refined state rate is bounded by the payoff's range. -/
theorem gT_num_le : E.vlo + E.nlo * E.sfloor ≤ 2 * E.MT₀ := by
  have h1 := E.hUT_stateLo 0 zero_mem_I E.sfloor E.sfloor_mem 0 zero_mem_I 1 one_mem_I
    zero_le_one
  simp only [sub_zero, mul_one] at h1
  have h2 := E.abs_U_T_le_MT₀ one_mem_I zero_mem_I E.sfloor_mem
  have h3 := E.abs_U_T_le_MT₀ zero_mem_I zero_mem_I E.sfloor_mem
  linarith [le_abs_self (E.U_T 1 0 E.sfloor), neg_abs_le (E.U_T 0 0 E.sfloor)]

theorem gT_le_MT : E.gT ≤ E.MT := by
  unfold gT MT
  have h1 : 0 < 1 - E.β_T * E.glo := by linarith [E.βT_glo_lt_one]
  have h2 : 0 < 1 - E.β_T := by linarith [E.hβT1]
  rw [div_le_div_iff₀ h1 h2]
  have hglo1 : E.glo ≤ 1 := E.hglo_ghi.trans E.hghi1
  have h3 := E.gT_num_le
  have h4 : 1 - E.β_T ≤ 1 - E.β_T * E.glo := by
    have := mul_le_mul_of_nonneg_left hglo1 E.hβT0.le
    linarith
  have hnum : 0 ≤ E.vlo + E.nlo * E.sfloor := by
    have := mul_nonneg E.hnlo E.sfloor_mem.1; linarith [E.hvlo]
  have h5 : (E.vlo + E.nlo * E.sfloor) * (1 - E.β_T)
      ≤ (E.vlo + E.nlo * E.sfloor) * (1 - E.β_T * E.glo) :=
    mul_le_mul_of_nonneg_left h4 hnum
  have h6 : (E.vlo + E.nlo * E.sfloor) * (1 - E.β_T * E.glo)
      ≤ 2 * E.MT₀ * (1 - E.β_T * E.glo) :=
    mul_le_mul_of_nonneg_right h3 h1.le
  linarith

/-- **The Target carrier**: bounded, with lower state-slope `g_T` on `[0,1]`. No
Lipschitz clause: under a monotone response none is needed. -/
def carrierT : Set Val :=
  {V : Val | ‖V‖ ≤ E.MT ∧
    AbstractGame.Params.LowerSlopeOnValueOn V (Icc (0 : ℝ) 1) E.gT}

theorem carrierT_isClosed : IsClosed E.carrierT := by
  unfold carrierT
  exact IsClosed.inter (isClosed_le continuous_norm continuous_const)
    (AbstractGame.Params.lowerSlopeOnValueOn_isClosed _ _)

theorem carrierT_nonempty : E.carrierT.Nonempty := by
  have h := SymbolicEconomyF.affineBCF_mem_gainBall_cone E.gT_pos.le (le_refl E.gT) E.gT_le_MT
  exact ⟨affineBCF E.gT, h.1, h.2.2⟩

/-- Lower slope through the clip on the Target carrier. -/
theorem clipT_lowerSlope {V : Val} (hV : V ∈ E.carrierT) :
    ∀ z₁ ∈ Icc (0 : ℝ) 1, ∀ z₂ ∈ Icc (0 : ℝ) 1, z₁ ≤ z₂ →
      E.gT * (z₂ - z₁) ≤ V (Sanctions.clipS' z₂) - V (Sanctions.clipS' z₁) := by
  intro z₁ hz₁ z₂ hz₂ hle
  have h := hV.2 (Sanctions.clipS' z₁) (Sanctions.clipS' z₂)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₁]; exact hz₁)
    (by rw [Sanctions.clipS'_val_eq_of_mem hz₂]; exact hz₂)
    (Sanctions.clipS'_mono hle)
  have hdist : dist (Sanctions.clipS' z₁) (Sanctions.clipS' z₂) = z₂ - z₁ := by
    rw [Subtype.dist_eq, Real.dist_eq, Sanctions.clipS'_val_eq_of_mem hz₁,
        Sanctions.clipS'_val_eq_of_mem hz₂, abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hdist] at h
  exact h

/-- The joint Target integrand, unfolded at the response. -/
theorem joint_T_integrand_eq (V_T V_S : Val) (x a : ℝ) :
    E.toParams.joint_T_integrand V_T V_S x a
      = E.toParams.U_T x a (E.response V_S x a)
        + E.toParams.β_T * V_T (Sanctions.clipS' (E.toParams.F x (E.response V_S x a))) := rfl

/-- **Full defiance is the strict unique Target argmax** at every carrier pair:
more compliance buys less sanction, but the discounted continuation gain of the
higher state that sanction would have produced exceeds the sanction's pain
(`hTM`, the loss-offset margin), and compliance costs `ℓ` on top. -/
theorem targetObj_strictAntiOn (hTM : E.LossOffset) {V_T : Val} (hV_T : V_T ∈ E.carrierT)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I) :
    StrictAntiOn (fun a => E.toParams.joint_T_integrand V_T V_S x a) Sanctions.I := by
  intro a₁ ha₁ a₂ ha₂ hlt
  show E.toParams.joint_T_integrand V_T V_S x a₂ < E.toParams.joint_T_integrand V_T V_S x a₁
  rw [joint_T_integrand_eq, joint_T_integrand_eq]
  have hρ : E.response V_S x a₂ ≤ E.response V_S x a₁ :=
    E.response_antitoneOn_a hV_S hx ha₁ ha₂ hlt.le
  have hρ₁ := E.response_mem V_S x a₁
  have hρ₂ := E.response_mem V_S x a₂
  have hz : E.F x (E.response V_S x a₂) ≤ E.F x (E.response V_S x a₁) := E.F_mono_s x hρ
  have hchord : E.dlo * (E.response V_S x a₁ - E.response V_S x a₂)
      ≤ E.F x (E.response V_S x a₁) - E.F x (E.response V_S x a₂) := E.hSlo hx hρ₂ hρ₁ hρ
  have hslope := E.clipT_lowerSlope hV_T _ (E.F_mem _ _ hx hρ₂) _ (E.F_mem _ _ hx hρ₁) hz
  have hTM : E.c ≤ E.β_T * E.dlo * E.gT := hTM
  have hgT := E.gT_pos
  have hA : E.β_T * (V_T (Sanctions.clipS' (E.F x (E.response V_S x a₂)))
        - V_T (Sanctions.clipS' (E.F x (E.response V_S x a₁))))
      ≤ -(E.β_T * E.dlo * E.gT) * (E.response V_S x a₁ - E.response V_S x a₂) := by
    have h1 := mul_le_mul_of_nonneg_left hchord (mul_nonneg E.hβT0.le hgT.le)
    have h2 := mul_le_mul_of_nonneg_left hslope E.hβT0.le
    nlinarith [h1, h2]
  have hB : (E.response V_S x a₁ - E.response V_S x a₂) * (E.c - E.β_T * E.dlo * E.gT) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hρ) (by linarith)
  -- The stage: `T2` at the lower sanction, `T4` at the lower compliance.
  have hU := E.UT_sub_le hx ha₁ ha₂ hρ₁ hρ₂ hlt.le hρ
  have hD : 0 < E.ℓlo * (a₂ - a₁) := mul_pos E.hℓlo (by linarith)
  nlinarith [hA, hB, hU, hD]

theorem zero_isMaxOn_joint (hTM : E.LossOffset) {V_T : Val} (hV_T : V_T ∈ E.carrierT)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I) :
    IsMaxOn (fun a => E.toParams.joint_T_integrand V_T V_S x a) Sanctions.I 0 := by
  rw [isMaxOn_iff]
  intro a ha
  rcases eq_or_lt_of_le ha.1 with h0 | hpos
  · rw [← h0]
  · exact (E.targetObj_strictAntiOn hTM hV_T hV_S hx ⟨le_refl 0, zero_le_one⟩ ha hpos).le

/-- Every joint Target maximiser at a carrier pair is full defiance. -/
theorem targetArgmax_eq_zero (hTM : E.LossOffset) {V_T : Val} (hV_T : V_T ∈ E.carrierT)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a : ℝ} (ha : a ∈ Sanctions.I)
    (hmax : IsMaxOn (fun b => E.toParams.joint_T_integrand V_T V_S x b) Sanctions.I a) :
    a = 0 := by
  by_contra hne
  have hpos : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm hne)
  have h1 := E.targetObj_strictAntiOn hTM hV_T hV_S hx ⟨le_refl 0, zero_le_one⟩ ha hpos
  have h2 := hmax (show (0:ℝ) ∈ Sanctions.I from ⟨le_refl 0, zero_le_one⟩)
  exact absurd h2 (not_le.mpr h1)

end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The stage flip.** Under the endpoint comparison `ℓ_hi < b·p_lo` — full
compliance costs at most `ℓ_hi`, and the relief it buys, at least the sanction
floor `b = σ(0,0)`, is worth at least `p_lo` per unit — at the stage, sanction
response included and future excluded, full compliance strictly beats full
defiance: the placable Sender drops the sanction to zero. On the quadratic
family it is `ℓq < u₀(c − n)`. -/
theorem targetStage_one_gt_zero (hP : E.Placable) (hflip : E.ℓhi < E.sfloor * E.plo)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toParams.U_T x 0 (E.response V_S x 0) < E.toParams.U_T x 1 (E.response V_S x 1) := by
  rw [E.response_at_one hP hV_S hx]
  have hρ₀ : E.sfloor ≤ E.response V_S x 0 :=
    (E.sfloor_le hx).trans (E.response_ge_stage hV_S hx 0)
  have hρmem := E.response_mem V_S x 0
  have hU := E.UT_sub_ge hx zero_mem_I one_mem_I hρmem zero_mem_I zero_le_one hρmem.1
  have h1 : E.sfloor * E.plo ≤ E.response V_S x 0 * E.plo :=
    mul_le_mul_of_nonneg_right hρ₀ E.hplo.le
  change E.U_T x 0 (E.response V_S x 0) < E.U_T x 1 0
  nlinarith [hU, h1, hflip]

/-- **The Target channel is active** at every carrier pair and every state,
under the stage flip: no forward-looking Target maximiser is a stage maximiser.
The forward-looking maximiser is full defiance; at the stage, full compliance
beats it. (On the enriched subclass under (RL) the same conclusion holds with
no flip, through a small compliance rather than full compliance:
`ChordEconomyCs.target_channel_active_of_relief`.) -/
theorem target_channel_active_on_carriers (hTM : E.LossOffset) (hP : E.Placable)
    (hflip : E.ℓhi < E.sfloor * E.plo)
    {V_T : Val} (hV_T : V_T ∈ E.carrierT)
    {V_S : Val} (hV_S : V_S ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.I) :
    E.toParams.ContinuationChangesTargetChoiceAt (fun y b => E.response V_S y b) V_T x := by
  intro a ha hdyn hstage
  have hdyn' : IsMaxOn (fun b => E.toParams.joint_T_integrand V_T V_S x b) Sanctions.I a :=
    hdyn
  have ha0 : a = 0 := E.targetArgmax_eq_zero hTM hV_T hV_S hx ha hdyn'
  subst ha0
  have h := hstage (show (1:ℝ) ∈ Sanctions.I from ⟨zero_le_one, le_refl 1⟩)
  exact absurd h (not_le.mpr (E.targetStage_one_gt_zero hP hflip hV_S hx))

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 5. The Target's equilibrium value and the composed equilibrium,
conditional on a monotone response -/

/-- The realised response at defiance, as a function of the state. -/
def responsePath (V_S : Val) (y : ℝ) : ℝ := E.response V_S y 0

theorem responsePath_mem (V_S : Val) (y : ℝ) : E.responsePath V_S y ∈ Sanctions.I :=
  E.response_mem V_S y 0

/-- The response is continuous in the state on the carrier (Berge, restricted
to the state set under state-local uniqueness). -/
theorem responsePath_continuousOn {V_S : Val} (hV_S : V_S ∈ E.carrierS) :
    ContinuousOn (E.responsePath V_S) (Sanctions.S : Set ℝ) := by
  have h := E.toParams.σ_dyn_continuousOn_S_of_unique_on V_S
    (fun x hx a s₁ s₂ hs₁ hs₂ h₁ h₂ => E.DAU_on_carrier hV_S x hx a s₁ s₂ hs₁ hs₂ h₁ h₂)
  have hmap : Set.MapsTo (fun x : ℝ => (x, (0 : ℝ))) (Sanctions.S : Set ℝ)
      ((Sanctions.S : Set ℝ) ×ˢ (Set.univ : Set ℝ)) :=
    fun x hx => ⟨hx, Set.mem_univ _⟩
  have hc := h.comp (continuous_id.prodMk continuous_const).continuousOn hmap
  exact hc.congr (fun x _ => rfl)

/-- **The Target Bellman operator** at the realised response of a carrier
Sender value. -/
def targetOp {V_S : Val} (hV_S : V_S ∈ E.carrierS) (V_T : Val) : Val :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y : ↥(Sanctions.S : Set ℝ) =>
        E.toParams.U_T y.val 0 (E.responsePath V_S y.val)
          + E.toParams.β_T
              * V_T (Sanctions.clipS' (E.toParams.F y.val (E.responsePath V_S y.val))),
     by
       have hρ : Continuous (fun y : ↥(Sanctions.S : Set ℝ) => E.responsePath V_S y.val) :=
         continuousOn_iff_continuous_restrict.mp (E.responsePath_continuousOn hV_S)
       have hU : Continuous (fun y : ↥(Sanctions.S : Set ℝ) =>
           E.toParams.U_T y.val 0 (E.responsePath V_S y.val)) :=
         E.toParams.U_T_continuous.comp
           (continuous_subtype_val.prodMk (continuous_const.prodMk hρ))
       have hF : Continuous (fun y : ↥(Sanctions.S : Set ℝ) =>
           E.toParams.F y.val (E.responsePath V_S y.val)) :=
         E.toParams.F_continuous.comp (continuous_subtype_val.prodMk hρ)
       exact hU.add (continuous_const.mul
         (V_T.continuous.comp (Sanctions.clipS'_continuous.comp hF)))⟩

theorem targetOp_apply {V_S : Val} (hV_S : V_S ∈ E.carrierS) (V_T : Val)
    (y : ↥(Sanctions.S : Set ℝ)) :
    E.targetOp hV_S V_T y
      = E.toParams.U_T y.val 0 (E.responsePath V_S y.val)
        + E.toParams.β_T
            * V_T (Sanctions.clipS' (E.toParams.F y.val (E.responsePath V_S y.val))) := rfl

theorem targetOp_contracting {V_S : Val} (hV_S : V_S ∈ E.carrierS) :
    ContractingWith E.toParams.β_T_nnreal (E.targetOp hV_S) := by
  refine ⟨E.toParams.β_T_nnreal_lt_one, ?_⟩
  apply lipschitzWith_of_pointwise_dist_le
  intro V W y
  rw [targetOp_apply, targetOp_apply, Real.dist_eq]
  have hβ : (0:ℝ) ≤ E.toParams.β_T := E.toParams.β_T_mem.1
  have h1 : |(E.toParams.U_T y.val 0 (E.responsePath V_S y.val)
        + E.toParams.β_T * V (Sanctions.clipS' (E.toParams.F y.val (E.responsePath V_S y.val))))
      - (E.toParams.U_T y.val 0 (E.responsePath V_S y.val)
        + E.toParams.β_T * W (Sanctions.clipS' (E.toParams.F y.val (E.responsePath V_S y.val))))|
      = E.toParams.β_T * |V (Sanctions.clipS' (E.toParams.F y.val (E.responsePath V_S y.val)))
          - W (Sanctions.clipS' (E.toParams.F y.val (E.responsePath V_S y.val)))| := by
    rw [show ∀ a b c : ℝ, (a + E.toParams.β_T * b) - (a + E.toParams.β_T * c)
        = E.toParams.β_T * (b - c) from fun a b c => by ring, abs_mul, abs_of_nonneg hβ]
  rw [h1]
  have h2 := BoundedContinuousFunction.dist_coe_le_dist (f := V) (g := W)
    (Sanctions.clipS' (E.toParams.F y.val (E.responsePath V_S y.val)))
  rw [Real.dist_eq] at h2
  have := mul_le_mul_of_nonneg_left h2 hβ
  convert this using 2

/-- **The response at defiance is never below the sanction floor** `b = σ(0,0)`:
it dominates the stage response (`response_ge_stage`), which is nondecreasing in
the state (`stage_argmax_mono`). On the quadratic family `b = u₀/q`. -/
theorem responsePath_ge_sfloor {V_S : Val} (hV_S : V_S ∈ E.carrierS) {y : ℝ}
    (hy : y ∈ Sanctions.I) : E.sfloor ≤ E.responsePath V_S y :=
  (E.sfloor_le hy).trans (E.response_ge_stage hV_S hy 0)

/-- **The Target carrier is invariant under the Target operator whenever the
response is monotone in the state.** Norm leg: the stage payoff at defiance is
bounded by `c + v`. Slope leg: a rise in the state raises the stage payoff by
at least `v + n·u₀/q` per unit (the rally term `n·ρ` at the response floor
`u₀/q`, `responsePath_ge_b` — round J), and the realised successor by at least
`glo` per unit plus `dlo` per unit of the response's rise; by the loss-offset margin `hTM` that
rise is a net gain, so the image's slope is at least
`v + n·u₀/q + β_T·g_T·glo = g_T`. -/
theorem targetOp_mem_of_monotone (hTM : E.LossOffset) {V_S : Val} (hV_S : V_S ∈ E.carrierS)
    (hmono : MonotoneOn (E.responsePath V_S) (Icc (0 : ℝ) 1))
    {V_T : Val} (hV_T : V_T ∈ E.carrierT) :
    E.targetOp hV_S V_T ∈ E.carrierT := by
  have hβ : (0:ℝ) ≤ E.β_T := E.hβT0.le
  refine ⟨?_, ?_⟩
  · -- Norm leg.
    rw [BoundedContinuousFunction.norm_le E.MT_nonneg]
    intro y
    rw [targetOp_apply, Real.norm_eq_abs]
    have hVb : |V_T (Sanctions.clipS' (E.toParams.F y.val (E.responsePath V_S y.val)))| ≤ E.MT := by
      have h := BoundedContinuousFunction.norm_coe_le_norm V_T
        (Sanctions.clipS' (E.toParams.F y.val (E.responsePath V_S y.val)))
      rw [Real.norm_eq_abs] at h
      exact h.trans hV_T.1
    have hρ := E.responsePath_mem V_S y.val
    have hy := y.property
    have hU : |E.toParams.U_T y.val 0 (E.responsePath V_S y.val)| ≤ E.MT₀ :=
      E.abs_U_T_le_MT₀ hy zero_mem_I hρ
    have hMT : E.MT₀ + E.β_T * E.MT ≤ E.MT := by
      unfold MT
      have h2 : 0 < 1 - E.β_T := by linarith [E.hβT1]
      have h2' : (1 - E.β_T) ≠ 0 := h2.ne'
      have hid : E.MT₀ + E.β_T * (2 * E.MT₀ / (1 - E.β_T))
          = E.MT₀ * (1 + E.β_T) / (1 - E.β_T) := by field_simp; ring
      rw [hid]
      apply div_le_div_of_nonneg_right _ h2.le
      nlinarith [E.MT₀_nonneg, E.hβT1]
    calc |E.toParams.U_T y.val 0 (E.responsePath V_S y.val)
          + E.β_T * V_T (Sanctions.clipS' (E.toParams.F y.val (E.responsePath V_S y.val)))|
        ≤ |E.toParams.U_T y.val 0 (E.responsePath V_S y.val)|
          + |E.β_T * V_T (Sanctions.clipS' (E.toParams.F y.val (E.responsePath V_S y.val)))| :=
          abs_add_le _ _
      _ ≤ E.MT₀ + E.β_T * E.MT := by
          rw [abs_mul, abs_of_nonneg hβ]
          exact add_le_add hU (mul_le_mul_of_nonneg_left hVb hβ)
      _ ≤ E.MT := hMT
  · -- Slope leg.
    intro y₁ y₂ hy₁ hy₂ hle
    rw [targetOp_apply, targetOp_apply]
    have hyle : y₁.val ≤ y₂.val := hle
    have hd : dist y₁ y₂ = y₂.val - y₁.val := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hd]
    have hρ : E.responsePath V_S y₁.val ≤ E.responsePath V_S y₂.val := hmono hy₁ hy₂ hyle
    have hρ₁ := E.responsePath_mem V_S y₁.val
    have hρ₂ := E.responsePath_mem V_S y₂.val
    have hz₁ : E.F y₁.val (E.responsePath V_S y₁.val) ≤ E.F y₁.val (E.responsePath V_S y₂.val) :=
      E.F_mono_s _ hρ
    have hz₂ : E.F y₁.val (E.responsePath V_S y₂.val) ≤ E.F y₂.val (E.responsePath V_S y₂.val) :=
      E.F_mono_x _ hyle
    have hband := (E.hbandAll _ hρ₂) y₁.val hy₁ y₂.val hy₂ hyle
    have hchord := E.hSlo hy₁ hρ₁ hρ₂ hρ
    have hslope := E.clipT_lowerSlope hV_T _ (E.F_mem _ _ hy₁ hρ₁) _ (E.F_mem _ _ hy₂ hρ₂)
      (hz₁.trans hz₂)
    have hTM : E.c ≤ E.β_T * E.dlo * E.gT := hTM
    have hgT : E.gT * (1 - E.β_T * E.glo) * (y₂.val - y₁.val)
        = (E.vlo + E.nlo * E.sfloor) * (y₂.val - y₁.val) := by rw [E.gT_mul]
    have hgT0 := E.gT_pos
    -- The successor rises by at least `glo·Δy + dlo·Δρ`.
    have hsucc : E.glo * (y₂.val - y₁.val)
          + E.dlo * (E.responsePath V_S y₂.val - E.responsePath V_S y₁.val)
        ≤ E.F y₂.val (E.responsePath V_S y₂.val) - E.F y₁.val (E.responsePath V_S y₁.val) := by
      linarith [hband.1, hchord]
    have hA : E.β_T * E.gT * (E.glo * (y₂.val - y₁.val)
          + E.dlo * (E.responsePath V_S y₂.val - E.responsePath V_S y₁.val))
        ≤ E.β_T * (V_T (Sanctions.clipS' (E.F y₂.val (E.responsePath V_S y₂.val)))
          - V_T (Sanctions.clipS' (E.F y₁.val (E.responsePath V_S y₁.val)))) := by
      have h1 := mul_le_mul_of_nonneg_left hsucc (mul_nonneg hβ hgT0.le)
      have h2 := mul_le_mul_of_nonneg_left hslope hβ
      nlinarith [h1, h2]
    have hC : 0 ≤ (E.responsePath V_S y₂.val - E.responsePath V_S y₁.val)
        * (E.β_T * E.dlo * E.gT - E.c) :=
      mul_nonneg (sub_nonneg.mpr hρ) (by linarith)
    -- The stage: the state rate `v_lo + n_lo·ρ₁` at the lower sanction, which the
    -- floor `ρ₁ ≥ b` puts at least at `v_lo + n_lo·b`; then the pain `c`.
    have hUst := E.UT_state_chord_ge hy₁ hy₂ zero_mem_I hρ₁ hρ₂ hyle hρ
    have hE : E.sfloor * (E.nlo * (y₂.val - y₁.val))
        ≤ E.responsePath V_S y₁.val * (E.nlo * (y₂.val - y₁.val)) :=
      mul_le_mul_of_nonneg_right (E.responsePath_ge_sfloor hV_S hy₁)
        (mul_nonneg E.hnlo (by linarith))
    change E.gT * (y₂.val - y₁.val)
      ≤ (E.U_T y₂.val 0 (E.responsePath V_S y₂.val)
          + E.β_T * V_T (Sanctions.clipS' (E.F y₂.val (E.responsePath V_S y₂.val))))
        - (E.U_T y₁.val 0 (E.responsePath V_S y₁.val)
          + E.β_T * V_T (Sanctions.clipS' (E.F y₁.val (E.responsePath V_S y₁.val))))
    nlinarith [hA, hC, hUst, hE, hgT]

instance carrierT_completeSpace : CompleteSpace E.carrierT :=
  E.carrierT_isClosed.completeSpace_coe

instance carrierT_nonempty_inst : Nonempty E.carrierT :=
  E.carrierT_nonempty.to_subtype

/-- The Target operator at the Sender's equilibrium value, restricted to the
Target carrier — under a monotone response. -/
def targetOpSub (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    E.carrierT → E.carrierT :=
  fun V => ⟨E.targetOp E.VSstar_mem V.1, E.targetOp_mem_of_monotone hTM E.VSstar_mem hmono V.2⟩

theorem targetOpSub_contracting
    (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    ContractingWith E.toParams.β_T_nnreal (E.targetOpSub hTM hmono) := by
  refine ⟨E.toParams.β_T_nnreal_lt_one, ?_⟩
  intro V W
  have h := (E.targetOp_contracting E.VSstar_mem).2 V.1 W.1
  simpa [targetOpSub, Subtype.edist_eq] using h

/-- **The Target's equilibrium value**, constructed under a monotone response. -/
def VTstar (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) : Val :=
  (ContractingWith.fixedPoint (E.targetOpSub hTM hmono) (E.targetOpSub_contracting hTM hmono)).1

theorem VTstar_mem (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    E.VTstar hTM hmono ∈ E.carrierT :=
  (ContractingWith.fixedPoint (E.targetOpSub hTM hmono) (E.targetOpSub_contracting hTM hmono)).2

theorem VTstar_fix (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    E.targetOp E.VSstar_mem (E.VTstar hTM hmono) = E.VTstar hTM hmono := by
  have h := ContractingWith.fixedPoint_isFixedPt (E.targetOpSub_contracting hTM hmono)
  exact congrArg Subtype.val h

/-- On the carrier the top integrand is the joint integrand. -/
theorem joint_T_top_integrand_eq {V_S : Val} (hV_S : V_S ∈ E.carrierS) (V_T : Val)
    {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    E.toParams.joint_T_top_integrand V_T V_S x a = E.toParams.joint_T_integrand V_T V_S x a := by
  unfold AbstractGame.Params.joint_T_top_integrand AbstractGame.Params.joint_T_integrand
  rw [← E.response_eq_top hV_S hx a]
  rfl

/-- **The composed feedback Stackelberg equilibrium (top form), conditional on
a monotone response.** Sender value constructed on the Sender carrier; Target
value constructed on the Target carrier; the leader policy is full defiance,
derived as the strict unique argmax at every feasible state. -/
def equilibriumTop (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    E.toParams.FeedbackStackelbergEquilibriumTop where
  V_T := E.VTstar hTM hmono
  V_S := E.VSstar
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_refl 0, zero_le_one⟩
  V_S_fix := E.VSstar_fix.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest
        ((fun a => E.toParams.joint_T_top_integrand (E.VTstar hTM hmono) E.VSstar y.val a) '' Sanctions.I)
        (E.toParams.joint_T_top_integrand (E.VTstar hTM hmono) E.VSstar y.val 0) := by
      refine ⟨⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      dsimp only
      rw [E.joint_T_top_integrand_eq E.VSstar_mem _ y.property,
          E.joint_T_top_integrand_eq E.VSstar_mem _ y.property]
      exact E.zero_isMaxOn_joint hTM (E.VTstar_mem hTM hmono) E.VSstar_mem y.property ha
    rw [hgt.csSup_eq, E.joint_T_top_integrand_eq E.VSstar_mem _ y.property, E.joint_T_integrand_eq]
    have h := congrArg (fun V : Val => V y) (E.VTstar_fix hTM hmono)
    simp only at h
    rw [targetOp_apply] at h
    exact h.symm
  α_opt_top := by
    intro x hx
    rw [isMaxOn_iff]
    intro a ha
    rw [E.joint_T_top_integrand_eq E.VSstar_mem _ hx, E.joint_T_top_integrand_eq E.VSstar_mem _ hx]
    exact E.zero_isMaxOn_joint hTM (E.VTstar_mem hTM hmono) E.VSstar_mem hx ha

end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **Both continuation channels change equilibrium behaviour** at the
composed equilibrium, at every feasible state, under the stage flip (which
the Target side uses; the Sender side needs no flip): the Sender's
forward-looking sanction is never a stage optimum, and the Target's
forward-looking compliance is never a stage optimum. General in `F`. The Sender
side needs only the stage appetite `u_hi < q` (BH3.1, 2026-10-06: the binder was
interiority `A < q`, read only through `u_hi < q`). -/
theorem both_channels_active_of_response_monotone (hS : E.uhi < E.q)
    (hP : E.Placable) (hflip : E.ℓhi < E.sfloor * E.plo)
    (hTM : E.LossOffset) (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)) :
    ∀ x ∈ Sanctions.I,
      E.toParams.ContinuationChangesSenderChoiceAt (E.equilibriumTop hTM hmono).V_S x
        ((E.equilibriumTop hTM hmono).α x)
      ∧ E.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => E.response (E.equilibriumTop hTM hmono).V_S y b)
          (E.equilibriumTop hTM hmono).V_T x :=
  fun x hx => ⟨E.sender_channel_active hS hx,
    E.target_channel_active_on_carriers hTM hP hflip (E.VTstar_mem hTM hmono) E.VSstar_mem hx⟩

end ChordEconomyRelief

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-! ## 6. Discharging the monotone-response conditional (Rung 3)

The conditional on `equilibriumTop` is discharged from primitives, given one
inequality among the economy's rates — stated as a hypothesis, never a field:

    βS · (σ_C·ghi·dhi + (KS + 2σ_C)·Mmix) ≤ r_lo.

Its economics: the stage rally complementarity (at least `r_lo`) covers the two
forward-looking forces against a monotone response — saturation of the
continuation (capped by `σ_C`, which now also carries the Sender payoff's own
state semiconvexity `τ_x`) and cross-effectiveness of the transition (capped by
`Mmix`). With a flat transition and a Sender payoff convex in the state both
vanish and the inequality reads `0 ≤ r_lo` (`margin_of_flat`).

The margin reads the two-sided curvature data `τ_x`, `M_cx`, `M_mix`, so since
renovation item BJ3.1 (2026-10-07) this section is stated on `ChordEconomyTwoSided`
(until then on `ChordEconomy`, otherwise unchanged). General in `F`. -/

/-- **Increasing differences at the equilibrium value, given the margin.** The
stage cross-difference is at least `r_lo·Δx·Δs` (S8); the continuation's is
bounded below by `crossDiff_comp_ge_of_semiconvex` on the two-sided carrier. -/
theorem senderObj_increasingDifferences_of_margin
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    Sanctions.MilgromShannon.IncreasingDifferencesOn Sanctions.I Sanctions.S
      (fun s x => E.toParams.U_S x 0 s
        + E.toParams.β_S * E.VSstar (Sanctions.clipS' (E.toParams.F x s))) := by
  intro s s' x x' hs hs' hss' hx hx' hxx'
  have hV := E.VSstar_mem2
  have hcont := crossDiff_comp_ge_of_semiconvex
    (v := fun z => E.VSstar (Sanctions.clipS' z)) (F := E.F)
    E.SigC_nonneg E.hglo0 E.hdlo0.le (E.clip_lip hV.1.1) hV.2 E.F_maps
    E.hbandAll E.hSlo E.hShi E.hFmix hx hx' hs hs' hxx' hss'
  simp only at hcont
  have hstage := E.hUS_crossLo x hx x' hx' s hs s' hs' hxx' hss'
  have hdx : 0 ≤ x' - x := by linarith
  have hds : 0 ≤ s' - s := by linarith
  have hP : 0 ≤ (x' - x) * (s' - s) := mul_nonneg hdx hds
  have h1 := mul_le_mul_of_nonneg_left hcont E.hβS0.le
  have h2 := mul_le_mul_of_nonneg_right hmargin hP
  change E.U_S x 0 s' + E.β_S * E.VSstar (Sanctions.clipS' (E.F x s'))
      - (E.U_S x 0 s + E.β_S * E.VSstar (Sanctions.clipS' (E.F x s)))
    ≤ E.U_S x' 0 s' + E.β_S * E.VSstar (Sanctions.clipS' (E.F x' s'))
      - (E.U_S x' 0 s + E.β_S * E.VSstar (Sanctions.clipS' (E.F x' s)))
  linarith [h1, h2, hstage]

/-- **The response is monotone in the state, given the margin** (the Rung 3
discharger): increasing differences at `VSstar` and state-local uniqueness on
the carrier, through the general `σ_dyn_top_monotoneOn_x_of_increasingDifferences`. -/
theorem responsePath_monotoneOn_of_margin
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1) := by
  have hmono := E.toParams.σ_dyn_top_monotoneOn_x_of_increasingDifferences E.VSstar 0
    (E.senderObj_increasingDifferences_of_margin hmargin) (E.DAU_on_carrier E.VSstar_mem)
  intro x hx y hy hxy
  simp only [responsePath]
  rw [E.response_eq_top E.VSstar_mem hx 0, E.response_eq_top E.VSstar_mem hy 0]
  exact hmono hx hy hxy

/-- **The composed equilibrium, unconditional given the margin.** -/
def equilibriumTop_of_margin (hTM : E.LossOffset)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    E.toParams.FeedbackStackelbergEquilibriumTop :=
  E.equilibriumTop hTM (E.responsePath_monotoneOn_of_margin hmargin)

end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **Both channels active at the composed equilibrium, given the margin, under
the stage appetite** `u_hi < q`. General in `F`. The stage-appetite form of the
pinned `both_channels_active_of_margin` (renovation item BH3.1, 2026-10-06): that
statement takes interiority `A = u_hi + β_S·K_S·d_hi < q`, but only its stage part
`u_hi < q` is read, by the Sender side (the stage vertex is below one). In plain
terms, both continuation channels are active even when the forward-looking Sender
would want to sanction fully: what matters is only that the myopic Sender would
not. -/
theorem both_channels_active_of_margin_stage (hS : E.uhi < E.q) (hTM : E.LossOffset)
    (hP : E.Placable)
    (hflip : E.ℓhi < E.sfloor * E.plo)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    ∀ x ∈ Sanctions.I,
      E.toParams.ContinuationChangesSenderChoiceAt (E.equilibriumTop_of_margin hTM hmargin).V_S x
        ((E.equilibriumTop_of_margin hTM hmargin).α x)
      ∧ E.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => E.response (E.equilibriumTop_of_margin hTM hmargin).V_S y b)
          (E.equilibriumTop_of_margin hTM hmargin).V_T x :=
  E.both_channels_active_of_response_monotone hS hP hflip hTM
    (E.responsePath_monotoneOn_of_margin hmargin)

/-- **Both channels active at the composed equilibrium, given the margin.** A
pinned headline, so it keeps interiority `hInt`; it is the corollary of
`both_channels_active_of_margin_stage` at `u_hi < q` (`uhi_lt_q`, BH3.1). -/
theorem both_channels_active_of_margin (hInt : E.Interior) (hTM : E.LossOffset)
    (hP : E.Placable)
    (hflip : E.ℓhi < E.sfloor * E.plo)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo) :
    ∀ x ∈ Sanctions.I,
      E.toParams.ContinuationChangesSenderChoiceAt (E.equilibriumTop_of_margin hTM hmargin).V_S x
        ((E.equilibriumTop_of_margin hTM hmargin).α x)
      ∧ E.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => E.response (E.equilibriumTop_of_margin hTM hmargin).V_S y b)
          (E.equilibriumTop_of_margin hTM hmargin).V_T x :=
  E.both_channels_active_of_margin_stage (E.uhi_lt_q hInt) hTM hP hflip hmargin

end ChordEconomyRelief

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- **The flat case.** With a Sender payoff convex in the state (`τ_x = 0`), convex
state sections of the transition and no cross-curvature — the affine law, every
additively separable transition — the margin is `0 ≤ r_lo`. General in `F` among flat
transitions. On the two-sided extension since renovation item BJ3.1 (2026-10-07). -/
theorem margin_of_flat (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMmix : E.Mmix = 0) :
    E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo := by
  have hSigC : E.SigC = 0 := by
    unfold SigC chSigC; rw [hτ, hMcx]; simp
  rw [hSigC, hMmix]; simpa using E.hrlo

/-- **The composed equilibrium at a flat transition, unconditional.** On the two-sided
extension since renovation item BJ3.1 (2026-10-07). -/
def equilibriumTop_of_flat (hTM : E.LossOffset) (hτ : E.τx = 0) (hMcx : E.Mcx = 0)
    (hMmix : E.Mmix = 0) : E.toParams.FeedbackStackelbergEquilibriumTop :=
  E.equilibriumTop_of_margin hTM (E.margin_of_flat hτ hMcx hMmix)

end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **Both channels active at a flat transition**, under the stage flip alone
(the rally margin is discharged). General in `F` among flat transitions. Under the
stage appetite `u_hi < q` (BH3.1, 2026-10-06: the binder was interiority `A < q`,
read only through `u_hi < q`). -/
theorem both_channels_active_of_flat (hS : E.uhi < E.q) (hTM : E.LossOffset)
    (hP : E.Placable)
    (hflip : E.ℓhi < E.sfloor * E.plo)
    (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMmix : E.Mmix = 0) :
    ∀ x ∈ Sanctions.I,
      E.toParams.ContinuationChangesSenderChoiceAt
        (E.equilibriumTop_of_flat hTM hτ hMcx hMmix).V_S x
        ((E.equilibriumTop_of_flat hTM hτ hMcx hMmix).α x)
      ∧ E.toParams.ContinuationChangesTargetChoiceAt
          (fun y b => E.response (E.equilibriumTop_of_flat hTM hτ hMcx hMmix).V_S y b)
          (E.equilibriumTop_of_flat hTM hτ hMcx hMmix).V_T x :=
  E.both_channels_active_of_margin_stage hS hTM hP hflip (E.margin_of_flat hτ hMcx hMmix)

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 7. The response is Lipschitz in the state (Rung 4)

Rung 3 needed the *sign* of the mixed second difference and paid for it with the
margin. Lipschitz needs only its *size*, which the two-sided carrier supplies
with no inequality at all: the difference of the Sender's objectives at two
states is Lipschitz in the sanction, and a strongly concave objective moves its
argmax at most `L/μ` under an `L`-Lipschitz perturbation
(`Foundations/StrongConcaveArgmaxStability`; the two theorems below carry the
factor-four form of round D, their sharp siblings follow). -/

/-- The objective is `μ`-strongly concave in the sanction on a carrier value,
in the chord form the perturbation lemma consumes: `−μ`-semiconcave. -/
theorem senderObj_semiconcave_neg_mu {V : Val} (hV : V ∈ E.carrierS) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (a : ℝ) :
    SemiconcaveOnSet (fun s => E.senderObj V x a s) Sanctions.I (-E.mu) := by
  have hcomp := E.carrier_comp_semiconcave hV hx
  intro s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hsc := hcomp s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hD := mul_le_mul_of_nonneg_left hsc E.hβS0.le
  have hU := E.hUS_concave x hx a s₁ hs₁ s₂ hs₂ t ht0 ht1
  have hT : 0 ≤ t * (1 - t) * (s₁ - s₂) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  simp only [senderObj]
  unfold mu plMu
  nlinarith [hD, hT, hU]

/-- **The response Lipschitz constant, closed form**: the stage rally slope plus
the discounted two-sided cross-difference constant at the larger curvature
modulus. -/
def plLresp (r βS σbar ghi dhi KS Mmix : ℝ) : ℝ :=
  r + βS * (σbar * ghi * dhi + (KS + 2 * σbar) * Mmix)

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- `L_resp`. On the two-sided extension since renovation item BJ3.1 (2026-10-07): it
reads `σ_C` and `M_mix`. -/
def Lresp : ℝ := plLresp E.rhi E.β_S (max E.SigV E.SigC) E.ghi E.dhi E.KS E.Mmix

end ChordEconomyTwoSided

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)



theorem Lresp_nonneg : 0 ≤ E.Lresp := by
  unfold Lresp plLresp
  have hσ : 0 ≤ max E.SigV E.SigC := le_max_of_le_left E.hSigV0
  apply add_nonneg E.rhi_nonneg
  apply mul_nonneg E.hβS0.le
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg hσ E.ghi_nonneg) E.dhi_nonneg
  · exact mul_nonneg (by linarith [E.KS_nonneg]) E.hMmix0

/-- **The state-perturbation of the objective is Lipschitz in the sanction**, with
constant `L_resp·|x − y|`: the stage part is exactly `r·(y − x)·(u − w)`, and the
continuation part is the two-sided cross-difference bound at `VSstar`. -/
theorem senderObj_state_perturbation_lipschitz {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    ∀ u ∈ Sanctions.I, ∀ w ∈ Sanctions.I,
      |(E.senderObj E.VSstar y 0 u - E.senderObj E.VSstar x 0 u)
          - (E.senderObj E.VSstar y 0 w - E.senderObj E.VSstar x 0 w)|
        ≤ (E.Lresp * |x - y|) * |u - w| := by
  intro u hu w hw
  have hV := E.VSstar_mem2
  have hcross := abs_crossDiff_le_of_twoSided
    (v := fun z => E.VSstar (Sanctions.clipS' z)) (F := E.F)
    E.hSigV0 E.SigC_nonneg E.hglo0 E.hdlo0.le
    (E.clip_lip hV.1.1) hV.1.2 hV.2 E.F_maps
    E.hbandAll E.hSlo E.hShi E.hFmix hx hy hw hu
  simp only at hcross
  have hid : (E.senderObj E.VSstar y 0 u - E.senderObj E.VSstar x 0 u)
        - (E.senderObj E.VSstar y 0 w - E.senderObj E.VSstar x 0 w)
      = ((E.U_S y 0 u - E.U_S y 0 w) - (E.U_S x 0 u - E.U_S x 0 w))
        + E.β_S * ((E.VSstar (Sanctions.clipS' (E.F y u)) - E.VSstar (Sanctions.clipS' (E.F y w)))
          - (E.VSstar (Sanctions.clipS' (E.F x u)) - E.VSstar (Sanctions.clipS' (E.F x w)))) := by
    simp only [senderObj]; ring
  rw [hid]
  have hstage := E.hUS_crossHi 0 zero_mem_I x hx y hy w hw u hu
  have h1 := abs_add_le ((E.U_S y 0 u - E.U_S y 0 w) - (E.U_S x 0 u - E.U_S x 0 w))
    (E.β_S * ((E.VSstar (Sanctions.clipS' (E.F y u)) - E.VSstar (Sanctions.clipS' (E.F y w)))
      - (E.VSstar (Sanctions.clipS' (E.F x u)) - E.VSstar (Sanctions.clipS' (E.F x w)))))
  have h3 := mul_le_mul_of_nonneg_left hcross E.hβS0.le
  rw [abs_mul E.β_S, abs_of_nonneg E.hβS0.le] at h1
  have h4 : (E.Lresp * |x - y|) * |u - w|
      = E.rhi * (|y - x| * |u - w|)
        + E.β_S * ((max E.SigV E.SigC * E.ghi * E.dhi + (E.KS + 2 * max E.SigV E.SigC) * E.Mmix)
          * |y - x| * |u - w|) := by
    unfold Lresp plLresp
    rw [abs_sub_comm x y]
    ring
  rw [h4]
  linarith [h1, hstage, h3]

/-- **The response is Lipschitz in the political state**, with constant
`4·L_resp/μ`, on the two-sided carrier and with no margin: the argmax of a
`μ`-strongly concave objective moves at most `4L/μ` under an `L`-Lipschitz
perturbation, and the state-perturbation is `L_resp·|x − y|`-Lipschitz. -/
theorem responsePath_lipschitz {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |E.responsePath E.VSstar x - E.responsePath E.VSstar y|
      ≤ 4 * (E.Lresp * |x - y|) / E.mu := by
  have hf := E.senderObj_semiconcave_neg_mu E.VSstar_mem hx 0
  have hpert := E.senderObj_state_perturbation_lipschitz hx hy
  exact argmax_dist_le_of_strongConcave_lipschitz_perturbation (convex_Icc 0 1) E.mu_pos
    (mul_nonneg E.Lresp_nonneg (abs_nonneg _)) hf hpert
    (E.response_mem _ _ _) (E.response_mem _ _ _)
    (E.response_isMaxOn _ _ _) (E.response_isMaxOn _ _ _)

/-- **The realised successor is Lipschitz in the state**, constant
`ghi + dhi·4L_resp/μ`: the state chord and the sanction chord, through the
Lipschitz response. -/
theorem successor_lipschitz {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |E.F x (E.responsePath E.VSstar x) - E.F y (E.responsePath E.VSstar y)|
      ≤ (E.ghi + E.dhi * (4 * E.Lresp / E.mu)) * |x - y| := by
  have hρx := E.responsePath_mem E.VSstar x
  have hρy := E.responsePath_mem E.VSstar y
  have hstate := abs_sub_le_of_stateBand E.hglo0 (E.hbandAll _ hρx) hx hy
  simp only at hstate
  have hsanc := abs_sub_le_of_sanctionChords E.hdlo0.le E.hSlo E.hShi hy hρx hρy
  have hρ := E.responsePath_lipschitz hx hy
  have htri := abs_sub_le (E.F x (E.responsePath E.VSstar x)) (E.F y (E.responsePath E.VSstar x))
    (E.F y (E.responsePath E.VSstar y))
  have hmu := E.mu_pos
  have hρ' : E.dhi * |E.responsePath E.VSstar x - E.responsePath E.VSstar y|
      ≤ E.dhi * (4 * E.Lresp / E.mu * |x - y|) := by
    apply mul_le_mul_of_nonneg_left _ E.dhi_nonneg
    calc |E.responsePath E.VSstar x - E.responsePath E.VSstar y|
        ≤ 4 * (E.Lresp * |x - y|) / E.mu := hρ
      _ = 4 * E.Lresp / E.mu * |x - y| := by ring
  nlinarith [htri, hstate, hsanc, hρ']

/-! ### The sharp constants (round L, doc 80 M1)

The two theorems above carry the factor four of the midpoint chord. The sharp
argmax stability lemma (`argmax_dist_le_of_strongConcave_lipschitz_perturbation_sharp`,
constant `L/μ`) removes it under the same hypotheses; the old statements and
their names are kept, the sharp forms are siblings. -/

/-- **The response is `L_resp/μ`-Lipschitz in the state** (sharp form): the same
inputs as `responsePath_lipschitz`, through the sharp stability lemma. -/
theorem responsePath_lipschitz_sharp {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    |E.responsePath E.VSstar x - E.responsePath E.VSstar y|
      ≤ (E.Lresp * |x - y|) / E.mu := by
  have hf := E.senderObj_semiconcave_neg_mu E.VSstar_mem hx 0
  have hpert := E.senderObj_state_perturbation_lipschitz hx hy
  exact argmax_dist_le_of_strongConcave_lipschitz_perturbation_sharp (convex_Icc 0 1) E.mu_pos
    (mul_nonneg E.Lresp_nonneg (abs_nonneg _)) hf hpert
    (E.response_mem _ _ _) (E.response_mem _ _ _)
    (E.response_isMaxOn _ _ _) (E.response_isMaxOn _ _ _)

/-- **The realised successor is `(g_hi + d_hi·L_resp/μ)`-Lipschitz in the state**
(sharp form): `successor_lipschitz` with the sharp response constant. -/
theorem successor_lipschitz_sharp {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |E.F x (E.responsePath E.VSstar x) - E.F y (E.responsePath E.VSstar y)|
      ≤ (E.ghi + E.dhi * (E.Lresp / E.mu)) * |x - y| := by
  have hρx := E.responsePath_mem E.VSstar x
  have hρy := E.responsePath_mem E.VSstar y
  have hstate := abs_sub_le_of_stateBand E.hglo0 (E.hbandAll _ hρx) hx hy
  simp only at hstate
  have hsanc := abs_sub_le_of_sanctionChords E.hdlo0.le E.hSlo E.hShi hy hρx hρy
  have hρ := E.responsePath_lipschitz_sharp hx hy
  have htri := abs_sub_le (E.F x (E.responsePath E.VSstar x)) (E.F y (E.responsePath E.VSstar x))
    (E.F y (E.responsePath E.VSstar y))
  have hmu := E.mu_pos
  have hρ' : E.dhi * |E.responsePath E.VSstar x - E.responsePath E.VSstar y|
      ≤ E.dhi * (E.Lresp / E.mu * |x - y|) := by
    apply mul_le_mul_of_nonneg_left _ E.dhi_nonneg
    calc |E.responsePath E.VSstar x - E.responsePath E.VSstar y|
        ≤ (E.Lresp * |x - y|) / E.mu := hρ
      _ = E.Lresp / E.mu * |x - y| := by ring
  nlinarith [htri, hstate, hsanc, hρ']

end ChordEconomyRelief

end

end Examples
end Sanctions
