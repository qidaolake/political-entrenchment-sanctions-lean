/-
Sanctions/Examples/PlacableSenderCollapseEquilibrium.lean

**The collapse with fourteen equalities, and the exact equilibrium threshold
there** (round BB, 2026-09-28; doc 110, item R11 (a) and (c)).

`collapse_sides` (`PlacableSenderBracket.lean`) and `collapse_threshold`
(`PlacableSenderBracketSatellites.lean`) show that under sixteen tightness
equalities the three certificates of the bracket in the Target's discount
factor read one threshold `β_T* = D/(δ v + (1 − δ) D)` (`betaStar`). This file
does two things beside them; neither original is touched.

* **(a) Two of the sixteen equalities are redundant.** The supplied Sender
  modulus at zero, `σ_V = 0`, turns the Riccati closure `hSigV` into
  `σ_x + β_S K_S M_x + (r_hi + β_S K_S M_m)²/μ ≤ 0`. Every term is nonnegative
  and `μ > 0`, so `r_hi = σ_x = M_x = M_m = 0`
  (`zeros_of_SigV_eq_zero`, `rhi_eq_zero_of_SigV_eq_zero`). So `σ_V = 0` is not
  only a certificate choice: it is content about the payoff (zero upper cross
  rate, and zero state modulus in the Sender's joint semiconcavity bound
  `hUS_joint`: the defiance payoff is concave along the state) and about the
  transition (zero state and mixed moduli in its joint-semiconcavity bound
  `hFjsc`). These are one-sided moduli: a zero modulus still allows strict
  concavity. And tight Target state rates with no upper
  envelope slope, `v_lo = v_hi` and `n_hi = 0`, force `n_lo = 0`, through
  `v_lo + n_lo ≤ v_hi + n_hi` at sanction one and `n_lo ≥ 0`
  (`nlo_eq_zero_of_tight_state_rates`). So `collapse_sides'` and
  `collapse_threshold'` have the conclusions of the originals under fourteen
  equalities: `σ_V`, `M_s`, `τ_x`, `M_cx`, `M_cs`, `M_mix`, `n_hi` zero, and
  `Q̄ = q`, `k_lo = k_hi`, `ℓ_lo = ℓ_hi`, `p_lo = c`, `v_lo = v_hi`,
  `g_lo = g_hi`, `d_lo = d_hi`. `collapse_Lresp'` drops `r_hi = 0` likewise
  (five equalities to four).

* **(c) At the collapse the threshold is an equilibrium statement.** The
  originals compare certificates: the sharp defiance side, the relief sides.
  Here, under the fourteen equalities, placability (`Placable`: the Sender's
  appetite is at most the lower placation rate) and `β_T ≠ β_T*`, a top-selector
  feedback Stackelberg equilibrium in which the Target defies at every feasible
  state exists **if and only if** `β_T* < β_T`
  (`collapse_equilibrium_threshold`). Above the threshold the equilibrium is the
  constructed one, `equilibriumTop_sharp` at `g = g_T`: at the collapse the
  response does not move with the state (`L_resp = 0`), so it is monotone
  (`responsePath_monotoneOn_of_Lresp_eq_zero`) and `g_T` balances exactly
  (`gT_balance_of_Lresp_eq_zero`); the sharp side at `g_T` is `β_T* < β_T`
  (`collapse_threshold'`). Below it no top-selector equilibrium of any kind has
  full defiance: any such equilibrium has the constructed values
  (`values_eq_of_policy_zero`), the loop condition holds because the loop rate
  is `g_hi` at `L_resp = 0` (`βT_ghi_lt_one`), and the relief side against the
  defiance-profile values holds (`collapse_threshold'`), so
  `no_defiance_equilibrium_of_relief_side` applies. Placability and
  `β_T ≠ β_T*` are read by the non-existence direction only; the existence
  direction (`exists_defiance_equilibrium_of_collapse`) needs neither. Since renovation
  item BG3.3 (2026-10-06) it reads seven conditions in place of the stage relief margin
  and the fourteen equalities: `σ_V = M_s = τ_x = M_cx = M_mix = 0`, `1 ≤ g_lo + d_lo` and
  `β_T* < β_T`. Its core is `exists_defiance_equilibrium_of_Lresp_eq_zero`: `L_resp = 0`
  and the weak sharp side at `g_T` give full defiance.

**Scope (Rule 9).** Universal over the enriched chord class at the collapse.
The existence direction exhibits a constructed equilibrium; the non-existence
direction quantifies over every `FeedbackStackelbergEquilibriumTop` with
`α ≡ 0` on `[0,1]`. The statement is about full defiance only: it says nothing
about equilibria with partial compliance. The fourteen equalities are a
sufficient condition for the window to close, not a characterisation of when it
does. The equality case `β_T = β_T*` is decided in `PlacableSenderDefianceClosed.lean`:
full defiance exists at the threshold (`collapse_equilibrium_threshold_le`). The hypothesis
bundle is jointly satisfiable, and both sides of the threshold are inhabited, at the
affine members of `PlacableSenderCollapseWitness.lean` (`β_T* = 2/11`; a
full-defiance equilibrium at `β_T = 1/2`, none at `β_T = 1/8`).

**Rule 22: AFFINE BY HYPOTHESIS.** The tight sanction chords (`d_lo = d_hi`) and
tight state chords (`g_lo = g_hi`), with `F_diag`, pin the affine law
`F = affineF d_lo` on the unit square (either pair alone suffices:
`ChordEconomy.F_eq_affineF_of_tight_sanction` and `_of_tight_state`,
`ChordEconomyTightChords.lean`); every theorem here that carries both
equalities is the affine collapse of the general bracket, stated over the general
class. The lemmas that read neither chord equality nor `L_resp = 0` are general in `F`:
`zeros_of_SigV_eq_zero`, `rhi_eq_zero_of_SigV_eq_zero` and
`nlo_eq_zero_of_tight_state_rates`. A zero response slope itself forces the affine law
`F = affineF (1 − F(1,0))` on the square (`F_eq_affineF_of_Lresp_eq_zero`, renovation item
BG3.4, 2026-10-06, a general-`F` theorem), so `collapse_Lresp'`,
`responsePath_eq_of_Lresp_eq_zero`, `responsePath_monotoneOn_of_Lresp_eq_zero` and
`exists_defiance_equilibrium_of_Lresp_eq_zero` are affine by hypothesis as well, although
they carry no chord equality. Until 2026-10-06 the first three were listed as general.

**Rule 3.** No field, no new hypothesis: every premise is a premise of
`collapse_sides`, `collapse_threshold` or `no_defiance_equilibrium_of_relief_side`,
or the strict scope restriction `β_T ≠ β_T*`; two premises of the originals
(`r_hi = 0`, `n_lo = 0`) are removed as derivable. The existence direction's
`1 ≤ g_lo + d_lo` is implied by the tight chords (`glo_add_dlo_eq_one_of_tight`).
Rule 1: the full-defiance
policy is not imposed; existence is of an equilibrium whose `α ≡ 0` is the
Target's unique optimum (the equilibrium records only that it is a maximiser;
uniqueness is the strict decrease of the Target's objective on the sharp side,
`targetObj_strictAntiOn_of_sharp`), and non-existence is over all equilibria.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.
-/
import Sanctions.Examples.PlacableSenderBracketSatellites
import Sanctions.Examples.PlacableSenderDefianceValues

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## (a) The redundant equalities -/


end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **A zero Sender modulus forces the payoff and transition zeros.** If the
supplied Sender-carrier modulus is zero (`σ_V = 0`), the Riccati closure `hSigV`
reads `σ_x + β_S K_S M_x + (r_hi + β_S K_S M_m)²/μ ≤ 0`; every term is
nonnegative and `μ > 0`, so the Sender's upper cross rate `r_hi`, its state
semiconcavity modulus `σ_x`, and the transition's state and mixed joint-curvature
moduli `M_x`, `M_m` all vanish. Rule 22: general in `F`. -/
theorem zeros_of_SigV_eq_zero (hSigV : E.SigV = 0) :
    E.rhi = 0 ∧ E.σx = 0 ∧ E.Mx = 0 ∧ E.Mm = 0 := by
  have hcl := E.hSigV
  have hμ := E.mu_pos
  unfold mu plMu at hμ
  rw [hSigV] at hcl hμ
  unfold chSigImg chSig plRho plMu at hcl
  change E.σx + E.β_S * (0 * E.ghi ^ 2 + E.KS * E.Mx)
      + (E.rhi + E.β_S * (0 * E.ghi * E.dhi + E.KS * E.Mm)) ^ 2
        / (E.q - E.β_S * (0 * E.dhi ^ 2 + E.KS * E.Ms)) ≤ 0 at hcl
  have hKS := E.KS_pos
  have hβ := E.hβS0
  have hr := E.rhi_nonneg
  have hσ := E.hσx0
  have hMx := E.hMx0
  have hMm := E.hMm0
  have hβK : 0 < E.β_S * E.KS := mul_pos hβ hKS
  have hsq : 0 ≤ (E.rhi + E.β_S * (0 * E.ghi * E.dhi + E.KS * E.Mm)) ^ 2
      / (E.q - E.β_S * (0 * E.dhi ^ 2 + E.KS * E.Ms)) :=
    div_nonneg (sq_nonneg _) hμ.le
  have hxm : 0 ≤ E.β_S * (0 * E.ghi ^ 2 + E.KS * E.Mx) := by
    have := mul_nonneg hβK.le hMx
    nlinarith
  have hσ0 : E.σx = 0 := by linarith
  have hx0 : E.β_S * (0 * E.ghi ^ 2 + E.KS * E.Mx) = 0 := by linarith
  have hq0 : (E.rhi + E.β_S * (0 * E.ghi * E.dhi + E.KS * E.Mm)) ^ 2
      / (E.q - E.β_S * (0 * E.dhi ^ 2 + E.KS * E.Ms)) = 0 := by linarith
  rw [div_eq_zero_iff] at hq0
  have hρ0 : E.rhi + E.β_S * (0 * E.ghi * E.dhi + E.KS * E.Mm) = 0 := by
    rcases hq0 with h | h
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    · exact absurd h hμ.ne'
  have hm : 0 ≤ E.β_S * E.KS * E.Mm := mul_nonneg hβK.le hMm
  have hr0 : E.rhi = 0 := by nlinarith
  have hMm0 : E.Mm = 0 := by
    have h1 : E.β_S * E.KS * E.Mm = 0 := by nlinarith
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hβK.ne'
    · exact h
  have hMx0 : E.Mx = 0 := by
    have h1 : E.β_S * E.KS * E.Mx = 0 := by nlinarith
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hβK.ne'
    · exact h
  exact ⟨hr0, hσ0, hMx0, hMm0⟩

/-- **A zero Sender modulus forces a zero upper cross rate**: `σ_V = 0` implies
`r_hi = 0` (`zeros_of_SigV_eq_zero`). So the hypothesis `r_hi = 0` of the
collapse theorems is redundant beside `σ_V = 0`. Rule 22: general in `F`. -/
theorem rhi_eq_zero_of_SigV_eq_zero (hSigV : E.SigV = 0) : E.rhi = 0 :=
  (E.zeros_of_SigV_eq_zero hSigV).1

/-- **Tight Target state rates force a zero lower envelope slope**: if the
Target's lower and upper state rates agree (`v_lo = v_hi`) and the upper
envelope has no sanction slope (`n_hi = 0`), then the lower envelope has none
either (`n_lo = 0`): the two envelopes are ordered at sanction one
(`vlo_le_vhi`), and `n_lo ≥ 0` is a field. Rule 22: general in `F`. -/
theorem nlo_eq_zero_of_tight_state_rates (hv : E.vlo = E.vhi) (hnhi : E.nhi = 0) :
    E.nlo = 0 := by
  have h := E.vlo_le_vhi 1 one_mem_I
  rw [hv, hnhi] at h
  have := E.hnlo
  linarith

/-- **A zero response slope forces the affine law** (renovation item BG3.4, 2026-10-06).
If the Sender's response does not move with the state, `L_resp = 0`, the transition is the
affine law `F = affineF (1 − F(1,0))` at every feasible state and sanction. Every term of
`L_resp = r_hi + β_S(σ̄ g_hi d_hi + (K_S + 2σ̄) M_mix)` is nonnegative, so `M_mix = 0` and
`σ̄·g_hi = 0` (`σ̄ = max σ_V σ_C`). If `g_hi = 0` every state section of `F` is constant;
if `σ̄ = 0` then `M_x = 0` (`zeros_of_SigV_eq_zero`) and `M_cx = 0`, so every state section
is both concave (`hFjsc`) and convex (`hFcx`). Either way each section `F(·, s)` is affine
on `[0,1]`; the zero mixed chord (`hFmix`) gives it the common slope `F(1,0)`, and the
fixed diagonal (`F_diag`) pins the intercept. So `L_resp = 0` is not a regularity
condition: every result that assumes it is affine by hypothesis (Rule 22). The statement is
confined to the feasible square, where the chord fields quantify. General in `F`: it is the
theorem that pins `F`, and it reads only the class fields. It sits on the relief extension
because it uses `r_hi ≥ 0` (`rhi_nonneg`). -/
theorem F_eq_affineF_of_Lresp_eq_zero (hL : E.Lresp = 0) {x s : ℝ}
    (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    E.F x s = affineF (1 - E.F 1 0) x s := by
  -- every term of `L_resp` is nonnegative, so each vanishes
  have hσ0 : 0 ≤ max E.SigV E.SigC := le_max_of_le_left E.hSigV0
  have hd : 0 < E.dhi := lt_of_lt_of_le E.hdlo0 E.hdlo_dhi
  have h1 : 0 ≤ max E.SigV E.SigC * E.ghi * E.dhi :=
    mul_nonneg (mul_nonneg hσ0 E.ghi_nonneg) hd.le
  have h2 : 0 ≤ (E.KS + 2 * max E.SigV E.SigC) * E.Mmix :=
    mul_nonneg (by linarith [E.KS_pos]) E.hMmix0
  have hL' := hL
  unfold Lresp plLresp at hL'
  have h3 := mul_nonneg E.hβS0.le (add_nonneg h1 h2)
  have h4 : E.β_S * (max E.SigV E.SigC * E.ghi * E.dhi
      + (E.KS + 2 * max E.SigV E.SigC) * E.Mmix) = 0 := by linarith [E.rhi_nonneg]
  have h5 := (mul_eq_zero.mp h4).resolve_left E.hβS0.ne'
  have hA : max E.SigV E.SigC * E.ghi = 0 :=
    (mul_eq_zero.mp (show max E.SigV E.SigC * E.ghi * E.dhi = 0 by linarith)).resolve_right
      hd.ne'
  have hMmix : E.Mmix = 0 :=
    (mul_eq_zero.mp (show (E.KS + 2 * max E.SigV E.SigC) * E.Mmix = 0 by linarith)).resolve_left
      (by linarith [E.KS_pos])
  -- each state section `F(·, s)` is affine on the unit interval
  have haff : ∀ y ∈ Sanctions.I, E.F y s = E.F 0 s + y * (E.F 1 s - E.F 0 s) := by
    intro y hy
    rcases mul_eq_zero.mp hA with hσ | hg
    · -- `σ̄ = 0`: the state sections are concave (`M_x = 0`) and convex (`M_cx = 0`)
      have hSigV : E.SigV = 0 := le_antisymm (hσ ▸ le_max_left _ _) E.hSigV0
      have hSigC : E.SigC = 0 := le_antisymm (hσ ▸ le_max_right _ _) E.SigC_nonneg
      have hMx : E.Mx = 0 := (E.zeros_of_SigV_eq_zero hSigV).2.2.1
      have hMcx : E.Mcx = 0 := by
        have hden : 0 < 1 - E.β_S * E.ghi ^ 2 := by linarith [E.βS_ghi_sq_lt_one]
        have hnum : E.τx + E.β_S * E.KS * E.Mcx = 0 := by
          have h := hSigC
          unfold SigC chSigC at h
          rcases div_eq_zero_iff.mp h with h | h
          · exact h
          · exact absurd h hden.ne'
        have hk : 0 ≤ E.β_S * E.KS * E.Mcx :=
          mul_nonneg (mul_nonneg E.hβS0.le E.KS_nonneg) E.hMcx0
        have hk0 : E.β_S * E.KS * E.Mcx = 0 := by linarith [E.hτx0]
        exact (mul_eq_zero.mp hk0).resolve_left (mul_pos E.hβS0 E.KS_pos).ne'
      have hcav := E.hFjsc 1 one_mem_I 0 zero_mem_I s hs s hs y hy.1 hy.2
      have hvex := E.hFcx s hs 1 one_mem_I 0 zero_mem_I y hy.1 hy.2
      have e1 : y * 1 + (1 - y) * 0 = y := by ring
      have e2 : y * s + (1 - y) * s = s := by ring
      rw [e1, e2, hMx] at hcav
      rw [e1, hMcx] at hvex
      have r1 : y * (1 - y) / 2 * (0 * (1 - 0) ^ 2 + 2 * E.Mm * |1 - 0| * |s - s|
          - -E.Ms * (s - s) ^ 2) = 0 := by simp
      have r2 : (0 : ℝ) / 2 * (y * (1 - y) * (1 - 0) ^ 2) = 0 := by simp
      rw [r1] at hcav
      rw [r2] at hvex
      linarith
    · -- `g_hi = 0`: the state sections are constant
      have hglo : E.glo = 0 := le_antisymm (hg ▸ E.hglo_ghi) E.hglo0
      have hb1 := (E.hbandAll s hs) 0 zero_mem_I y hy hy.1
      have hb2 := (E.hbandAll s hs) 0 zero_mem_I 1 one_mem_I zero_le_one
      rw [hg, hglo] at hb1 hb2
      simp only [zero_mul] at hb1 hb2
      have hy0 : E.F y s - E.F 0 s = 0 := le_antisymm hb1.2 hb1.1
      have h10 : E.F 1 s - E.F 0 s = 0 := le_antisymm hb2.2 hb2.1
      rw [h10, mul_zero, add_zero]
      linarith
  -- the zero mixed chord: `F(1, s) − F(0, s) = F(1, 0) − F(0, 0) = F(1, 0)`
  have hmix : E.F 1 s - E.F 0 s = E.F 1 0 := by
    have h := E.hFmix (x₁ := 0) (x₂ := 1) (s₁ := 0) (s₂ := s) zero_mem_I one_mem_I zero_mem_I hs
    rw [hMmix, zero_mul, zero_mul] at h
    have h0 := abs_nonpos_iff.mp h
    have hF00 := E.F_diag 0
    linarith
  -- the fixed diagonal pins the intercept: `F(0, s) = s − s·F(1, 0)`
  have hdiag := E.F_diag s
  rw [haff s hs, hmix] at hdiag
  rw [haff x hx, hmix, affineF]
  linarith

/-! ## (c), the existence side: a state-independent response is monotone -/

/-- **Where the response does not move with the state, it is constant**: at
`L_resp = 0` the sharp response Lipschitz bound (`responsePath_lipschitz_sharp`)
reads `|ρ(x) − ρ(y)| ≤ 0`. **Rule 22: AFFINE BY HYPOTHESIS** (renovation item BG3.4,
2026-10-06; it was read as general in `F`): `L_resp = 0` forces the affine law
(`F_eq_affineF_of_Lresp_eq_zero`). -/
theorem responsePath_eq_of_Lresp_eq_zero (hL : E.Lresp = 0) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    E.responsePath E.VSstar x = E.responsePath E.VSstar y := by
  have h := E.responsePath_lipschitz_sharp hx hy
  rw [hL, zero_mul, zero_div] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

/-- **Where the response does not move with the state, it is monotone**: the
monotone-response input of `equilibriumTop_sharp` holds at `L_resp = 0`.
**Rule 22: AFFINE BY HYPOTHESIS** (renovation item BG3.4, 2026-10-06; it was read as
general in `F`): `L_resp = 0` forces the affine law (`F_eq_affineF_of_Lresp_eq_zero`). -/
theorem responsePath_monotoneOn_of_Lresp_eq_zero (hL : E.Lresp = 0) :
    MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1) :=
  fun _ hx _ hy _ => (E.responsePath_eq_of_Lresp_eq_zero hL hx hy).le

/-- **A zero response slope and the weak sharp side give full defiance** (renovation item
BG3.3, 2026-10-06). If the Sender's response does not move with the state
(`L_resp = 0`) and the sharp defiance side holds weakly at `g_T`,
`c − ℓ_lo μ/k_hi ≤ β_T d_lo g_T`, a top-selector feedback Stackelberg equilibrium exists in
which the Target defies at every feasible state. It is the constructed
`equilibriumTop_sharp` at `g = g_T`: `L_resp = 0` supplies its monotone-response input
(`responsePath_monotoneOn_of_Lresp_eq_zero`) and makes `g_T` balance exactly
(`gT_balance_of_Lresp_eq_zero`). The collapse's existence direction is this statement with
its conditions translated (`exists_defiance_equilibrium_of_collapse`). **Rule 22: AFFINE BY
HYPOTHESIS**: stated over the general class, with no chord equality, but `L_resp = 0`
forces `F = affineF (1 − F(1,0))` on the square (`F_eq_affineF_of_Lresp_eq_zero`). -/
theorem exists_defiance_equilibrium_of_Lresp_eq_zero (hL : E.Lresp = 0)
    (hsharp : E.c - E.ℓlo * E.mu / E.khi ≤ E.β_T * E.dlo * E.gT) :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0 :=
  ⟨E.equilibriumTop_sharp (E.responsePath_monotoneOn_of_Lresp_eq_zero hL)
    E.gT_pos.le (E.gT_balance_of_Lresp_eq_zero hL) hsharp, fun _ _ => rfl⟩

end ChordEconomyRelief


namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided ChordEconomyRelief

variable (E : ChordEconomyCs)

/-! ## (a) The collapse with fourteen equalities -/

/-- **`L_resp = 0` at the collapse, without `r_hi = 0`**: `collapse_Lresp` with
`r_hi = 0` derived from `σ_V = 0` (`rhi_eq_zero_of_SigV_eq_zero`). Four
equalities: `σ_V`, `τ_x`, `M_cx`, `M_mix` zero. **Rule 22: AFFINE BY HYPOTHESIS**
(renovation item BG3.4, 2026-10-06; it was read as general in `F`): its conclusion
`L_resp = 0` forces the affine law (`F_eq_affineF_of_Lresp_eq_zero`), so the four
equalities already pin `F`. -/
theorem collapse_Lresp' (hSigV : E.SigV = 0) (hτ : E.τx = 0) (hMcx : E.Mcx = 0)
    (hMmix : E.Mmix = 0) : E.Lresp = 0 :=
  E.collapse_Lresp (E.rhi_eq_zero_of_SigV_eq_zero hSigV) hSigV hτ hMcx hMmix

/-- **The collapse, under fourteen tightness equalities**: the conclusion of
`collapse_sides`, with its two redundant premises removed — `r_hi = 0` follows
from `σ_V = 0` through the Riccati closure (`rhi_eq_zero_of_SigV_eq_zero`), and
`n_lo = 0` from `v_lo = v_hi` and `n_hi = 0` (`nlo_eq_zero_of_tight_state_rates`).
The fourteen: seven zeros (`σ_V`, `M_s`, `τ_x`, `M_cx`, `M_cs`, `M_mix`, `n_hi`)
and seven pair equalities (`Q̄ = q`, `k_lo = k_hi`, `ℓ_lo = ℓ_hi`, `p_lo = c`,
`v_lo = v_hi`, `g_lo = g_hi`, `d_lo = d_hi`). Then the sharp defiance side at
`g_T` reads `D < β_T δ g_T` and both relief sides read `β_T δ g_T < D`, with
`D = c − ℓ_lo q/k_hi` and `δ = d_lo`. A sufficient condition for the window to
close, not a characterisation of when it closes; the strict inequalities do not
decide the equality case. **Rule 22: AFFINE BY HYPOTHESIS.** The tight chords
`g_lo = g_hi` and `d_lo = d_hi`, with `F_diag`, pin `F = affineF d_lo` on the
square. -/
theorem collapse_sides' (hSigV : E.SigV = 0) (hMs : E.Ms = 0)
    (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMcs : E.Mcs = 0) (hMmix : E.Mmix = 0)
    (hQ : E.Qbar = E.q) (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c)
    (hv : E.vlo = E.vhi) (hnhi : E.nhi = 0) (hg : E.glo = E.ghi)
    (hd : E.dlo = E.dhi) :
    ((E.c - E.ℓlo * E.mu / E.khi < E.β_T * E.dlo * E.gT)
        ↔ (E.c - E.ℓlo * E.q / E.khi < E.β_T * E.dlo * E.gT))
    ∧ ((E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel))
        ↔ (E.β_T * E.dlo * E.gT < E.c - E.ℓlo * E.q / E.khi))
    ∧ ((E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT))
        ↔ (E.β_T * E.dlo * E.gT < E.c - E.ℓlo * E.q / E.khi)) :=
  E.collapse_sides (E.rhi_eq_zero_of_SigV_eq_zero hSigV) hSigV hMs hτ hMcx hMcs hMmix hQ hk
    hℓ hp hv (E.nlo_eq_zero_of_tight_state_rates hv hnhi) hnhi hg hd

/-- **The collapse solved for `β_T`, under fourteen tightness equalities**: the
conclusion of `collapse_threshold` — the sharp defiance side at `g_T` holds
exactly above `β_T* = D/(δ v + (1 − δ) D)` (`betaStar`) and both relief sides
exactly below it — with the redundant premises `r_hi = 0` and `n_lo = 0`
removed, as in `collapse_sides'`. A sufficient condition, not a
characterisation; the equality case `β_T = β_T*` is not decided.
**Rule 22: AFFINE BY HYPOTHESIS** (`g_lo = g_hi`, `d_lo = d_hi` and `F_diag`
pin `F = affineF d_lo` on the square). -/
theorem collapse_threshold' (hSR : E.StageRelief) (hSigV : E.SigV = 0) (hMs : E.Ms = 0)
    (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMcs : E.Mcs = 0) (hMmix : E.Mmix = 0)
    (hQ : E.Qbar = E.q) (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c)
    (hv : E.vlo = E.vhi) (hnhi : E.nhi = 0) (hg : E.glo = E.ghi)
    (hd : E.dlo = E.dhi) :
    ((E.c - E.ℓlo * E.mu / E.khi < E.β_T * E.dlo * E.gT) ↔ E.betaStar < E.β_T)
    ∧ ((E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel)) ↔ E.β_T < E.betaStar)
    ∧ ((E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT)) ↔ E.β_T < E.betaStar) :=
  E.collapse_threshold hSR (E.rhi_eq_zero_of_SigV_eq_zero hSigV) hSigV hMs hτ hMcx hMcs hMmix hQ
    hk hℓ hp hv (E.nlo_eq_zero_of_tight_state_rates hv hnhi) hnhi hg hd

/-! ## (c) The exact equilibrium threshold at the collapse -/

/-- **Above the threshold, a full-defiance equilibrium exists** (constructed), from seven
conditions (renovation item BG3.3, 2026-10-06; until then the stage relief margin and the
fourteen tightness equalities). Suppose the supplied Sender modulus, the transition's
sanction curvature, the Sender's state semiconvexity, the transition's state-section
semiconvexity and its mixed chord vanish (`σ_V = M_s = τ_x = M_cx = M_mix = 0`), the lower
chords span the square (`1 ≤ g_lo + d_lo`, hence `g_lo + d_lo = 1`), and `β_T* < β_T`. Then
the constructed top-selector feedback Stackelberg equilibrium `equilibriumTop_sharp` at
`g = g_T` exists, with the Target defying at every state. The five zeros give
`L_resp = 0` (`collapse_Lresp'`) and `μ = q` (`collapse_mu`). With `g_lo = 1 − d_lo` and
`D = c − ℓ_lo q/k_hi > 0`, the condition `β_T* < β_T` reads `D < β_T(d_lo v_lo + g_lo D)`,
which gives the sharp side at `g_T` because `n_lo·σ(0,0) ≥ 0`; at `D ≤ 0` the sharp side
holds outright. Then `exists_defiance_equilibrium_of_Lresp_eq_zero` applies. The dropped
conditions (`StageRelief`, `M_cs = 0`, `Q̄ = q`, `k_lo = k_hi`, `ℓ_lo = ℓ_hi`, `p_lo = c`,
`v_lo = v_hi`, `n_hi = 0`, `g_lo = g_hi`, `d_lo = d_hi`) are read only by the
non-existence direction. Neither placability nor `β_T ≠ β_T*` is read. **Rule 22: AFFINE
BY HYPOTHESIS**: the five zeros give `L_resp = 0`, which pins `F = affineF (1 − F(1,0))`
on the square (`F_eq_affineF_of_Lresp_eq_zero`). -/
theorem exists_defiance_equilibrium_of_collapse (hSigV : E.SigV = 0) (hMs : E.Ms = 0)
    (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMmix : E.Mmix = 0) (hgd : 1 ≤ E.glo + E.dlo)
    (hβ : E.betaStar < E.β_T) :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0 := by
  refine E.exists_defiance_equilibrium_of_Lresp_eq_zero (E.collapse_Lresp' hSigV hτ hMcx hMmix)
    (le_of_lt ?_)
  -- the sharp side at `g_T`, from `β_T* < β_T`
  rw [E.collapse_mu hSigV hMs]
  have hsum : E.glo = 1 - E.dlo := by linarith [E.glo_add_dlo_le_one]
  have hβ0 := E.hβT0
  have hd0 := E.hdlo0
  have hpos : 0 < 1 - E.β_T * E.glo := by linarith [E.βT_glo_lt_one]
  have hgT : E.vlo ≤ E.gT * (1 - E.β_T * E.glo) := by
    rw [E.gT_mul]
    nlinarith [E.hnlo, E.sfloor_mem.1]
  set D := E.c - E.ℓlo * E.q / E.khi with hD
  rcases le_or_gt D 0 with hD0 | hD0
  · have : 0 < E.β_T * E.dlo * E.gT := mul_pos (mul_pos hβ0 hd0) E.gT_pos
    linarith
  · have hden : 0 < E.dlo * E.vlo + (1 - E.dlo) * D := by
      have : 0 ≤ 1 - E.dlo := by linarith [E.hglo0]
      nlinarith [mul_pos hd0 E.hvlo, mul_nonneg this hD0.le]
    have h1 : D < E.β_T * (E.dlo * E.vlo + (1 - E.dlo) * D) := by
      have h := hβ
      unfold betaStar at h
      rw [← hD, div_lt_iff₀ hden] at h
      linarith
    rw [← hsum] at h1
    have h2 : D * (1 - E.β_T * E.glo) < E.β_T * E.dlo * E.gT * (1 - E.β_T * E.glo) := by
      have := mul_le_mul_of_nonneg_left hgT (mul_nonneg hβ0.le hd0.le)
      nlinarith
    exact lt_of_mul_lt_mul_right h2 hpos.le

/-- **Below the threshold, no equilibrium has full defiance** (all equilibria).
Under placability (`Placable`: the Sender's appetite `A` is at most the lower
placation rate `k_lo`) and the fourteen tightness equalities, if `β_T < β_T*`
then no top-selector feedback Stackelberg equilibrium has the Target defying at
every state. Any such equilibrium has the constructed values `VSstar`, `VTdef`
(`values_eq_of_policy_zero`); the loop condition `β_T L_loop < 1` holds because
`L_loop = g_hi` at `L_resp = 0` (`βT_ghi_lt_one`); and the relief side against
the defiance-profile values is `β_T < β_T*` (`collapse_threshold'`), so defiance
is not a Target best reply (`no_defiance_equilibrium_of_relief_side`).
**Rule 22: AFFINE BY HYPOTHESIS** (the tight chords pin `F = affineF d_lo` on the
square). -/
theorem no_defiance_equilibrium_of_collapse (hInt : E.Interior) (hSR : E.StageRelief) (hP :
    E.Placable) (hSigV : E.SigV = 0)
    (hMs : E.Ms = 0) (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMcs : E.Mcs = 0)
    (hMmix : E.Mmix = 0) (hQ : E.Qbar = E.q) (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi)
    (hp : E.plo = E.c) (hv : E.vlo = E.vhi) (hnhi : E.nhi = 0) (hg : E.glo = E.ghi)
    (hd : E.dlo = E.dhi) (hβ : E.β_T < E.betaStar)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) :
    ¬ ∀ x ∈ Sanctions.I, Eq.α x = 0 := by
  intro hα
  have hL := E.collapse_Lresp' hSigV hτ hMcx hMmix
  have hγ : E.β_T * E.LloopSharp < 1 := by
    unfold LloopSharp
    rw [hL, zero_div, mul_zero, add_zero]
    exact E.βT_ghi_lt_one
  have hrel := (E.collapse_threshold' hSR hSigV hMs hτ hMcx hMcs hMmix hQ hk hℓ hp hv hnhi
    hg hd).2.2.2 hβ
  obtain ⟨hVS, hVT, -⟩ := E.values_eq_of_policy_zero Eq hα
  exact E.no_defiance_equilibrium_of_relief_side hInt hP hγ hrel Eq hVS hVT hα

/-- **The exact equilibrium threshold at the collapse.** Under placability
(`Placable`: the Sender's appetite is at most the lower placation rate), the
fourteen tightness equalities (seven zeros: the supplied Sender modulus `σ_V`,
the transition's sanction curvature `M_s`, the Sender's state semiconvexity
`τ_x`, the transition's state-section semiconvexity `M_cx`, its
sanction-section semiconvexity `M_cs`, its mixed chord `M_mix`, the Target's
upper envelope slope `n_hi`; and seven pair equalities: the Sender's sanction
curvature and ceiling `Q̄ = q`, its placation rates `k_lo = k_hi`, the Target's
compliance-cost rates `ℓ_lo = ℓ_hi`, its pain rates `p_lo = c`, its state rates
`v_lo = v_hi`, and the transition's state and sanction chords `g_lo = g_hi`,
`d_lo = d_hi`), and away from the threshold (`β_T ≠ β_T*`): a top-selector
feedback Stackelberg equilibrium in which the Target defies at every feasible
state exists **if and only if** `β_T* < β_T`, with
`β_T* = D/(δ v + (1 − δ) D)`, `D = c − ℓ_lo q/k_hi`, `δ = d_lo`, `v = v_lo`
(`betaStar`).

The existence direction is the constructed equilibrium
(`exists_defiance_equilibrium_of_collapse`); the non-existence direction ranges
over every top-selector equilibrium (`no_defiance_equilibrium_of_collapse`).
The equalities are a sufficient condition for the window to close, not a
characterisation of when it closes. The equality case `β_T = β_T*` is excluded here and
closed by `collapse_equilibrium_threshold_le` (`PlacableSenderDefianceClosed.lean`). The
statement is about full defiance only. **Rule 22: AFFINE BY
HYPOTHESIS.** The tight sanction chords `d_lo = d_hi` and state chords
`g_lo = g_hi`, with `F_diag`, pin the affine law `F = affineF d_lo` on the unit
square (`ChordEconomy.F_eq_affineF_of_tight_sanction`). -/
theorem collapse_equilibrium_threshold (hInt : E.Interior) (hSR : E.StageRelief) (hP : E.Placable)
    (hSigV : E.SigV = 0)
    (hMs : E.Ms = 0) (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMcs : E.Mcs = 0)
    (hMmix : E.Mmix = 0) (hQ : E.Qbar = E.q) (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi)
    (hp : E.plo = E.c) (hv : E.vlo = E.vhi) (hnhi : E.nhi = 0) (hg : E.glo = E.ghi)
    (hd : E.dlo = E.dhi) (hne : E.β_T ≠ E.betaStar) :
    (∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0)
      ↔ E.betaStar < E.β_T := by
  constructor
  · rintro ⟨Eq, hα⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hα (E.no_defiance_equilibrium_of_collapse hInt hSR hP hSigV hMs hτ hMcx hMcs
        hMmix
        hQ hk hℓ hp hv hnhi hg hd h Eq)
    · exact h
  · exact E.exists_defiance_equilibrium_of_collapse hSigV hMs hτ hMcx hMmix
      (E.glo_add_dlo_eq_one_of_tight hg hd).ge

end ChordEconomyCs

end

#print axioms Sanctions.Examples.ChordEconomyRelief.zeros_of_SigV_eq_zero
#print axioms Sanctions.Examples.ChordEconomyRelief.rhi_eq_zero_of_SigV_eq_zero
#print axioms Sanctions.Examples.ChordEconomyRelief.nlo_eq_zero_of_tight_state_rates
#print axioms Sanctions.Examples.ChordEconomyRelief.F_eq_affineF_of_Lresp_eq_zero
#print axioms Sanctions.Examples.ChordEconomyRelief.exists_defiance_equilibrium_of_Lresp_eq_zero
#print axioms Sanctions.Examples.ChordEconomyRelief.responsePath_eq_of_Lresp_eq_zero
#print axioms Sanctions.Examples.ChordEconomyRelief.responsePath_monotoneOn_of_Lresp_eq_zero
#print axioms Sanctions.Examples.ChordEconomyCs.collapse_Lresp'
#print axioms Sanctions.Examples.ChordEconomyCs.collapse_sides'
#print axioms Sanctions.Examples.ChordEconomyCs.collapse_threshold'
#print axioms Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_of_collapse
#print axioms Sanctions.Examples.ChordEconomyCs.no_defiance_equilibrium_of_collapse
#print axioms Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold

end Examples
end Sanctions
