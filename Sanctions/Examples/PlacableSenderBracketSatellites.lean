/-
Sanctions/Examples/PlacableSenderBracketSatellites.lean

**The satellites of the bracket, on a chord economy** (round AS, 2026-09-23;
doc 102 §1 rows 3, 4, 6, 8, 11, on the user's word; on the abstract payoffs
since round AV, 2026-09-25, doc 104). Each is the general form of a result the
retired affine groups carried:

* **The Sender-side bracket** (rows 6 and 11). The Sender's *lower appetite*
  `u_lo + β_S g_S d_lo` and its *upper appetite* `A = u_hi + β_S K_S d_hi`
  bracket placability: when the lower appetite exceeds the upper placation rate
  `k_hi`, every top-selector equilibrium whose policy is nonincreasing in the
  state carries a sanction of at least `(u_lo + β_S g_S d_lo − k_hi)/Q̄ > 0` at
  every state, full compliance included (`nonplacable_floor_of_lowerAppetite`,
  from round AM's wedge floor, which reads the pairwise one-sided zero-sanction
  neutrality); when the upper appetite is at most `k_lo`, full compliance ends
  the sanction (`Placable`, round AP). The lower appetite rises strictly with the
  Sender's discount factor across economies that differ only in it
  (`lowerAppetite_lt_of_βS_lt`), and so does the upper appetite
  (`A_lt_of_βS_lt`, round AY).
* **Monotonicity in the Target's sanction-indexed rates** (row 8). The Target's
  state rates are indexed by the sanction through the envelope slopes `n_lo`,
  `n_hi` (bounds on the value of entrenchment, not cross rates; on the family,
  the rally softening `n`), and its pain rate has the floor `p_lo`. Across
  economies that differ only there, the sharp defiance side is inherited by a
  larger `n_lo` (`sharp_side_mono_nlo`), the relief-existence side by a larger
  `p_lo` (`relief_side_anti_plo`), and the relief side against the
  defiance-profile value by a larger `p_lo` together with a smaller `n_hi`
  (`relief_side_notdef_anti`). On the quadratic–linear family all three move
  together with `n` (`n_lo = n_hi = n`, `p_lo = c − n`): a larger rally softening
  `n` lowers both certified boundaries, the defiance side's because it is
  inherited by the larger `n_lo`, and both relief sides' because they are
  inherited by the smaller `n`. (This header said "raises its relief boundary" until
  round AY; the direction was corrected in the paper in round AX.)
* **Sender-independence** (row 3). The sharp defiance side at `g_T` depends on
  the Sender only through `μ`, the upper placation rate `k_hi` and the sanction
  floor `b = σ(0,0)` (the floor enters `g_T` through the envelope slope `n_lo`);
  the relief-existence side only through `M_tot`, the lower placation rate
  `k_lo` and `K_T^rel`
  (`sharp_side_eq_of_target_side_eq`, `relief_side_eq_of_target_side_eq`). These
  are equalities of the predicates with those constants held fixed, not
  invariance of the equilibrium response across re-solved economies: `μ`,
  `M_tot` and `K_T^rel` themselves move with the Sender's discount factor.
* **Disjointness of the existence side** (round AY, 2026-09-27; doc 107). The
  sharp side and the relief-existence side cannot both hold
  (`bracket_existence_sides_disjoint`), from the class conditions alone, through
  `g_lo + d_lo ≤ 1` and `v_lo + n_lo b ≤ v_hi + (c − p_lo) b`.
* **Openness in `β_T`** (row 4). The sharp side at `g_T` and the
  relief-existence side, each as a condition on `β_T` with the economy's other
  data fixed, are open sets of discount factors (`sharpSideSet_isOpen`,
  `reliefSideSet_isOpen`). No openness is proved for the second relief side.
* **Certificates and the side at `g_T`; the collapse solved** (round AY, after the
  independent check of doc 108). Every certified slope is at most `g_T`
  (`le_gT_of_balance`), so every defiance certificate implies the sharp side at
  `g_T` (`sharp_gT_of_sharp_of_balance`), and the properties above bound every
  certified defiance region. Certified defiance is itself inherited by a more
  patient Target (`certified_sharp_mono_βT`), so it is an upper set of discount
  factors; where the response does not move with the state (`L_resp = 0`, as at
  the collapse) `g_T` is certified without the margin
  (`gT_balance_of_Lresp_eq_zero`). Under the sixteen tightness equalities the three
  sides read `β_T > β_T*` and `β_T < β_T*` with
  `β_T* = D/(δ v + (1 − δ) D)` (`collapse_threshold`, through
  `glo_add_dlo_eq_one_of_tight`).

Rule 3: no field, no hypothesis beyond those of the bracket and the wedge floor.
Rule 22: general in `F`, except the statements marked otherwise: the collapse
(`collapse_threshold`) and `gT_balance_of_Lresp_eq_zero` are affine by hypothesis (the
latter since renovation item BG3.4, 2026-10-06: `L_resp = 0` forces the affine law).
Rule 9: the members of
`PlacableSenderBracketWitnesses.lean`.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.

Renovation round BJ (2026-10-07). BJ2.2: the upper placation rate `k_hi` is no longer a
field of `ChordEconomy`. The non-placable floor takes a placation ceiling `hPC`; the
sharp-side set, its openness and the Sender-independence of the sharp side are stated at
any rate `k_hi` (a number, no ceiling read); the collapse threshold `betaStar` is defined
on the relief extension, which carries `k_hi`. BJ3.1: `gT_balance_of_Lresp_eq_zero` reads
`L_resp` and is stated on `ChordEconomyTwoSided`.
-/
import Sanctions.Examples.PlacableSenderBracket
import Sanctions.Examples.PlacableSenderAllEquilibria

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 1. The Sender-side bracket -/

/-- The Sender's lower appetite at defiance, `u_lo + β_S g_S d_lo`: the stage
appetite floor at the lowest state plus the continuation wedge. -/
def lowerAppetite : ℝ := E.ulo + E.β_S * E.gS * E.dlo

theorem lowerAppetite_pos : 0 < E.lowerAppetite := by
  unfold lowerAppetite
  have := mul_nonneg (mul_nonneg E.hβS0.le E.gS_pos.le) E.hdlo0.le
  linarith [E.hulo]

/-- The lower appetite is at most the upper appetite `A`. -/
theorem lowerAppetite_le_A : E.lowerAppetite ≤ E.A := by
  unfold lowerAppetite A
  have h2 : E.β_S * E.gS * E.dlo ≤ E.β_S * E.KS * E.dhi :=
    mul_le_mul (mul_le_mul_of_nonneg_left E.gS_le_KS E.hβS0.le) E.hdlo_dhi E.hdlo0.le
      (mul_nonneg E.hβS0.le E.KS_nonneg)
  linarith [E.ulo_le_uhi]

/-- **The non-placable floor**: when the lower appetite exceeds the upper
placation rate, every top-selector equilibrium whose policy is nonincreasing in
the state carries a sanction of at least `(u_lo + β_S g_S d_lo − k_hi)/Q̄ > 0` at
every state, full compliance included — when a larger concession is never
worth more to the Sender in itself. General in `F`. Renovation item BJ2.2 (2026-10-07):
`k_hi` is any placation ceiling `hPC` (`PlacationCeiling`), no longer a field of the base
class. -/
theorem nonplacable_floor_of_lowerAppetite {khi : ℝ} (hPC : E.PlacationCeiling khi)
    (hNP : khi < E.lowerAppetite)
    (hZ : E.ZeroSanctionAntitone)
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop) (hanti : AntitoneOn Eq.α Sanctions.S)
    {x : ℝ} (hx : x ∈ Sanctions.I) :
    0 < (E.lowerAppetite - khi) / E.Qbar ∧
    min ((E.lowerAppetite - khi) / E.Qbar) 1 ≤ E.toParams.dynamicEquilibriumRule Eq x := by
  have hfloor := E.equilibrium_sanction_ge_wedge_of_antitone hPC hZ Eq hanti hx
  have hα := Eq.α_mem x hx
  have hrx : 0 ≤ E.rlo * x := mul_nonneg E.hrlo hx.1
  have hk : khi * Eq.α x ≤ khi := by nlinarith [E.khi_pos hPC, hα.2]
  refine ⟨div_pos (by linarith) E.Qbar_pos, ?_⟩
  refine le_trans (min_le_min_right 1 ?_) hfloor
  apply div_le_div_of_nonneg_right _ E.Qbar_pos.le
  unfold lowerAppetite
  linarith

/-- **The lower appetite rises strictly with the Sender's discount factor**
across economies that differ only in `β_S`: the wedge `β_S g_S d_lo` with
`g_S = w_lo/(1 − β_S g_lo)` is strictly increasing in `β_S`. -/
theorem lowerAppetite_lt_of_βS_lt (E₁ E₂ : ChordEconomy) (hulo : E₁.ulo = E₂.ulo)
    (hw : E₁.wlo = E₂.wlo) (hglo : E₁.glo = E₂.glo) (hdlo : E₁.dlo = E₂.dlo)
    (hβ : E₁.β_S < E₂.β_S) : E₁.lowerAppetite < E₂.lowerAppetite := by
  unfold lowerAppetite gS chGS
  rw [hulo, hw, hglo, hdlo]
  have hd₁ := E₁.one_sub_βS_glo_pos
  have hd₂ := E₂.one_sub_βS_glo_pos
  rw [hglo] at hd₁
  have hfrac : E₁.β_S / (1 - E₁.β_S * E₂.glo) < E₂.β_S / (1 - E₂.β_S * E₂.glo) := by
    rw [div_lt_div_iff₀ hd₁ hd₂]
    nlinarith [E₂.hglo0]
  have hwd : 0 < E₂.wlo * E₂.dlo := mul_pos E₂.hwlo E₂.hdlo0
  have e : ∀ β : ℝ, β * (E₂.wlo / (1 - β * E₂.glo)) * E₂.dlo
      = E₂.wlo * E₂.dlo * (β / (1 - β * E₂.glo)) := by intro β; ring
  rw [e E₁.β_S, e E₂.β_S]
  have := mul_lt_mul_of_pos_left hfrac hwd
  linarith

/-- **The upper appetite rises strictly with the Sender's discount factor** as
well, across economies that differ only in `β_S`: in `A = u_hi + β_S K_S d_hi`,
`K_S = w_hi/(1 − β_S g_hi)`, so `β_S K_S d_hi` is strictly increasing in `β_S`
(round AY, 2026-09-27: the manuscript's "both appetites rise strictly with the
Sender's patience" had a theorem for the lower appetite only). -/
theorem A_lt_of_βS_lt (E₁ E₂ : ChordEconomy) (huhi : E₁.uhi = E₂.uhi)
    (hw : E₁.whi = E₂.whi) (hghi : E₁.ghi = E₂.ghi) (hdhi : E₁.dhi = E₂.dhi)
    (hβ : E₁.β_S < E₂.β_S) : E₁.A < E₂.A := by
  unfold A KS chKS
  rw [huhi, hw, hghi, hdhi]
  have hd₁ := E₁.one_sub_βS_ghi_pos
  have hd₂ := E₂.one_sub_βS_ghi_pos
  rw [hghi] at hd₁
  have hfrac : E₁.β_S / (1 - E₁.β_S * E₂.ghi) < E₂.β_S / (1 - E₂.β_S * E₂.ghi) := by
    rw [div_lt_div_iff₀ hd₁ hd₂]
    nlinarith [E₂.ghi_nonneg]
  have hwd : 0 < E₂.whi * E₂.dhi := mul_pos E₂.whi_pos (lt_of_lt_of_le E₂.hdlo0 E₂.hdlo_dhi)
  have e : ∀ β : ℝ, β * (E₂.whi / (1 - β * E₂.ghi)) * E₂.dhi
      = E₂.whi * E₂.dhi * (β / (1 - β * E₂.ghi)) := by intro β; ring
  rw [e E₁.β_S, e E₂.β_S]
  have := mul_lt_mul_of_pos_left hfrac hwd
  linarith

/-! ## 3. Sender-independence of the sharp side -/

/-- **The sharp defiance side at `g_T` depends on the Sender only through `μ`,
the upper placation rate `k_hi` and the sanction floor**: two economies equal on
the Target's data, the lower chords, `μ` and `b` have the same side at a common rate
`k_hi`. General in `F`. Renovation item BJ2.2 (2026-10-07): `k_hi` is no longer a field
of the base class, so it is the argument `khi`, common to both sides; the hypothesis
`E₁.k_hi = E₂.k_hi` is dropped. -/
theorem sharp_side_eq_of_target_side_eq (E₁ E₂ : ChordEconomy) (khi : ℝ)
    (hc : E₁.c = E₂.c) (hℓ : E₁.ℓlo = E₂.ℓlo) (hβT : E₁.β_T = E₂.β_T)
    (hdlo : E₁.dlo = E₂.dlo) (hglo : E₁.glo = E₂.glo) (hv : E₁.vlo = E₂.vlo)
    (hn : E₁.nlo = E₂.nlo) (hb : E₁.sfloor = E₂.sfloor) (hμ : E₁.mu = E₂.mu) :
    (E₁.c - E₁.ℓlo * E₁.mu / khi < E₁.β_T * E₁.dlo * E₁.gT)
      ↔ (E₂.c - E₂.ℓlo * E₂.mu / khi < E₂.β_T * E₂.dlo * E₂.gT) := by
  unfold gT
  rw [hc, hℓ, hβT, hdlo, hglo, hv, hn, hb, hμ]

/-! ## 4. Openness of the sharp side in the Target's discount factor -/

/-- The sharp defiance side as a condition on `β_T`, the other data fixed, at the upper
placation rate `khi` (an argument since renovation item BJ2.2, 2026-10-07: `k_hi` is no
longer a field of the base class). -/
def sharpSideSet (khi : ℝ) : Set ℝ :=
  {β | E.c - E.ℓlo * E.mu / khi < β * E.dlo * ((E.vlo + E.nlo * E.sfloor) / (1 - β * E.glo))}

/-- **The sharp side is open in `β_T`**, at every rate `k_hi`. General in `F`. Renovation
item BJ2.2 (2026-10-07): `k_hi` is the argument `khi`; no placation ceiling is read. -/
theorem sharpSideSet_isOpen (khi : ℝ) : IsOpen (Ioo (0 : ℝ) 1 ∩ E.sharpSideSet khi) := by
  have hden : ∀ β ∈ Ioo (0 : ℝ) 1, 1 - β * E.glo ≠ 0 := by
    intro β hβ
    have h1 := mul_le_mul_of_nonneg_left E.hghi1 hβ.1.le
    have h2 := mul_le_mul_of_nonneg_left E.hglo_ghi hβ.1.le
    have : β * E.glo < 1 := by linarith [hβ.2]
    linarith
  have hcont : ContinuousOn
      (fun β : ℝ => β * E.dlo * ((E.vlo + E.nlo * E.sfloor) / (1 - β * E.glo))) (Ioo 0 1) := by
    apply ContinuousOn.mul (continuousOn_id.mul continuousOn_const)
    exact ContinuousOn.div continuousOn_const
      (continuousOn_const.sub (continuousOn_id.mul continuousOn_const)) hden
  have h : Ioo (0 : ℝ) 1 ∩ E.sharpSideSet khi
      = Ioo (0 : ℝ) 1 ∩
          (fun β : ℝ => β * E.dlo * ((E.vlo + E.nlo * E.sfloor) / (1 - β * E.glo))) ⁻¹'
          Ioi (E.c - E.ℓlo * E.mu / khi) := by
    ext β
    simp only [sharpSideSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi]
  rw [h]
  exact hcont.isOpen_inter_preimage isOpen_Ioo isOpen_Ioi

/-- The sharp side at an economy is its membership in the set at its own
`β_T`, at any rate `k_hi` (renovation item BJ2.2: the argument `khi`). -/
theorem mem_sharpSideSet_iff (khi : ℝ) :
    E.β_T ∈ E.sharpSideSet khi ↔ E.c - E.ℓlo * E.mu / khi < E.β_T * E.dlo * E.gT := Iff.rfl

/-! ## 5. Two facts about the class, for the disjointness of the existence side -/

/-- **The lower chords span at most the unit square**: `g_lo + d_lo ≤ 1`. The
lower sanction chord from `(0,0)` to `(0,1)` and the lower state chord at
sanction `1` from `(0,1)` to `(1,1)` add up to at most `F(1,1) − F(0,0) = 1`
(`F_diag`). -/
theorem glo_add_dlo_le_one : E.glo + E.dlo ≤ 1 := by
  have h1 := E.hSlo zero_mem_I zero_mem_I one_mem_I zero_le_one
  have h2 := (E.hbandAll 1 one_mem_I 0 zero_mem_I 1 one_mem_I zero_le_one).1
  have h3 := E.F_diag 0
  have h4 := E.F_diag 1
  simp only [sub_zero, mul_one] at h1 h2
  linarith


end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The Target's rates at the sanction floor**:
`v_lo + n_lo·b ≤ v_hi + (c − p_lo)·b` at `b = σ(0,0)`. The state increment from
`0` to `1` at sanction `b` is at least `v_lo + n_lo·b` (T6). It differs from the
increment at zero sanction by the pain at state `1`, at least `p_lo·b` (T5),
against the pain at state `0`, at most `c·b` (T4); and the increment at zero
sanction is at most `v_hi` (T7). No increasing differences are read: the
envelope slope `n_lo` is paid for by the pain spread `c − p_lo`. -/
theorem vlo_nlo_floor_le :
    E.vlo + E.nlo * E.sfloor ≤ E.vhi + (E.c - E.plo) * E.sfloor := by
  have hb := E.sfloor_mem
  have h1 := E.hUT_stateLo 0 zero_mem_I E.sfloor hb 0 zero_mem_I 1 one_mem_I zero_le_one
  have h2 := E.hUT_stateHi 0 zero_mem_I 0 zero_mem_I 0 zero_mem_I 1 one_mem_I
  have h3 := E.hUT_painLo 1 one_mem_I 0 zero_mem_I 0 zero_mem_I E.sfloor hb hb.1
  have h4 := E.hUT_painHi 0 zero_mem_I 0 zero_mem_I 0 zero_mem_I E.sfloor hb hb.1
  simp only [sub_zero, abs_one, mul_one, mul_zero, add_zero] at h1 h2 h3 h4
  have h5 := le_abs_self (E.U_T 1 0 0 - E.U_T 0 0 0)
  rw [sub_mul]
  linarith

/-- **Every certified slope is at most `g_T`.** A lower slope `g` satisfying the
balance inequality under which the defiance-profile value carries it
(`VTdef_lowerSlope`) is at most `g_T`: the pain term is nonnegative, and
`g_T (1 − β_T g_lo) = v_lo + n_lo b` (round AY, 2026-09-27, after the
independent check recorded in doc 108). -/
theorem le_gT_of_balance {g : ℝ}
    (hginv : g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor) : g ≤ E.gT := by
  have h0 : 0 ≤ max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu) :=
    mul_nonneg (le_max_left _ _) (div_nonneg E.Lresp_nonneg E.mu_pos.le)
  have hD : 0 < 1 - E.β_T * E.glo := by linarith [E.βT_glo_lt_one]
  have h1 : g * (1 - E.β_T * E.glo) ≤ E.gT * (1 - E.β_T * E.glo) := by
    rw [E.gT_mul]; linarith
  exact le_of_mul_le_mul_right h1 hD

/-- **Every defiance certificate implies the defiance condition at `g_T`**: if
the sharp inequality holds at a slope `g` that satisfies the balance inequality,
it holds at `g_T`. So what is proved of the condition at `g_T` — that it excludes
the relief conditions, is inherited by a more patient Target and is open in
`β_T` — bounds every certified defiance region; below the loss-offset margin the
certified slope is `min g_T g_eff` (`gSharp_balance`), not `g_T`. -/
theorem sharp_gT_of_sharp_of_balance {g : ℝ}
    (hginv : g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor)
    (hsharp : E.c - E.ℓlo * E.mu / E.khi < E.β_T * E.dlo * g) :
    E.c - E.ℓlo * E.mu / E.khi < E.β_T * E.dlo * E.gT := by
  have hg := E.le_gT_of_balance hginv
  have := mul_le_mul_of_nonneg_left hg (mul_nonneg E.hβT0.le E.hdlo0.le)
  linarith

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)


/-- **Tight chords sum to one**: with `g_lo = g_hi` and `d_lo = d_hi`, the upper
chords from `(0,0)` to `(0,1)` and on to `(1,1)` give `g_hi + d_hi ≥ 1`, so with
`glo_add_dlo_le_one` the tight rates satisfy `g_lo + d_lo = 1`. -/
theorem glo_add_dlo_eq_one_of_tight (hg : E.glo = E.ghi) (hd : E.dlo = E.dhi) :
    E.glo + E.dlo = 1 := by
  have h1 := E.hShi zero_mem_I zero_mem_I one_mem_I zero_le_one
  have h2 := (E.hbandAll 1 one_mem_I 0 zero_mem_I 1 one_mem_I zero_le_one).2
  have h3 := E.F_diag 0
  have h4 := E.F_diag 1
  simp only [sub_zero, mul_one] at h1 h2
  have := E.glo_add_dlo_le_one
  linarith

end ChordEconomy

namespace ChordEconomyTwoSided

open ChordEconomy

variable (E : ChordEconomyTwoSided)

/-- **Where the response does not move with the state, `g_T` is certified without
the margin**: at `L_resp = 0` the pain term of the balance inequality vanishes
and `g_T` balances exactly. This is the case at the collapse (`collapse_Lresp`),
so there the sharp side at `g_T` is itself the defiance certificate.

**Rule 22: AFFINE BY HYPOTHESIS** (renovation item BG3.4, 2026-10-06; it was read as
general in `F`). On every relief economy a zero response slope forces the affine law
`F = affineF (1 − F(1,0))` on the unit square
(`ChordEconomyRelief.F_eq_affineF_of_Lresp_eq_zero`). The statement sits on the two-sided
extension (renovation item BJ3.1, 2026-10-07: `L_resp` reads the two-sided curvature data;
until then on the base class), where the sign of `r_hi` is not fixed, and its proof does
not read `F`. -/
theorem gT_balance_of_Lresp_eq_zero (hL : E.Lresp = 0) :
    E.gT * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * E.gT) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor := by
  rw [hL, zero_div, mul_zero, add_zero, E.gT_mul]

end ChordEconomyTwoSided

namespace ChordEconomyRelief

variable (E : ChordEconomyRelief)

/-- The exact threshold of the tight, affine, rally-free case,
`β_T* = D/(δ v + (1 − δ) D)` with `D = c − ℓ_lo q/k_hi`, `δ = d_lo` and `v = v_lo`
(the manuscript's `eq:target-threshold`). Defined on the relief extension since
renovation item BJ2.2 (2026-10-07), which carries the upper placation rate `k_hi`; until
then on `ChordEconomy`, with the same body. Every user is stated on the relief
extension or the enriched subclass. The number is defined on every relief economy,
general in `F`; it is the exact threshold only in the tight, affine, rally-free case. -/
def betaStar : ℝ :=
  (E.c - E.ℓlo * E.q / E.khi) / (E.dlo * E.vlo + (1 - E.dlo) * (E.c - E.ℓlo * E.q / E.khi))

end ChordEconomyRelief

namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided ChordEconomyRelief

variable (E : ChordEconomyCs)

/-! ## 2. Monotonicity in the Target's sanction-indexed rates (the rally, on the family) -/

/-- Two enriched chord economies that differ only in the Target's sanction-indexed
state rates `n_lo`, `n_hi` (envelope slopes; the rally softening on the family),
its pain rate `p_lo`, and its payoff. The Sender, the transition, the discount
factors and every other rate bound are the same. -/
def SameButRally (E₁ E₂ : ChordEconomyCs) : Prop :=
  E₁.U_S = E₂.U_S ∧ E₁.σ = E₂.σ ∧ E₁.F = E₂.F ∧
  E₁.glo = E₂.glo ∧ E₁.ghi = E₂.ghi ∧ E₁.dlo = E₂.dlo ∧ E₁.dhi = E₂.dhi ∧
  E₁.Mx = E₂.Mx ∧ E₁.Mm = E₂.Mm ∧ E₁.Ms = E₂.Ms ∧ E₁.Mcx = E₂.Mcx ∧ E₁.Mmix = E₂.Mmix ∧
  E₁.Mcs = E₂.Mcs ∧ E₁.β_S = E₂.β_S ∧ E₁.β_T = E₂.β_T ∧ E₁.q = E₂.q ∧ E₁.Qbar = E₂.Qbar ∧
  E₁.whi = E₂.whi ∧ E₁.τx = E₂.τx ∧ E₁.rhi = E₂.rhi ∧ E₁.klo = E₂.klo ∧ E₁.khi = E₂.khi ∧
  E₁.ℓlo = E₂.ℓlo ∧ E₁.ℓhi = E₂.ℓhi ∧ E₁.c = E₂.c ∧ E₁.vlo = E₂.vlo ∧ E₁.vhi = E₂.vhi ∧
  E₁.SigV = E₂.SigV

theorem SameButRally.consts {E₁ E₂ : ChordEconomyCs} (h : SameButRally E₁ E₂) :
    E₁.KS = E₂.KS ∧ E₁.mu = E₂.mu ∧ E₁.SigC = E₂.SigC ∧ E₁.Lresp = E₂.Lresp ∧
    E₁.Mtot = E₂.Mtot ∧ E₁.LloopSharp = E₂.LloopSharp ∧ E₁.Lalpha = E₂.Lalpha ∧
    E₁.KTrel = E₂.KTrel ∧ E₁.sfloor = E₂.sfloor := by
  obtain ⟨-, hσ, -, hglo, hghi, hdlo, hdhi, hMx, hMm, hMs, hMcx, hMmix, hMcs, hβS, hβT, hq,
    hQ, hwhi, hτ, hr, hk, hkhi, hℓlo, hℓ, hc, hvlo, hvhi, hSigV⟩ := h
  have hKS : E₁.KS = E₂.KS := by unfold KS chKS; rw [hβS, hghi, hwhi]
  have hmu : E₁.mu = E₂.mu := by unfold mu plMu; rw [hβS, hq, hSigV, hdhi, hKS, hMs]
  have hSigC : E₁.SigC = E₂.SigC := by unfold SigC chSigC; rw [hβS, hτ, hKS, hMcx, hghi]
  have hL : E₁.Lresp = E₂.Lresp := by
    unfold Lresp plLresp; rw [hr, hβS, hSigV, hSigC, hghi, hdhi, hKS, hMmix]
  have hM : E₁.Mtot = E₂.Mtot := by unfold Mtot; rw [hQ, hβS, hSigC, hdhi, hKS, hMcs]
  have hLoop : E₁.LloopSharp = E₂.LloopSharp := by unfold LloopSharp; rw [hghi, hdhi, hL, hmu]
  have hLa : E₁.Lalpha = E₂.Lalpha := by unfold Lalpha; rw [hM, hL, hk, hmu]
  have hKr : E₁.KTrel = E₂.KTrel := by unfold KTrel; rw [hvhi, hℓ, hLa, hβT, hghi]
  have hsf : E₁.sfloor = E₂.sfloor := by unfold sfloor; rw [hσ]
  exact ⟨hKS, hmu, hSigC, hL, hM, hLoop, hLa, hKr, hsf⟩

/-- `g_T` rises with the lower envelope slope `n_lo`. -/
theorem SameButRally.gT_le {E₁ E₂ : ChordEconomyCs} (h : SameButRally E₁ E₂)
    (hn : E₁.nlo ≤ E₂.nlo) : E₁.gT ≤ E₂.gT := by
  have hc := h.consts
  obtain ⟨-, -, -, hglo, -, -, -, -, -, -, -, -, -, -, hβT, -, -, -, -, -, -, -, -, -, -,
    hvlo, -, -⟩ := h
  unfold gT
  rw [hglo, hβT, hvlo, hc.2.2.2.2.2.2.2.2]
  apply div_le_div_of_nonneg_right _ (by linarith [E₂.βT_glo_lt_one])
  have := mul_le_mul_of_nonneg_right hn E₂.sfloor_mem.1
  linarith

/-- **The sharp defiance side is inherited by a larger lower envelope slope
`n_lo`.** -/
theorem sharp_side_mono_nlo {E₁ E₂ : ChordEconomyCs} (h : SameButRally E₁ E₂)
    (hn : E₁.nlo ≤ E₂.nlo)
    (hsharp : E₁.c - E₁.ℓlo * E₁.mu / E₁.khi < E₁.β_T * E₁.dlo * E₁.gT) :
    E₂.c - E₂.ℓlo * E₂.mu / E₂.khi < E₂.β_T * E₂.dlo * E₂.gT := by
  have hc := h.consts
  have hg := h.gT_le hn
  obtain ⟨-, -, -, -, -, hdlo, -, -, -, -, -, -, -, -, hβT, -, -, -, -, -, -, hkhi, hℓlo, -,
    hcc, -, -, -⟩ := h
  rw [hcc, hℓlo, hc.2.1, hkhi, hdlo, hβT] at hsharp
  have := mul_le_mul_of_nonneg_left hg (mul_nonneg E₂.hβT0.le E₂.hdlo0.le)
  linarith

/-- **The relief-existence side is inherited by a larger pain rate** (it does not
read the envelope slopes: along the zero level the sanction is zero). -/
theorem relief_side_anti_plo {E₁ E₂ : ChordEconomyCs} (h : SameButRally E₁ E₂)
    (hp : E₂.plo ≤ E₁.plo)
    (hrel : E₂.ℓhi * E₂.Mtot < E₂.klo * (E₂.plo - E₂.β_T * E₂.dhi * E₂.KTrel)) :
    E₁.ℓhi * E₁.Mtot < E₁.klo * (E₁.plo - E₁.β_T * E₁.dhi * E₁.KTrel) := by
  have hc := h.consts
  obtain ⟨-, -, -, -, -, -, hdhi, -, -, -, -, -, -, -, hβT, -, -, -, -, -, hk, -, -, hℓ, -, -,
    -, -⟩ := h
  rw [hℓ, hc.2.2.2.2.1, hk, hβT, hdhi, hc.2.2.2.2.2.2.2.1]
  have := mul_le_mul_of_nonneg_left hp E₂.hklo.le
  linarith

/-- **The relief side against the defiance-profile value is inherited by a
larger pain rate and a smaller upper envelope slope `n_hi`**, under the loop
condition `β_T L_loop < 1` at the member it is inherited from (`hγ₂`): `K_T` reads
`n_hi` through the stage payoff's state-Lipschitz constant. -/
theorem relief_side_notdef_anti {E₁ E₂ : ChordEconomyCs} (h : SameButRally E₁ E₂)
    (hp : E₂.plo ≤ E₁.plo) (hn : E₁.nhi ≤ E₂.nhi) (hγ₂ : E₂.β_T * E₂.LloopSharp < 1)
    (hrel : E₂.ℓhi * E₂.Mtot < E₂.klo * (E₂.plo - E₂.β_T * E₂.dhi * E₂.KT)) :
    E₁.ℓhi * E₁.Mtot < E₁.klo * (E₁.plo - E₁.β_T * E₁.dhi * E₁.KT) := by
  have hc := h.consts
  have hKT : E₁.KT ≤ E₂.KT := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hβT, -, -, -, -, -, -, -, -, -, hcc, -,
      hvhi, -⟩ := h
    unfold KT LUT
    rw [hβT, hc.2.2.2.2.2.1, hcc, hvhi, hc.2.2.2.1, hc.2.1]
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : max E₂.vhi (E₂.vhi + E₁.nhi) ≤ max E₂.vhi (E₂.vhi + E₂.nhi) :=
      max_le_max le_rfl (by linarith)
    linarith
  obtain ⟨-, -, -, -, -, -, hdhi, -, -, -, -, -, -, -, hβT, -, -, -, -, -, hk, -, -, hℓ, -, -,
    -, -⟩ := h
  rw [hℓ, hc.2.2.2.2.1, hk, hβT, hdhi]
  have h1 := mul_le_mul_of_nonneg_left hp E₂.hklo.le
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKT
    (mul_nonneg E₂.hβT0.le E₂.dhi_nonneg)) E₂.hklo.le
  linarith

/-! ## 3′. Sender-independence of the relief-existence side -/

/-- **The relief-existence side depends on the Sender only through `M_tot`, the
lower placation rate `k_lo` and `K_T^rel`** (hence through `M_tot`, `k_lo`,
`L_resp` and `μ`). An equality of predicates with those constants held fixed; it
is not an invariance of the equilibrium response across re-solved economies,
since `M_tot`, `μ` and `K_T^rel` move with the Sender's discount factor. -/
theorem relief_side_eq_of_target_side_eq (E₁ E₂ : ChordEconomyCs)
    (hℓ : E₁.ℓhi = E₂.ℓhi) (hk : E₁.klo = E₂.klo) (hp : E₁.plo = E₂.plo)
    (hβT : E₁.β_T = E₂.β_T) (hdhi : E₁.dhi = E₂.dhi) (hM : E₁.Mtot = E₂.Mtot)
    (hK : E₁.KTrel = E₂.KTrel) :
    (E₁.ℓhi * E₁.Mtot < E₁.klo * (E₁.plo - E₁.β_T * E₁.dhi * E₁.KTrel))
      ↔ (E₂.ℓhi * E₂.Mtot < E₂.klo * (E₂.plo - E₂.β_T * E₂.dhi * E₂.KTrel)) := by
  rw [hℓ, hk, hp, hβT, hdhi, hM, hK]

/-! ## 4′. Openness of the relief side in the Target's discount factor -/

/-- The relief side (existence form) as a condition on `β_T`, the other data
fixed; `K_T^rel` at `β` is `(v_hi + ℓ_hi L_α)/(1 − β g_hi)`. -/
def reliefSideSet : Set ℝ :=
  {β | E.ℓhi * E.Mtot
    < E.klo * (E.plo - β * E.dhi * ((E.vhi + E.ℓhi * E.Lalpha) / (1 - β * E.ghi)))}

theorem reliefSideSet_isOpen : IsOpen (Ioo (0 : ℝ) 1 ∩ E.reliefSideSet) := by
  have hden : ∀ β ∈ Ioo (0 : ℝ) 1, 1 - β * E.ghi ≠ 0 := by
    intro β hβ
    have h1 := mul_le_mul_of_nonneg_left E.hghi1 hβ.1.le
    have : β * E.ghi < 1 := by linarith [hβ.2]
    linarith
  have hcont : ContinuousOn (fun β : ℝ =>
      E.klo * (E.plo - β * E.dhi * ((E.vhi + E.ℓhi * E.Lalpha) / (1 - β * E.ghi))))
      (Ioo 0 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.mul (continuousOn_id.mul continuousOn_const)
    exact ContinuousOn.div continuousOn_const
      (continuousOn_const.sub (continuousOn_id.mul continuousOn_const)) hden
  have h : Ioo (0 : ℝ) 1 ∩ E.reliefSideSet
      = Ioo (0 : ℝ) 1 ∩ (fun β : ℝ =>
          E.klo * (E.plo - β * E.dhi * ((E.vhi + E.ℓhi * E.Lalpha) / (1 - β * E.ghi)))) ⁻¹'
          Ioi (E.ℓhi * E.Mtot) := by
    ext β
    simp only [reliefSideSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi]
  rw [h]
  exact hcont.isOpen_inter_preimage isOpen_Ioo isOpen_Ioi

theorem mem_reliefSideSet_iff :
    E.β_T ∈ E.reliefSideSet
      ↔ E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel) :=
  Iff.rfl

/-! ## 5′. The sharp side and the relief-existence side are disjoint

`bracket_sides_disjoint` (round AQ) separates the sharp defiance side from the
second relief side, the one against the defiance-profile values (the `K_T`
inequality, with the loop condition). The relief equilibrium itself exists under
a different inequality, the `K_T^rel` form (`reliefEquilibriumTop`). That side is
disjoint from the sharp side as well, from the class conditions alone (round AY,
2026-09-27; the outside reader's D1, doc 107). -/

/-- **The sharp side and the relief-existence side cannot both hold**: the sharp
defiance side at `g_T` and the inequality
`ℓ_hi·M_tot < k_lo(p_lo − β_T d_hi K_T^rel)` under which the relief equilibrium
exists. No comparison of `g_T` with `K_T^rel` is proved (the outside reader
reports that `g_T ≤ K_T^rel` fails at a family member with a positive Target
rally; not checked here), so the proof pays for the difference with the pain
spread: `β_T d_lo g_T ≤ β_T d_hi K_T^rel + (c − p_lo)`,
from `vlo_nlo_floor_le` and `β_T d_lo ≤ 1 − β_T g_lo` (`glo_add_dlo_le_one`). No
neutrality, placability or loop condition is read. -/
theorem bracket_existence_sides_disjoint
    (hsharp : E.c - E.ℓlo * E.mu / E.khi < E.β_T * E.dlo * E.gT)
    (hrel : E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel)) : False := by
  have hβ0 := E.hβT0
  have hb := E.sfloor_mem
  have hC : 0 ≤ E.c - E.plo := sub_nonneg.mpr E.plo_le_c
  have hD1 : 0 < 1 - E.β_T * E.glo := by linarith [E.βT_glo_lt_one]
  have hD21 : 1 - E.β_T * E.ghi ≤ 1 - E.β_T * E.glo := by
    have := mul_le_mul_of_nonneg_left E.hglo_ghi hβ0.le
    linarith
  -- `β_T d_lo ≤ 1 − β_T g_lo`, from `g_lo + d_lo ≤ 1` and `β_T < 1`
  have hβd : E.β_T * E.dlo ≤ 1 - E.β_T * E.glo := by
    have h := mul_le_mul_of_nonneg_left E.glo_add_dlo_le_one hβ0.le
    rw [mul_add, mul_one] at h
    linarith [E.hβT1]
  -- `v_hi ≤ K_T^rel (1 − β_T g_lo)`
  have hKnn := E.KTrel_nonneg
  have hvK : E.vhi ≤ E.KTrel * (1 - E.β_T * E.glo) := by
    have hfix : E.vhi + E.ℓhi * E.Lalpha = E.KTrel * (1 - E.β_T * E.ghi) := by
      linear_combination E.KTrel_fix
    have h1 : E.KTrel * (1 - E.β_T * E.ghi) ≤ E.KTrel * (1 - E.β_T * E.glo) :=
      mul_le_mul_of_nonneg_left hD21 hKnn
    have h2 : 0 ≤ E.ℓhi * E.Lalpha := mul_nonneg E.ℓhi_pos.le E.Lalpha_nonneg
    linarith
  -- `g_T (1 − β_T g_lo) ≤ K_T^rel (1 − β_T g_lo) + (c − p_lo) b`
  have hgD : E.gT * (1 - E.β_T * E.glo)
      ≤ E.KTrel * (1 - E.β_T * E.glo) + (E.c - E.plo) * E.sfloor := by
    rw [E.gT_mul]
    linarith [E.vlo_nlo_floor_le]
  -- the key inequality `β_T d_lo g_T ≤ β_T d_hi K_T^rel + (c − p_lo)`
  have hβdlo : 0 ≤ E.β_T * E.dlo := mul_nonneg hβ0.le E.hdlo0.le
  have hCb : 0 ≤ (E.c - E.plo) * E.sfloor := mul_nonneg hC hb.1
  have hCb1 : (E.c - E.plo) * E.sfloor ≤ E.c - E.plo := mul_le_of_le_one_right hC hb.2
  have h3 := mul_le_mul_of_nonneg_left hgD hβdlo
  have h4 : E.β_T * E.dlo * (E.KTrel * (1 - E.β_T * E.glo))
      ≤ E.β_T * E.dhi * (E.KTrel * (1 - E.β_T * E.glo)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left E.hdlo_dhi hβ0.le)
      (mul_nonneg hKnn hD1.le)
  have h5 : E.β_T * E.dlo * ((E.c - E.plo) * E.sfloor)
      ≤ (1 - E.β_T * E.glo) * (E.c - E.plo) :=
    calc E.β_T * E.dlo * ((E.c - E.plo) * E.sfloor)
        ≤ (1 - E.β_T * E.glo) * ((E.c - E.plo) * E.sfloor) :=
          mul_le_mul_of_nonneg_right hβd hCb
      _ ≤ (1 - E.β_T * E.glo) * (E.c - E.plo) := mul_le_mul_of_nonneg_left hCb1 hD1.le
  have key : E.β_T * E.dlo * E.gT ≤ E.β_T * E.dhi * E.KTrel + (E.c - E.plo) := by
    have h6 : E.β_T * E.dlo * E.gT * (1 - E.β_T * E.glo)
        ≤ (E.β_T * E.dhi * E.KTrel + (E.c - E.plo)) * (1 - E.β_T * E.glo) :=
      calc E.β_T * E.dlo * E.gT * (1 - E.β_T * E.glo)
          = E.β_T * E.dlo * (E.gT * (1 - E.β_T * E.glo)) := by ring
        _ ≤ E.β_T * E.dlo * (E.KTrel * (1 - E.β_T * E.glo) + (E.c - E.plo) * E.sfloor) := h3
        _ = E.β_T * E.dlo * (E.KTrel * (1 - E.β_T * E.glo))
              + E.β_T * E.dlo * ((E.c - E.plo) * E.sfloor) := by ring
        _ ≤ E.β_T * E.dhi * (E.KTrel * (1 - E.β_T * E.glo))
              + (1 - E.β_T * E.glo) * (E.c - E.plo) := add_le_add h4 h5
        _ = (E.β_T * E.dhi * E.KTrel + (E.c - E.plo)) * (1 - E.β_T * E.glo) := by ring
    exact le_of_mul_le_mul_right h6 hD1
  -- `ℓ_lo μ/k_hi ≤ ℓ_hi M_tot/k_lo`
  have hk := E.hklo
  have hkh := E.khi_pos
  have hμ := E.mu_pos
  have hXY : E.ℓlo * E.mu / E.khi ≤ E.ℓhi * E.Mtot / E.klo := by
    rw [div_le_div_iff₀ hkh hk]
    have e1 : E.ℓlo * E.mu ≤ E.ℓhi * E.Mtot :=
      mul_le_mul E.ℓlo_le_ℓhi E.mu_le_Mtot hμ.le E.ℓhi_pos.le
    have e3 : 0 ≤ E.ℓlo * E.mu := mul_nonneg E.hℓlo.le hμ.le
    calc E.ℓlo * E.mu * E.klo ≤ E.ℓlo * E.mu * E.khi :=
          mul_le_mul_of_nonneg_left E.klo_le_khi e3
      _ ≤ E.ℓhi * E.Mtot * E.khi := mul_le_mul_of_nonneg_right e1 hkh.le
  -- the relief-existence side: `ℓ_hi M_tot/k_lo < p_lo − β_T d_hi K_T^rel`
  have hY : E.ℓhi * E.Mtot / E.klo < E.plo - E.β_T * E.dhi * E.KTrel := by
    rw [div_lt_iff₀ hk]; linarith
  linarith

/-- **Certified defiance is inherited by a more patient Target**: across economies
that differ only in `β_T`, a slope `g ≥ 0` that satisfies the balance inequality
and the sharp inequality at `β_T` satisfies both at every larger `β_T`. The
balance inequality's left side falls with `β_T` (both `g (1 − β_T g_lo)` and the
pain term do) and the sharp side's right side rises; the Sender's data, and so
`μ`, `L_resp` and the monotone response, do not depend on `β_T`. So the certified
defiance region is an upper set of discount factors. -/
theorem certified_sharp_mono_βT {E₁ E₂ : ChordEconomyCs} (h : SameButβT E₁ E₂)
    (hβ : E₁.β_T ≤ E₂.β_T) {g : ℝ} (hg : 0 ≤ g)
    (hginv : g * (1 - E₁.β_T * E₁.glo) + max 0 (E₁.c - E₁.β_T * E₁.dlo * g) * (E₁.Lresp / E₁.mu)
      ≤ E₁.vlo + E₁.nlo * E₁.sfloor)
    (hsharp : E₁.c - E₁.ℓlo * E₁.mu / E₁.khi < E₁.β_T * E₁.dlo * g) :
    (g * (1 - E₂.β_T * E₂.glo) + max 0 (E₂.c - E₂.β_T * E₂.dlo * g) * (E₂.Lresp / E₂.mu)
      ≤ E₂.vlo + E₂.nlo * E₂.sfloor)
    ∧ (E₂.c - E₂.ℓlo * E₂.mu / E₂.khi < E₂.β_T * E₂.dlo * g) := by
  have hc := h.consts
  obtain ⟨-, -, -, -, hglo, -, hdlo, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hℓlo, hkhi,
    hcc, -, hvlo, hnlo, -, -, -⟩ := h
  have hmu : E₁.mu = E₂.mu := hc.2.1
  have hL : E₁.Lresp = E₂.Lresp := hc.2.2.2.1
  have hsf : E₁.sfloor = E₂.sfloor := hc.2.2.2.2.2.2.2.2
  rw [hglo, hdlo, hcc, hvlo, hnlo, hL, hmu, hsf] at hginv
  rw [hdlo, hcc, hℓlo, hmu, hkhi] at hsharp
  have hglo0 := E₂.hglo0
  have hdlo0 := E₂.hdlo0.le
  have hLμ : 0 ≤ E₂.Lresp / E₂.mu := div_nonneg E₂.Lresp_nonneg E₂.mu_pos.le
  -- the balance's left side falls with `β_T`
  have h1 : g * (1 - E₂.β_T * E₂.glo) ≤ g * (1 - E₁.β_T * E₂.glo) := by
    apply mul_le_mul_of_nonneg_left _ hg
    have := mul_le_mul_of_nonneg_right hβ hglo0
    linarith
  have hdg : E₁.β_T * E₂.dlo * g ≤ E₂.β_T * E₂.dlo * g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβ hdlo0) hg
  have h2 : max 0 (E₂.c - E₂.β_T * E₂.dlo * g) ≤ max 0 (E₂.c - E₁.β_T * E₂.dlo * g) :=
    max_le_max le_rfl (by linarith)
  have h3 := mul_le_mul_of_nonneg_right h2 hLμ
  refine ⟨by linarith, by linarith⟩

/-- **The collapse, solved for `β_T`**: under the sixteen tightness equalities of
`collapse_sides`, the sharp defiance side at `g_T` holds exactly above
`β_T* = D/(δ v + (1 − δ) D)` and both relief sides exactly below it, with
`D = c − ℓ_lo q/k_hi > 0` (the stage relief margin `hSR` at tight rates; a
hypothesis since round BC, when the margin stopped being a field) and
`δ = d_lo`. The step from `collapse_sides` is algebra, through
`g_lo = 1 − d_lo` (`glo_add_dlo_eq_one_of_tight`). Rule 22: affine-restricted by
its hypotheses, like `collapse_sides`. A conditional equivalence: it does not say
the equalities are necessary for the window to close. -/
theorem collapse_threshold (hSR : E.StageRelief) (hr : E.rhi = 0) (hSigV : E.SigV = 0)
    (hMs : E.Ms = 0)
    (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMcs : E.Mcs = 0) (hMmix : E.Mmix = 0)
    (hQ : E.Qbar = E.q) (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c)
    (hv : E.vlo = E.vhi) (hnlo : E.nlo = 0) (hnhi : E.nhi = 0) (hg : E.glo = E.ghi)
    (hd : E.dlo = E.dhi) :
    ((E.c - E.ℓlo * E.mu / E.khi < E.β_T * E.dlo * E.gT) ↔ E.betaStar < E.β_T)
    ∧ ((E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KTrel)) ↔ E.β_T < E.betaStar)
    ∧ ((E.ℓhi * E.Mtot < E.klo * (E.plo - E.β_T * E.dhi * E.KT)) ↔ E.β_T < E.betaStar) := by
  obtain ⟨h1, h2, h3⟩ := E.collapse_sides hr hSigV hMs hτ hMcx hMcs hMmix hQ hk hℓ hp hv
    hnlo hnhi hg hd
  set D := E.c - E.ℓlo * E.q / E.khi with hDdef
  have hkh := E.khi_pos
  -- `D > 0`: the stage relief margin at tight rates
  have hD : 0 < D := by
    have hsr : E.StageRelief := hSR
    unfold ChordEconomyRelief.StageRelief at hsr
    rw [hQ, hk, ← hℓ, hp] at hsr
    rw [hDdef, sub_pos, div_lt_iff₀ hkh]
    linarith
  -- at the collapse the Target slope is `g_T = v_lo/(1 − β_T (1 − d_lo))`
  have hsum := E.glo_add_dlo_eq_one_of_tight hg hd
  have hglo : E.glo = 1 - E.dlo := by linarith
  have hβ0 := E.hβT0
  have hβ1 := E.hβT1
  have hd0 := E.hdlo0
  have hd1 : E.dlo ≤ 1 := by linarith [E.hglo0]
  have hv0 := E.hvlo
  have hden : 0 < 1 - E.β_T * (1 - E.dlo) := by nlinarith
  have hgT : E.gT = E.vlo / (1 - E.β_T * (1 - E.dlo)) := by
    unfold gT; rw [hnlo, hglo]; ring
  have hP : 0 < E.dlo * E.vlo + (1 - E.dlo) * D := by
    have := mul_pos hd0 hv0
    have := mul_nonneg (sub_nonneg.mpr hd1) hD.le
    linarith
  have hsplit : E.β_T * E.dlo * (E.vlo / (1 - E.β_T * (1 - E.dlo)))
      = E.β_T * E.dlo * E.vlo / (1 - E.β_T * (1 - E.dlo)) := by ring
  have key1 : (D < E.β_T * E.dlo * E.gT) ↔ E.betaStar < E.β_T := by
    unfold betaStar
    rw [← hDdef, hgT, div_lt_iff₀ hP, hsplit, lt_div_iff₀ hden]
    constructor <;> intro h <;> linarith
  have key2 : (E.β_T * E.dlo * E.gT < D) ↔ E.β_T < E.betaStar := by
    unfold betaStar
    rw [← hDdef, hgT, lt_div_iff₀ hP, hsplit, div_lt_iff₀ hden]
    constructor <;> intro h <;> linarith
  exact ⟨h1.trans key1, h2.trans key2, h3.trans key2⟩

end ChordEconomyCs

end

#print axioms Sanctions.Examples.ChordEconomy.nonplacable_floor_of_lowerAppetite
#print axioms Sanctions.Examples.ChordEconomy.lowerAppetite_lt_of_βS_lt
#print axioms Sanctions.Examples.ChordEconomyCs.sharp_side_mono_nlo
#print axioms Sanctions.Examples.ChordEconomyCs.relief_side_anti_plo
#print axioms Sanctions.Examples.ChordEconomyCs.relief_side_notdef_anti
#print axioms Sanctions.Examples.ChordEconomy.sharpSideSet_isOpen
#print axioms Sanctions.Examples.ChordEconomyCs.reliefSideSet_isOpen
#print axioms Sanctions.Examples.ChordEconomyCs.bracket_existence_sides_disjoint
#print axioms Sanctions.Examples.ChordEconomy.A_lt_of_βS_lt
#print axioms Sanctions.Examples.ChordEconomyRelief.sharp_gT_of_sharp_of_balance
#print axioms Sanctions.Examples.ChordEconomyCs.collapse_threshold
#print axioms Sanctions.Examples.ChordEconomyCs.certified_sharp_mono_βT
#print axioms Sanctions.Examples.ChordEconomyTwoSided.gT_balance_of_Lresp_eq_zero

end Examples
end Sanctions
