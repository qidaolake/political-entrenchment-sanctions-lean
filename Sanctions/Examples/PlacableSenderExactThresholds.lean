/-
Sanctions/Examples/PlacableSenderExactThresholds.lean

**Exact thresholds in the Target's discount factor, general in `F`** (round BF, 2026-10-03;
on the author's word: "I still want the general abstract version of the theorems we just
prove, and the affine one only as an example of it", with the new hypothesis of item 2
approved the same day).

Across the members `E.withβT b` of an enriched chord economy that differ only in the Target's
discount factor:

1. **The exact relief test** (`exists_relief_equilibrium_iff`). Under interiority, placability
   and zero-sanction neutrality, a top-selector equilibrium whose realised sanction is zero at
   every state exists if and only if the zero level is a Target best reply at the relief
   values (`ReliefBestReply`). The bracket's relief certificate is one sufficient condition for
   the test; the test itself is exact. It mirrors `exists_defiance_equilibrium_iff`.
2. **A monotone relief value** (`VTrel_monotone`). If the state's lower rate at zero sanction
   covers the compliance cost along the zero level, `ℓ_hi·L_α ≤ v_lo`, the relief value is
   nondecreasing in the state. The condition does not involve `β_T`.
3. **A less patient Target keeps relief** (`reliefBestReply_anti_βT`). With a monotone relief
   value at one of two members, the relief best reply at the more patient member holds at the
   less patient one.
4. **Closure** (`reliefBestReply_of_tendsto`, `reliefExistence_sSup_mem`). The relief best reply
   passes to the limit in `β_T`, so the existence set contains its supremum when that is
   below one.
5. **The two intervals** (`reliefExistenceSet_eq_Ioc`, `defianceExistenceSet_eq_Ico`). Under
   `ℓ_hi·L_α ≤ v_lo` the discounts with a zero-rule equilibrium form an interval `(0, β_R]`.
   Under a monotone response at full defiance and the weak balance
   `c·L_resp/μ ≤ v_lo + n_lo·σ(0,0)` the discounts with a full-defiance equilibrium form
   `[β_D, 1)`. Neither interval is claimed to lie below the other.
6. **A general bound** (`reliefExistence_lt_margin`). Every discount with a zero-rule
   equilibrium lies below the loss-offset patience bound `c/(d_lo·v_lo + c·g_lo)`.

Renovation items BG3.1 and BG3.5(b) (2026-10-06). The two interval theorems of item 5 no
longer assume their sets nonempty: an empty relief set has supremum `0` and equals
`(0, 0]`, and a positive infimum of the defiance set already makes it nonempty. The bracket's
relief certificate with `≤` in place of `<` gives the relief best reply of item 1
(`reliefBestReply_of_relief_side_le`).

Renovation item BH3.7 (2026-10-06). The defiance half of item 5 is stated on the relief
extension (`ChordEconomyRelief.defianceExistence_upper`,
`ChordEconomyRelief.defianceExistenceSet_eq_Ico`), over the base family set
`ChordEconomy.defianceExistenceSet`: the enriched subclass's sanction-section semiconvexity
(T6) is not read there. The enriched names stay as one-line corollaries. The relief half,
items 1–4 and 6 stay on `ChordEconomyCs`: the relief interval's condition `ℓ_hi·L_α ≤ v_lo`
reads the enriched constant `M_cs` (through `L_α` and `M_tot`).

The affine member is an instance (`AffineWindowInstance.lean`): there `β_R = 36/197` and
`β_D = (82 − 7√2)/394`.

**Rule 3.** One new theorem-level hypothesis, `ℓ_hi·L_α ≤ v_lo`, approved by the author on
2026-10-03. It reads existing constants only and is discharged at the affine member
(`5/23 ≤ 30`). Items 1, 3 and 4 read nothing beyond the class and its relief hypotheses.
**Rule 22.** General in `F`. **Rule 9.** No witness is involved.
-/
import Sanctions.Examples.PlacableSenderReliefUniqueness
import Sanctions.Examples.PlacableSenderDefianceClosed
import Sanctions.Examples.PlacableSenderDefianceCore

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

/-! ## 0. Solutions of `V = h + β·V∘z` depend continuously on `β` -/

/-- **The discounted fixed point is continuous in the discount factor.** Let bounded
continuous values `V` and `Vₙ` on the state set solve `V = h + β·V∘z` and
`Vₙ = h + βₙ·Vₙ∘z` along a common map `z`, with `0 ≤ βₙ < 1`, `β < 1` and `βₙ → β`. Then
`βₙ·Vₙ(y) → β·V(y)` at every state, since `(1 − βₙ)‖Vₙ − V‖ ≤ |βₙ − β|·‖V‖`. -/
theorem tendsto_mul_of_solves {h : ↥(Sanctions.S : Set ℝ) → ℝ}
    {z : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.S : Set ℝ)} {V : ChordEconomy.Val}
    {Vs : ℕ → ChordEconomy.Val} {β : ℝ} {βs : ℕ → ℝ} (hβ1 : β < 1)
    (hβs0 : ∀ n, 0 ≤ βs n) (hβs1 : ∀ n, βs n < 1) (hlim : Tendsto βs atTop (𝓝 β))
    (hV : ∀ y, V y = h y + β * V (z y)) (hVs : ∀ n y, Vs n y = h y + βs n * Vs n (z y))
    (y : ↥(Sanctions.S : Set ℝ)) :
    Tendsto (fun n => βs n * Vs n y) atTop (𝓝 (β * V y)) := by
  have hdist : ∀ n, (1 - βs n) * ‖Vs n - V‖ ≤ |βs n - β| * ‖V‖ := by
    intro n
    set d := ‖Vs n - V‖ with hd
    have hpt : ∀ w, |Vs n w - V w| ≤ βs n * d + |βs n - β| * ‖V‖ := by
      intro w
      have e : Vs n w - V w = βs n * (Vs n (z w) - V (z w)) + (βs n - β) * V (z w) := by
        rw [hVs n w, hV w]; ring
      rw [e]
      have h1 : |Vs n (z w) - V (z w)| ≤ d := by
        have := BoundedContinuousFunction.norm_coe_le_norm (Vs n - V) (z w)
        rw [Real.norm_eq_abs] at this
        simpa using this
      have h2 : |V (z w)| ≤ ‖V‖ := by
        have := BoundedContinuousFunction.norm_coe_le_norm V (z w)
        rwa [Real.norm_eq_abs] at this
      calc |βs n * (Vs n (z w) - V (z w)) + (βs n - β) * V (z w)|
          ≤ |βs n * (Vs n (z w) - V (z w))| + |(βs n - β) * V (z w)| := abs_add_le _ _
        _ = βs n * |Vs n (z w) - V (z w)| + |βs n - β| * |V (z w)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (hβs0 n)]
        _ ≤ βs n * d + |βs n - β| * ‖V‖ := by
            gcongr
            exact hβs0 n
    have hnorm : d ≤ βs n * d + |βs n - β| * ‖V‖ := by
      have h0 : 0 ≤ βs n * d + |βs n - β| * ‖V‖ := by
        have := hβs0 n
        positivity
      refine (BoundedContinuousFunction.norm_le h0).2 (fun w => ?_)
      rw [Real.norm_eq_abs]
      simpa using hpt w
    linarith
  have hevent : ∀ᶠ n in atTop, βs n < (1 + β) / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have hb0 : Tendsto (fun n => |βs n - β|) atTop (𝓝 0) := by
    have := (tendsto_sub_nhds_zero_iff.mpr hlim).abs
    simpa using this
  set C := ‖V‖ * (2 / (1 - β) + 1) with hC
  have hg : Tendsto (fun n => |βs n - β| * C) atTop (𝓝 0) := by
    simpa using hb0.mul_const C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hg
  filter_upwards [hevent] with n hn
  rw [Real.norm_eq_abs]
  have hd := hdist n
  have hpos : (1 - β) / 2 ≤ 1 - βs n := by linarith
  have hdn : ‖Vs n - V‖ ≤ |βs n - β| * ‖V‖ * (2 / (1 - β)) := by
    have hA : 0 ≤ ‖Vs n - V‖ := norm_nonneg _
    have hden : 0 < 1 - β := by linarith
    rw [mul_div_assoc', le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_right hpos hA]
  have hy1 : |Vs n y - V y| ≤ ‖Vs n - V‖ := by
    have := BoundedContinuousFunction.norm_coe_le_norm (Vs n - V) y
    rw [Real.norm_eq_abs] at this
    simpa using this
  have hy2 : |V y| ≤ ‖V‖ := by
    have := BoundedContinuousFunction.norm_coe_le_norm V y
    rwa [Real.norm_eq_abs] at this
  have e : βs n * Vs n y - β * V y = βs n * (Vs n y - V y) + (βs n - β) * V y := by ring
  rw [e]
  calc |βs n * (Vs n y - V y) + (βs n - β) * V y|
      ≤ βs n * |Vs n y - V y| + |βs n - β| * |V y| := by
        calc _ ≤ |βs n * (Vs n y - V y)| + |(βs n - β) * V y| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (hβs0 n)]
    _ ≤ 1 * ‖Vs n - V‖ + |βs n - β| * ‖V‖ := by
        gcongr
        · exact (hβs1 n).le
    _ ≤ |βs n - β| * C := by
        rw [hC]; nlinarith [hdn, abs_nonneg (βs n - β), norm_nonneg V]

/-! ## The defiance interval on the relief extension (renovation item BH3.7) -/

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The defiance existence set is an upper set** in `(0,1)` under a monotone response at
full defiance and the weak balance `c·L_resp/μ ≤ v_lo + n_lo·σ(0,0)`, both free of `β_T`.
Stated on the relief extension over the base family set (renovation item BH3.7,
2026-10-06); the enriched form `ChordEconomyCs.defianceExistence_upper`, which also carried
the sanction-section semiconvexity (T6), is now its corollary. The relief rates enter only
through the weak balance, which makes the defiance-profile Target value monotone at the less
patient member (`VTdef_monotone_of_weak_hvL`). General in `F`. -/
theorem defianceExistence_upper (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hvL : E.c * (E.Lresp / E.mu) ≤ E.vlo + E.nlo * E.sfloor) {b₁ b₂ : ℝ} (hb : b₁ ≤ b₂)
    (h₂1 : b₂ < 1) (h₁ : b₁ ∈ E.defianceExistenceSet) : b₂ ∈ E.defianceExistenceSet := by
  obtain ⟨⟨h₁0, h₁1⟩, hex⟩ := h₁
  have h₂0 : 0 < b₂ := lt_of_lt_of_le h₁0 hb
  exact ⟨⟨h₂0, h₂1⟩, ChordEconomy.exists_defiance_equilibrium_mono_βT_of_monotone
    (E.toChordEconomy.withβT_sameGame h₁0 h₁1 h₂0 h₂1) hb hmono
    (Or.inl ((E.withβT b₁ h₁0 h₁1).VTdef_monotone_of_weak_hvL hmono hvL))
    hex⟩

/-- **The defiance existence set is an interval `[β_D, 1)`.** Under a monotone response at full
defiance and the weak balance, if the infimum `β_D` of the discounts that admit a
full-defiance equilibrium is positive, the set is exactly `[β_D, 1)`
(`ChordEconomy.defianceExistence_sInf_mem` for the lower end). The set is not assumed
nonempty (renovation item BG3.1): `sInf ∅ = 0`, so a positive infimum already makes it
nonempty. Stated on the relief extension (renovation item BH3.7, 2026-10-06): the enriched
subclass's sanction-section semiconvexity (T6), carried by the earlier statement on
`ChordEconomyCs`, is dropped; it was never read. General in `F`. -/
theorem defianceExistenceSet_eq_Ico (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hvL : E.c * (E.Lresp / E.mu) ≤ E.vlo + E.nlo * E.sfloor)
    (hpos : 0 < sInf E.defianceExistenceSet) :
    E.defianceExistenceSet = Ico (sInf E.defianceExistenceSet) 1 := by
  have hbdd : BddBelow E.defianceExistenceSet := ⟨0, fun b hb => hb.choose.1.le⟩
  have hmem := E.defianceExistence_sInf_mem hpos
  ext b
  constructor
  · intro hb
    exact ⟨csInf_le hbdd hb, hb.choose.2⟩
  · rintro ⟨hb, hb1⟩
    exact E.defianceExistence_upper hmono hvL hb hb1 hmem

end ChordEconomyRelief

namespace ChordEconomyCs

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyCs)

/-! ## 1. The exact test for the relief equilibrium -/

/-- **Relief as a Target best reply at the relief values**: at every feasible state the zero
level maximises the Target's objective against the Sender's top response, when the Sender's
value is the zero-sanction value `VS01` and the Target's continuation value is the relief
value `VTrel`. Written over those constructed values (Rule 14). -/
def ReliefBestReply (hInt : E.Interior) (hP : E.Placable) : Prop :=
  ∀ x ∈ Sanctions.I, IsMaxOn
    (fun a => E.toParams.joint_T_top_integrand (E.VTrel hInt hP) E.VS01 x a) Sanctions.I
    (E.zeroLevel x)

/-- **The relief equilibrium, built from the best-reply test.** The Sender value is `VS01`,
the Target value `VTrel`, the policy the zero level; the best-reply test replaces the bracket's
relief certificate in `reliefEquilibriumTop`. -/
def reliefEquilibriumOfBestReply (hInt : E.Interior) (hP : E.Placable)
    (hN : E.ZeroSanctionNeutral) (h : E.ReliefBestReply hInt hP) :
    E.toParams.FeedbackStackelbergEquilibriumTop where
  V_T := E.VTrel hInt hP
  V_S := E.VS01
  α := E.α01
  hα := E.α01_continuous hInt hP
  α_mem := fun x _ => E.α01_mem hP x
  V_S_fix := by
    ext y
    change E.VS01 y = sSup ((fun s => E.toParams.integrandS E.α01 (fun z => E.VS01 z)
      (y.val, s)) '' Sanctions.I)
    have hα : E.α01 y.val = E.zeroLevel y.val := E.α01_eq y.property
    have hgt : IsGreatest ((fun s => E.toParams.integrandS E.α01 (fun z => E.VS01 z)
        (y.val, s)) '' Sanctions.I)
        (E.senderObj E.VS01 y.val (E.α01 y.val) (E.response E.VS01 y.val (E.α01 y.val))) := by
      refine ⟨⟨_, E.response_mem E.VS01 y.val (E.α01 y.val), rfl⟩, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      exact E.response_isMaxOn E.VS01 y.val (E.α01 y.val) hs
    rw [hgt.csSup_eq, hα, E.ρ01_zeroLevel hP y.property]
    have hfix := congrArg (fun V : Val => V y) E.VS01_fix
    simp only at hfix
    rw [relaxOp_apply] at hfix
    unfold senderObj
    rw [hN y.val y.property (E.zeroLevel y.val) ((E.zeroLevel_mem hP) y.property)]
    exact hfix.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest
        ((fun a => E.toParams.joint_T_top_integrand (E.VTrel hInt hP) E.VS01 y.val a) ''
            Sanctions.I)
        (E.toParams.joint_T_top_integrand (E.VTrel hInt hP) E.VS01 y.val (E.zeroLevel y.val)) := by
      refine ⟨⟨_, E.zeroLevel_mem hP y.property, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      exact h y.val y.property ha
    rw [hgt.csSup_eq, E.joint_T_top_integrand_eq E.VS01_mem _ y.property,
      joint_T_integrand_eq, E.ρ01_zeroLevel hP y.property]
    have hfix := congrArg (fun V : Val => V y) (E.VTrel_fix hInt hP)
    simp only at hfix
    rw [reliefOp_apply] at hfix
    exact hfix.symm
  α_opt_top := by
    intro x hx
    rw [E.α01_eq hx]
    exact h x hx

/-- The realised sanction of the relief equilibrium is zero at every feasible state. -/
theorem reliefEquilibriumOfBestReply_rule (hInt : E.Interior) (hP : E.Placable)
    (hN : E.ZeroSanctionNeutral) (h : E.ReliefBestReply hInt hP) {x : ℝ}
    (hx : x ∈ Sanctions.I) :
    E.toParams.dynamicEquilibriumRule (E.reliefEquilibriumOfBestReply hInt hP hN h) x = 0 := by
  change E.toParams.σ_dyn_top E.VS01 x (E.α01 x) = 0
  rw [E.α01_eq hx, ← E.response_eq_top E.VS01_mem hx]
  exact E.ρ01_zeroLevel hP hx

/-- **The exact relief test.** Under interiority, placability and zero-sanction neutrality, a
top-selector equilibrium whose realised sanction is zero at every feasible state exists if and
only if the zero level is a Target best reply at the relief values. Forward: such an
equilibrium is the relief equilibrium (`relief_equilibrium_of_zero_rule`), and its policy is a
best reply there. Backward: `reliefEquilibriumOfBestReply`. General in `F`. -/
theorem exists_relief_equilibrium_iff (hInt : E.Interior) (hP : E.Placable)
    (hN : E.ZeroSanctionNeutral) :
    (∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, E.toParams.dynamicEquilibriumRule Eq x = 0)
      ↔ E.ReliefBestReply hInt hP := by
  constructor
  · rintro ⟨Eq, hzero⟩ x hx
    obtain ⟨hα, hV, hT⟩ := E.relief_equilibrium_of_zero_rule hInt hP hN Eq hzero
    have h := Eq.α_opt_top x hx
    rw [hα x hx, hV, hT] at h
    exact h
  · intro h
    exact ⟨E.reliefEquilibriumOfBestReply hInt hP hN h,
      fun x hx => E.reliefEquilibriumOfBestReply_rule hInt hP hN h hx⟩

/-- **The weak relief side gives the relief best reply** (renovation item BG3.5(b),
2026-10-06). Under interiority and placability, if
`ℓ_hi·M_tot ≤ k_lo(p_lo − β_T d_hi K_T^rel)` (the bracket's relief certificate with `≤` in
place of `<`), the zero level is a Target best reply at the relief values at every state
(`zeroLevel_isMaxOn_rel`). With zero-sanction neutrality, `exists_relief_equilibrium_iff`
then gives an equilibrium with zero sanctions at every state. In words: relief exists as
soon as closing the gap to the zero level is worth at least its compliance cost; the strict
certificate is needed only to make the zero level the unique reply. General in `F`. -/
theorem reliefBestReply_of_relief_side_le (hInt : E.Interior) (hP : E.Placable)
    (hrel : E.ℓhi * E.Mtot ≤ E.klo * (E.plo - E.β_T * E.dhi * E.KTrel)) :
    E.ReliefBestReply hInt hP := by
  intro x hx
  rw [isMaxOn_iff]
  intro a ha
  rw [E.joint_T_top_integrand_eq E.VS01_mem _ hx, E.joint_T_top_integrand_eq E.VS01_mem _ hx]
  exact E.zeroLevel_isMaxOn_rel hInt hP hrel hx ha

/-! ## 2. A monotone relief value -/

/-- **The relief value is nondecreasing in the state** when the state's lower rate at zero
sanction covers the compliance cost along the zero level, `ℓ_hi·L_α ≤ v_lo`. Along the zero
level the stage payoff then rises with the state (the state's lower rate at `s = 0`, the
compliance cost's upper rate and the zero level's `L_α`-Lipschitz bound), and the monotone cone
is closed under the relief operator. The condition does not involve `β_T`. -/
theorem VTrel_monotone (hInt : E.Interior) (hP : E.Placable) (hvL : E.ℓhi * E.Lalpha ≤ E.vlo) :
    Monotone (E.VTrel hInt hP : ↥(Sanctions.S : Set ℝ) → ℝ) := by
  refine Foundations.DiscountedExtremum.monotone_of_eq_add_mul_comp
    (h := fun y : ↥(Sanctions.S : Set ℝ) => E.toParams.U_T y.val (E.zeroLevel y.val) 0)
    (z := fun y : ↥(Sanctions.S : Set ℝ) => Sanctions.clipS' (E.toParams.F y.val 0))
    E.hβT0.le E.hβT1 (M := ‖E.VTrel hInt hP‖) (fun y => ?_) ?_ ?_ (fun y => ?_)
  · have := BoundedContinuousFunction.norm_coe_le_norm (E.VTrel hInt hP) y
    rwa [Real.norm_eq_abs] at this
  · intro y₁ y₂ hle
    have hle' : y₁.val ≤ y₂.val := hle
    have hz₁ := E.zeroLevel_mem hP y₁.property
    have hz₂ := E.zeroLevel_mem hP y₂.property
    have h1 := E.UT_compliance_lip y₂.property hz₁ hz₂ zero_mem_I
    have h2 := E.hUT_stateLo (E.zeroLevel y₁.val) hz₁ 0 zero_mem_I y₁.val y₁.property y₂.val
      y₂.property hle'
    simp only [mul_zero, add_zero] at h2
    have hz := E.zeroLevel_lipschitz hInt hP y₂.property y₁.property
    rw [abs_of_nonneg (sub_nonneg.mpr hle')] at hz
    have h3 : E.ℓhi * |E.zeroLevel y₂.val - E.zeroLevel y₁.val|
        ≤ E.ℓhi * (E.Lalpha * (y₂.val - y₁.val)) :=
      mul_le_mul_of_nonneg_left hz E.ℓhi_pos.le
    have h4 : E.ℓhi * E.Lalpha * (y₂.val - y₁.val) ≤ E.vlo * (y₂.val - y₁.val) :=
      mul_le_mul_of_nonneg_right hvL (sub_nonneg.mpr hle')
    have h1' := (abs_le.mp h1).1
    change E.U_T y₁.val (E.zeroLevel y₁.val) 0 ≤ E.U_T y₂.val (E.zeroLevel y₂.val) 0
    nlinarith [h1', h2, h3, h4]
  · intro y₁ y₂ hle
    have hle' : y₁.val ≤ y₂.val := hle
    exact Sanctions.clipS'_mono (E.F_mono_x 0 hle')
  · have hfix := congrArg (fun V : Val => V y) (E.VTrel_fix hInt hP)
    simp only at hfix
    rw [reliefOp_apply] at hfix
    exact hfix.symm

/-! ## 3. The family `E.withβT`, in the base economy's terms -/

/-- Along the common relief path, the relief value of the member at `b` solves
`V = u + b·V∘z`, with the stage `u` and the path `z` of the base economy. -/
theorem withβT_VTrel_eq (hInt : E.Interior) (hP : E.Placable) {b : ℝ} (h0 : 0 < b)
    (h1 : b < 1) (y : ↥(Sanctions.S : Set ℝ)) :
    (E.withβT b h0 h1).VTrel hInt hP y
      = E.toParams.U_T y.val (E.zeroLevel y.val) 0
        + b * (E.withβT b h0 h1).VTrel hInt hP (Sanctions.clipS' (E.toParams.F y.val 0)) := by
  have hfix := congrArg (fun V : Val => V y) ((E.withβT b h0 h1).VTrel_fix hInt hP)
  simp only at hfix
  rw [reliefOp_apply] at hfix
  exact hfix.symm

/-- **The relief best reply at a family member, unfolded.** At the member at `b` the zero level
is a best reply iff, at every state and compliance, the stage payoff against the Sender's
response plus `b` times the member's relief value at the successor is at most its value at the
zero level, where the sanction is zero. Only `b` and the relief value depend on the member. -/
theorem withβT_reliefBestReply_iff (hInt : E.Interior) (hP : E.Placable) {b : ℝ} (h0 : 0 < b)
    (h1 : b < 1) :
    (E.withβT b h0 h1).ReliefBestReply hInt hP ↔
      ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        E.toParams.U_T x a (E.response E.VS01 x a)
            + b * (E.withβT b h0 h1).VTrel hInt hP
              (Sanctions.clipS' (E.toParams.F x (E.response E.VS01 x a)))
          ≤ E.toParams.U_T x (E.zeroLevel x) 0
            + b * (E.withβT b h0 h1).VTrel hInt hP (Sanctions.clipS' (E.toParams.F x 0)) := by
  have hj : ∀ x ∈ Sanctions.I, ∀ a : ℝ,
      (E.withβT b h0 h1).toParams.joint_T_top_integrand ((E.withβT b h0 h1).VTrel hInt hP)
          (E.withβT b h0 h1).VS01 x a
        = E.toParams.U_T x a (E.response E.VS01 x a)
          + b * (E.withβT b h0 h1).VTrel hInt hP
            (Sanctions.clipS' (E.toParams.F x (E.response E.VS01 x a))) :=
    fun x hx a => (E.withβT b h0 h1).joint_T_top_integrand_eq (E.withβT b h0 h1).VS01_mem _ hx a
  have hz : ∀ x ∈ Sanctions.I,
      (E.withβT b h0 h1).toParams.joint_T_top_integrand ((E.withβT b h0 h1).VTrel hInt hP)
          (E.withβT b h0 h1).VS01 x ((E.withβT b h0 h1).zeroLevel x)
        = E.toParams.U_T x (E.zeroLevel x) 0
          + b * (E.withβT b h0 h1).VTrel hInt hP (Sanctions.clipS' (E.toParams.F x 0)) := by
    intro x hx
    rw [hj x hx]
    have e : E.response E.VS01 x (E.zeroLevel x) = 0 := E.ρ01_zeroLevel hP hx
    change E.toParams.U_T x (E.zeroLevel x) (E.response E.VS01 x (E.zeroLevel x))
        + b * (E.withβT b h0 h1).VTrel hInt hP
          (Sanctions.clipS' (E.toParams.F x (E.response E.VS01 x (E.zeroLevel x)))) = _
    rw [e]
  constructor
  · intro h x hx a ha
    have h' := h x hx ha
    simp only [mem_setOf_eq] at h'
    rw [hj x hx, hz x hx] at h'
    exact h'
  · intro h x hx a ha
    simp only [mem_setOf_eq]
    rw [hj x hx, hz x hx]
    exact h x hx a ha

/-! ## 4. A less patient Target keeps the relief equilibrium -/

/-- **Relief as a best reply is inherited by a less patient Target.** In the family `E.withβT`,
with `b₁ ≤ b₂` and a monotone relief value at one of the two members: if the zero level is a
Target best reply at the relief values of the member at `b₂`, it is one at the member at
`b₁`. Along the common relief path `y ↦ F(y,0)` both relief values solve `Vᵢ = u + bᵢ·Vᵢ∘z`,
so `W = b₂V₂ − b₁V₁` is monotone (patience increasing differences). A compliance below the zero
level draws a sanction and raises the successor state, so its gain is smaller by
`W(z_a(x)) − W(z(x)) ≥ 0` at the less patient member; a compliance above it draws no sanction
and its gain does not depend on the discount. General in `F`. -/
theorem reliefBestReply_anti_βT (hInt : E.Interior) (hP : E.Placable) {b₁ b₂ : ℝ}
    (h₁0 : 0 < b₁) (h₁1 : b₁ < 1) (h₂0 : 0 < b₂) (h₂1 : b₂ < 1) (hb : b₁ ≤ b₂)
    (hV : Monotone ((E.withβT b₁ h₁0 h₁1).VTrel hInt hP : ↥(Sanctions.S : Set ℝ) → ℝ)
      ∨ Monotone ((E.withβT b₂ h₂0 h₂1).VTrel hInt hP : ↥(Sanctions.S : Set ℝ) → ℝ))
    (h₂ : (E.withβT b₂ h₂0 h₂1).ReliefBestReply hInt hP) :
    (E.withβT b₁ h₁0 h₁1).ReliefBestReply hInt hP := by
  rw [E.withβT_reliefBestReply_iff hInt hP h₁0 h₁1]
  rw [E.withβT_reliefBestReply_iff hInt hP h₂0 h₂1] at h₂
  have hzm : Monotone (fun y : ↥(Sanctions.S : Set ℝ) =>
      Sanctions.clipS' (E.toParams.F y.val 0)) := by
    intro y₁ y₂ hle
    have hle' : y₁.val ≤ y₂.val := hle
    exact Sanctions.clipS'_mono (E.F_mono_x 0 hle')
  have hb₁ : ∀ y : ↥(Sanctions.S : Set ℝ), |(E.withβT b₁ h₁0 h₁1).VTrel hInt hP y|
      ≤ ‖(E.withβT b₁ h₁0 h₁1).VTrel hInt hP‖ + ‖(E.withβT b₂ h₂0 h₂1).VTrel hInt hP‖ := by
    intro y
    have h1 := BoundedContinuousFunction.norm_coe_le_norm ((E.withβT b₁ h₁0 h₁1).VTrel hInt hP) y
    rw [Real.norm_eq_abs] at h1
    linarith [norm_nonneg ((E.withβT b₂ h₂0 h₂1).VTrel hInt hP)]
  have hb₂ : ∀ y : ↥(Sanctions.S : Set ℝ), |(E.withβT b₂ h₂0 h₂1).VTrel hInt hP y|
      ≤ ‖(E.withβT b₁ h₁0 h₁1).VTrel hInt hP‖ + ‖(E.withβT b₂ h₂0 h₂1).VTrel hInt hP‖ := by
    intro y
    have h1 := BoundedContinuousFunction.norm_coe_le_norm ((E.withβT b₂ h₂0 h₂1).VTrel hInt hP) y
    rw [Real.norm_eq_abs] at h1
    linarith [norm_nonneg ((E.withβT b₁ h₁0 h₁1).VTrel hInt hP)]
  have hW : Monotone (fun y : ↥(Sanctions.S : Set ℝ) =>
      b₂ * (E.withβT b₂ h₂0 h₂1).VTrel hInt hP y - b₁ * (E.withβT b₁ h₁0 h₁1).VTrel hInt hP y) := by
    rcases hV with hV | hV
    · exact Foundations.DiscountedExtremum.monotone_sub_of_solves_of_monotone_left h₁0.le hb h₂1
        hb₁ hb₂ hzm (E.withβT_VTrel_eq hInt hP h₁0 h₁1) (E.withβT_VTrel_eq hInt hP h₂0 h₂1) hV
    · exact Foundations.DiscountedExtremum.monotone_sub_of_solves_of_monotone_right h₁0.le hb h₂1
        hb₁ hb₂ hzm (E.withβT_VTrel_eq hInt hP h₁0 h₁1) (E.withβT_VTrel_eq hInt hP h₂0 h₂1) hV
  intro x hx a ha
  have h2 := h₂ x hx a ha
  have hsucc : Sanctions.clipS' (E.toParams.F x 0)
      ≤ Sanctions.clipS' (E.toParams.F x (E.response E.VS01 x a)) :=
    Sanctions.clipS'_mono (E.F_mono_s x (E.response_mem E.VS01 x a).1)
  have hWle := hW hsucc
  simp only at hWle
  linarith

/-! ## 5. The relief best reply passes to the limit in `β_T` -/

/-- **Relief as a best reply passes to the limit in `β_T`.** If the members at discounts
`u n → b` each have the zero level as a Target best reply at their relief values, so does the
member at `b`. The Sender's side does not depend on the discount, the relief values converge
(`tendsto_mul_of_solves`), and the weak best-reply inequalities pass to the limit. General in
`F`. -/
theorem reliefBestReply_of_tendsto (hInt : E.Interior) (hP : E.Placable) {b : ℝ} (h0 : 0 < b)
    (h1 : b < 1) (u : ℕ → ℝ) (hu0 : ∀ n, 0 < u n) (hu1 : ∀ n, u n < 1)
    (hlim : Tendsto u atTop (𝓝 b))
    (hbr : ∀ n, (E.withβT (u n) (hu0 n) (hu1 n)).ReliefBestReply hInt hP) :
    (E.withβT b h0 h1).ReliefBestReply hInt hP := by
  rw [E.withβT_reliefBestReply_iff hInt hP h0 h1]
  intro x hx a ha
  have hconv : ∀ y, Tendsto
      (fun n => u n * (E.withβT (u n) (hu0 n) (hu1 n)).VTrel hInt hP y) atTop
      (𝓝 (b * (E.withβT b h0 h1).VTrel hInt hP y)) :=
    tendsto_mul_of_solves h1 (fun n => (hu0 n).le) hu1 hlim
      (E.withβT_VTrel_eq hInt hP h0 h1) (fun n => E.withβT_VTrel_eq hInt hP (hu0 n) (hu1 n))
  have hn : ∀ n, E.toParams.U_T x a (E.response E.VS01 x a)
        + u n * (E.withβT (u n) (hu0 n) (hu1 n)).VTrel hInt hP
          (Sanctions.clipS' (E.toParams.F x (E.response E.VS01 x a)))
      ≤ E.toParams.U_T x (E.zeroLevel x) 0
        + u n * (E.withβT (u n) (hu0 n) (hu1 n)).VTrel hInt hP
          (Sanctions.clipS' (E.toParams.F x 0)) :=
    fun n => (E.withβT_reliefBestReply_iff hInt hP (hu0 n) (hu1 n)).1 (hbr n) x hx a ha
  exact le_of_tendsto_of_tendsto' (tendsto_const_nhds.add (hconv _))
    (tendsto_const_nhds.add (hconv _)) hn

/-! ## 6. The two existence sets are intervals -/

/-- The discounts in `(0,1)` at which the family member has a top-selector equilibrium whose
realised sanction is zero at every feasible state. -/
def reliefExistenceSet : Set ℝ :=
  {b | ∃ h : 0 < b ∧ b < 1,
    ∃ Eq : (E.withβT b h.1 h.2).toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, (E.withβT b h.1 h.2).toParams.dynamicEquilibriumRule Eq x = 0}

/-- Membership in the relief existence set is the relief best reply at the member. -/
theorem mem_reliefExistenceSet_iff (hInt : E.Interior) (hP : E.Placable)
    (hN : E.ZeroSanctionNeutral) {b : ℝ} (h0 : 0 < b) (h1 : b < 1) :
    b ∈ E.reliefExistenceSet ↔ (E.withβT b h0 h1).ReliefBestReply hInt hP := by
  constructor
  · rintro ⟨_, hex⟩
    exact ((E.withβT b h0 h1).exists_relief_equilibrium_iff hInt hP hN).1 hex
  · intro hbr
    exact ⟨⟨h0, h1⟩, ((E.withβT b h0 h1).exists_relief_equilibrium_iff hInt hP hN).2 hbr⟩

/-- **The relief existence set is a lower set** in `(0,1)` under `ℓ_hi·L_α ≤ v_lo`. -/
theorem reliefExistence_lower (hInt : E.Interior) (hP : E.Placable)
    (hN : E.ZeroSanctionNeutral) (hvL : E.ℓhi * E.Lalpha ≤ E.vlo) {b₁ b₂ : ℝ} (h₁0 : 0 < b₁)
    (hb : b₁ ≤ b₂) (h₂ : b₂ ∈ E.reliefExistenceSet) : b₁ ∈ E.reliefExistenceSet := by
  obtain ⟨h₂0, h₂1⟩ := h₂.choose
  have h₁1 : b₁ < 1 := lt_of_le_of_lt hb h₂1
  rw [E.mem_reliefExistenceSet_iff hInt hP hN h₁0 h₁1]
  exact E.reliefBestReply_anti_βT hInt hP h₁0 h₁1 h₂0 h₂1 hb
    (Or.inl ((E.withβT b₁ h₁0 h₁1).VTrel_monotone hInt hP hvL))
    ((E.mem_reliefExistenceSet_iff hInt hP hN h₂0 h₂1).1 h₂)

/-- **The upper end of the relief existence set is attained** when it is below one. -/
theorem reliefExistence_sSup_mem (hInt : E.Interior) (hP : E.Placable)
    (hN : E.ZeroSanctionNeutral) (hne : E.reliefExistenceSet.Nonempty)
    (hlt : sSup E.reliefExistenceSet < 1) : sSup E.reliefExistenceSet ∈ E.reliefExistenceSet := by
  have hbdd : BddAbove E.reliefExistenceSet := ⟨1, fun b hb => hb.choose.2.le⟩
  obtain ⟨b₀, hb₀⟩ := hne
  have hpos : 0 < sSup E.reliefExistenceSet :=
    lt_of_lt_of_le hb₀.choose.1 (le_csSup hbdd hb₀)
  obtain ⟨u, -, hu_lim, hu_mem⟩ := exists_seq_tendsto_sSup ⟨b₀, hb₀⟩ hbdd
  rw [E.mem_reliefExistenceSet_iff hInt hP hN hpos hlt]
  exact E.reliefBestReply_of_tendsto hInt hP hpos hlt u (fun n => (hu_mem n).choose.1)
    (fun n => (hu_mem n).choose.2) hu_lim
    (fun n => (E.mem_reliefExistenceSet_iff hInt hP hN (hu_mem n).choose.1
      (hu_mem n).choose.2).1 (hu_mem n))

/-- **The relief existence set is an interval `(0, β_R]`.** Under interiority, placability,
zero-sanction neutrality and `ℓ_hi·L_α ≤ v_lo`, if the supremum `β_R` of the discounts that
admit an equilibrium with zero sanctions at every state is below one, the set is exactly
`(0, β_R]`. The set is not assumed nonempty (renovation item BG3.1, 2026-10-06): if no
discount admits such an equilibrium, `β_R = sSup ∅ = 0` and `(0, 0]` is empty as well.
General in `F`. -/
theorem reliefExistenceSet_eq_Ioc (hInt : E.Interior) (hP : E.Placable)
    (hN : E.ZeroSanctionNeutral) (hvL : E.ℓhi * E.Lalpha ≤ E.vlo)
    (hlt : sSup E.reliefExistenceSet < 1) :
    E.reliefExistenceSet = Ioc 0 (sSup E.reliefExistenceSet) := by
  rcases E.reliefExistenceSet.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Real.sSup_empty, Ioc_self]
  have hbdd : BddAbove E.reliefExistenceSet := ⟨1, fun b hb => hb.choose.2.le⟩
  have hmem := E.reliefExistence_sSup_mem hInt hP hN hne hlt
  ext b
  constructor
  · intro hb
    exact ⟨hb.choose.1, le_csSup hbdd hb⟩
  · rintro ⟨hb0, hb⟩
    exact E.reliefExistence_lower hInt hP hN hvL hb0 hb hmem

/-- **The defiance existence set is an upper set** in `(0,1)` under a monotone response at
full defiance and the weak balance `c·L_resp/μ ≤ v_lo + n_lo·σ(0,0)`, both free of `β_T`. The
relief-extension theorem `ChordEconomyRelief.defianceExistence_upper` at
`E.toChordEconomyRelief`, kept under its old name (renovation item BH3.7, 2026-10-06): the
sanction-section semiconvexity (T6) of the enriched subclass is not read. General in `F`. -/
theorem defianceExistence_upper (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hvL : E.c * (E.Lresp / E.mu) ≤ E.vlo + E.nlo * E.sfloor) {b₁ b₂ : ℝ} (hb : b₁ ≤ b₂)
    (h₂1 : b₂ < 1) (h₁ : b₁ ∈ E.defianceExistenceSet) : b₂ ∈ E.defianceExistenceSet :=
  E.toChordEconomyRelief.defianceExistence_upper hmono hvL hb h₂1 h₁

/-- **The defiance existence set is an interval `[β_D, 1)`.** Under a monotone response at full
defiance and the weak balance, if the infimum `β_D` of the discounts that admit a
full-defiance equilibrium is positive, the set is exactly `[β_D, 1)`. The relief-extension
theorem `ChordEconomyRelief.defianceExistenceSet_eq_Ico` at `E.toChordEconomyRelief`, kept
under its old name (renovation item BH3.7, 2026-10-06): the sanction-section semiconvexity
(T6) of the enriched subclass is not read. The set is not assumed nonempty (renovation item
BG3.1). General in `F`. -/
theorem defianceExistenceSet_eq_Ico (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hvL : E.c * (E.Lresp / E.mu) ≤ E.vlo + E.nlo * E.sfloor)
    (hpos : 0 < sInf E.defianceExistenceSet) :
    E.defianceExistenceSet = Ico (sInf E.defianceExistenceSet) 1 :=
  E.toChordEconomyRelief.defianceExistenceSet_eq_Ico hmono hvL hpos

/-- **Relief lies below the loss-offset patience bound.** Every discount at which the family
member has an equilibrium with zero sanctions at every state is below
`c/(d_lo·v_lo + c·g_lo)`: at or above it the unrefined margin holds
(`lossOffset₀_iff_βT_ge`) and excludes such an equilibrium (`no_zero_rule_equilibrium`). -/
theorem reliefExistence_lt_margin {b : ℝ} (hb : b ∈ E.reliefExistenceSet) :
    b < E.c / (E.dlo * E.vlo + E.c * E.glo) := by
  obtain ⟨⟨h0, h1⟩, Eq, hzero⟩ := hb
  by_contra hcon
  have hge : E.c / (E.dlo * E.vlo + E.c * E.glo) ≤ b := not_lt.mp hcon
  have hTM : (E.withβT b h0 h1).LossOffset₀ :=
    ((E.withβT b h0 h1).toChordEconomyRelief.lossOffset₀_iff_βT_ge).2 hge
  exact (E.withβT b h0 h1).toChordEconomy.no_zero_rule_equilibrium hTM Eq hzero

end ChordEconomyCs

end

#print axioms Sanctions.Examples.ChordEconomyCs.exists_relief_equilibrium_iff
#print axioms Sanctions.Examples.ChordEconomyCs.reliefBestReply_of_relief_side_le
#print axioms Sanctions.Examples.ChordEconomyCs.VTrel_monotone
#print axioms Sanctions.Examples.ChordEconomyCs.reliefBestReply_anti_βT
#print axioms Sanctions.Examples.ChordEconomyCs.reliefBestReply_of_tendsto
#print axioms Sanctions.Examples.ChordEconomyCs.reliefExistenceSet_eq_Ioc
#print axioms Sanctions.Examples.ChordEconomyRelief.defianceExistence_upper
#print axioms Sanctions.Examples.ChordEconomyRelief.defianceExistenceSet_eq_Ico
#print axioms Sanctions.Examples.ChordEconomyCs.defianceExistenceSet_eq_Ico
#print axioms Sanctions.Examples.ChordEconomyCs.reliefExistence_lt_margin

end Examples
end Sanctions
