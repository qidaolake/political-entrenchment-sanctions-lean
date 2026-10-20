/-
Sanctions/Examples/PlacableSenderDefianceClosed.lean

**The set of Target discounts at which full defiance is an equilibrium is closed, and its
lower end is attained** (round BE, 2026-10-03; gap G5 of
`suggestions/2026-10-02-lean-gap-map/01_GAP_MAP.md`; construction C3 of the first ChatGPT
gap review, checked locally on 2026-10-03).

`PlacableSenderPatienceExistence.lean` reduced the existence of a full-defiance equilibrium
to a best-reply test at the constructed defiance values, and proved the existence set
upward closed in `β_T` under its monotonicity hypotheses. It did not show that the lower
end of that set is attained, and the collapse theorem
(`PlacableSenderCollapseEquilibrium.lean`) left the equality case `β_T = β_T*` open. This
file closes both gaps, general in `F`.

1. `defianceBestReply_of_tendsto`: across chord economies that are the same game except
   for `β_T`, if full defiance is a best reply along a sequence whose `β_T` tends to that of
   `E`, it is one at `E`. The Sender's value and response do not depend on `β_T`; along the
   common defiance path the Target values solve `Vₙ = u + βₙ·Vₙ∘z`, so
   `(1 − βₙ)‖Vₙ − V‖ ≤ |βₙ − β|·‖V‖` and each deviation gain converges.
2. `exists_defiance_equilibrium_of_tendsto`: the same for existence of the equilibrium.
3. `ChordEconomy.withβT`: the same chord economy with another Target discount, and
   `ChordEconomy.defianceExistence_sInf_mem`: in that one-parameter family, the infimum of
   the existence set is itself in the set whenever it is positive. With the patience result
   the set is then an interval `[β*, 1)` with its lower end attained.
4. `exists_defiance_equilibrium_at_betaStar` and `collapse_equilibrium_threshold_le`: full
   defiance exists **at** the threshold, under the seven conditions of the collapse's
   existence direction (renovation item BG3.3, 2026-10-06); with the collapse's tightness
   equalities it exists exactly when `β_T* ≤ β_T`, with no exception at the threshold.

Renovation item BG3.1 (2026-10-06): `defianceExistence_sInf_mem` no longer assumes the
existence set nonempty; a positive infimum already says so, since `sInf ∅ = 0` in `ℝ`.

Renovation item BH3.7 (2026-10-06): the family `withβT`, the existence set
`defianceExistenceSet` and `defianceExistence_sInf_mem` are stated on the base class
`ChordEconomy`. Until then they were typed on the enriched subclass `ChordEconomyCs`, whose
extra field is the sanction-section semiconvexity (T6), and no proof read it. The relief
extension gets its own `withβT`, which the defiance interval of
`PlacableSenderExactThresholds.lean` uses; the enriched names stay, as the same objects
(`withβT_toChordEconomy`, `defianceExistenceSet_eq_toChordEconomy`) or one-line corollaries.

**Rule 22.** Items 1–3 are general in `F`. Item 4 inherits the collapse's hypotheses, which
make `F` affine on the unit square (its five zeros give `L_resp = 0`, which already does:
`F_eq_affineF_of_Lresp_eq_zero`). **Rule 3.** No assumption is introduced. **Rule 9.** No
witness is involved; the statements are about one profile, full defiance, not about the
whole equilibrium correspondence.
-/
import Sanctions.Examples.PlacableSenderPatienceExistence
import Sanctions.Examples.PlacableSenderCollapseEquilibrium

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomy

/-- **Full defiance as a best reply passes to the limit in `β_T`.** If a sequence of chord
economies, each the same game as `E` except for the Target's discount factor, has full
defiance as a Target best reply at its defiance-profile values, and their discount factors
tend to `E`'s, then full defiance is a best reply at `E`'s defiance-profile values. General
in `F`. -/
theorem defianceBestReply_of_tendsto {E : ChordEconomy} (Es : ℕ → ChordEconomy)
    (hs : ∀ n, SameGameButβT E (Es n))
    (hlim : Tendsto (fun n => (Es n).β_T) atTop (𝓝 E.β_T))
    (hbr : ∀ n, (Es n).DefianceBestReply) : E.DefianceBestReply := by
  -- the common defiance path, stage payoff and responses
  have hresp : ∀ n, ∀ x ∈ Sanctions.I, ∀ a : ℝ,
      (Es n).response (Es n).VSstar x a = E.response E.VSstar x a :=
    fun n x hx a => (hs n).response_eq hx a
  have hUT : ∀ n, (Es n).toParams.U_T = E.toParams.U_T := fun n => ((hs n).2.1).symm
  have hF : ∀ n, (Es n).toParams.F = E.toParams.F := fun n => ((hs n).2.2.1).symm
  set z : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.S : Set ℝ) :=
    fun y => Sanctions.clipS' (E.toParams.F y.val (E.responsePath E.VSstar y.val)) with hz
  set u : ↥(Sanctions.S : Set ℝ) → ℝ :=
    fun y => E.toParams.U_T y.val 0 (E.responsePath E.VSstar y.val) with hu
  have hV : ∀ y, E.VTdef y = u y + E.β_T * E.VTdef (z y) := by
    intro y
    have hfix := congrArg (fun V : Val => V y) E.VTdef_fix
    simp only at hfix
    rw [targetOp_apply] at hfix
    exact hfix.symm
  have hVn : ∀ n, ∀ y, (Es n).VTdef y = u y + (Es n).β_T * (Es n).VTdef (z y) := by
    intro n y
    have hfix := congrArg (fun V : Val => V y) (Es n).VTdef_fix
    simp only at hfix
    rw [targetOp_apply] at hfix
    have hr : (Es n).responsePath (Es n).VSstar y.val = E.responsePath E.VSstar y.val :=
      hresp n y.val y.property 0
    rw [hr, hUT n, hF n] at hfix
    exact hfix.symm
  -- the distance between the Target values
  have hβn : ∀ n, 0 ≤ (Es n).β_T ∧ (Es n).β_T < 1 := fun n => ⟨(Es n).hβT0.le, (Es n).hβT1⟩
  have hdist : ∀ n, (1 - (Es n).β_T) * ‖(Es n).VTdef - E.VTdef‖
      ≤ |(Es n).β_T - E.β_T| * ‖E.VTdef‖ := by
    intro n
    set d := ‖(Es n).VTdef - E.VTdef‖ with hd
    have hpt : ∀ y, |(Es n).VTdef y - E.VTdef y|
        ≤ (Es n).β_T * d + |(Es n).β_T - E.β_T| * ‖E.VTdef‖ := by
      intro y
      have e : (Es n).VTdef y - E.VTdef y
          = (Es n).β_T * ((Es n).VTdef (z y) - E.VTdef (z y))
            + ((Es n).β_T - E.β_T) * E.VTdef (z y) := by
        rw [hVn n y, hV y]; ring
      rw [e]
      have h1 : |(Es n).VTdef (z y) - E.VTdef (z y)| ≤ d := by
        have := BoundedContinuousFunction.norm_coe_le_norm ((Es n).VTdef - E.VTdef) (z y)
        rw [Real.norm_eq_abs] at this
        simpa using this
      have h2 : |E.VTdef (z y)| ≤ ‖E.VTdef‖ := by
        have := BoundedContinuousFunction.norm_coe_le_norm E.VTdef (z y)
        rwa [Real.norm_eq_abs] at this
      calc |(Es n).β_T * ((Es n).VTdef (z y) - E.VTdef (z y))
            + ((Es n).β_T - E.β_T) * E.VTdef (z y)|
          ≤ |(Es n).β_T * ((Es n).VTdef (z y) - E.VTdef (z y))|
            + |((Es n).β_T - E.β_T) * E.VTdef (z y)| := abs_add_le _ _
        _ = (Es n).β_T * |(Es n).VTdef (z y) - E.VTdef (z y)|
            + |(Es n).β_T - E.β_T| * |E.VTdef (z y)| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (hβn n).1]
        _ ≤ (Es n).β_T * d + |(Es n).β_T - E.β_T| * ‖E.VTdef‖ := by
              gcongr
              exact (hβn n).1
    have hnorm : d ≤ (Es n).β_T * d + |(Es n).β_T - E.β_T| * ‖E.VTdef‖ := by
      have h0 : 0 ≤ (Es n).β_T * d + |(Es n).β_T - E.β_T| * ‖E.VTdef‖ := by
        have := (hβn n).1
        positivity
      refine (BoundedContinuousFunction.norm_le h0).2 (fun y => ?_)
      rw [Real.norm_eq_abs]
      simpa using hpt y
    linarith
  -- convergence of the discounted continuation at every state
  have hβ1 := E.hβT1
  have hconv : ∀ y, Tendsto (fun n => (Es n).β_T * (Es n).VTdef y) atTop
      (𝓝 (E.β_T * E.VTdef y)) := by
    intro y
    have hevent : ∀ᶠ n in atTop, (Es n).β_T < (1 + E.β_T) / 2 :=
      hlim.eventually (gt_mem_nhds (by linarith))
    have hb0 : Tendsto (fun n => |(Es n).β_T - E.β_T|) atTop (𝓝 0) := by
      have := (tendsto_sub_nhds_zero_iff.mpr hlim).abs
      simpa using this
    set C := ‖E.VTdef‖ * (2 / (1 - E.β_T) + 1) with hC
    have hg : Tendsto (fun n => |(Es n).β_T - E.β_T| * C) atTop (𝓝 0) := by
      simpa using hb0.mul_const C
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hg
    filter_upwards [hevent] with n hn
    rw [Real.norm_eq_abs]
    have hd := hdist n
    have hpos : (1 - E.β_T) / 2 ≤ 1 - (Es n).β_T := by linarith
    have hdn : ‖(Es n).VTdef - E.VTdef‖
        ≤ |(Es n).β_T - E.β_T| * ‖E.VTdef‖ * (2 / (1 - E.β_T)) := by
      have hA : 0 ≤ ‖(Es n).VTdef - E.VTdef‖ := norm_nonneg _
      have hden : 0 < 1 - E.β_T := by linarith
      rw [mul_div_assoc', le_div_iff₀ hden]
      nlinarith [mul_le_mul_of_nonneg_right hpos hA]
    have hy1 : |(Es n).VTdef y - E.VTdef y| ≤ ‖(Es n).VTdef - E.VTdef‖ := by
      have := BoundedContinuousFunction.norm_coe_le_norm ((Es n).VTdef - E.VTdef) y
      rw [Real.norm_eq_abs] at this
      simpa using this
    have hy2 : |E.VTdef y| ≤ ‖E.VTdef‖ := by
      have := BoundedContinuousFunction.norm_coe_le_norm E.VTdef y
      rwa [Real.norm_eq_abs] at this
    have e : (Es n).β_T * (Es n).VTdef y - E.β_T * E.VTdef y
        = (Es n).β_T * ((Es n).VTdef y - E.VTdef y) + ((Es n).β_T - E.β_T) * E.VTdef y := by
      ring
    rw [e]
    calc |(Es n).β_T * ((Es n).VTdef y - E.VTdef y) + ((Es n).β_T - E.β_T) * E.VTdef y|
        ≤ (Es n).β_T * |(Es n).VTdef y - E.VTdef y| + |(Es n).β_T - E.β_T| * |E.VTdef y| := by
          calc _ ≤ |(Es n).β_T * ((Es n).VTdef y - E.VTdef y)|
                + |((Es n).β_T - E.β_T) * E.VTdef y| := abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (hβn n).1]
      _ ≤ 1 * ‖(Es n).VTdef - E.VTdef‖ + |(Es n).β_T - E.β_T| * ‖E.VTdef‖ := by
          gcongr
          · exact (hβn n).2.le
      _ ≤ |(Es n).β_T - E.β_T| * C := by
          rw [hC]; nlinarith [hdn, abs_nonneg ((Es n).β_T - E.β_T), norm_nonneg E.VTdef]
  -- the best-reply inequalities pass to the limit
  intro x hx
  rw [isMaxOn_iff]
  intro a ha
  have hlimit : ∀ b : ℝ, Tendsto (fun n => E.toParams.U_T x b (E.response E.VSstar x b)
      + (Es n).β_T * (Es n).VTdef (Sanctions.clipS' (E.toParams.F x (E.response E.VSstar x b))))
      atTop (𝓝 (E.toParams.U_T x b (E.response E.VSstar x b)
        + E.β_T * E.VTdef (Sanctions.clipS' (E.toParams.F x (E.response E.VSstar x b))))) :=
    fun b => tendsto_const_nhds.add (hconv _)
  have hn : ∀ n, E.toParams.U_T x a (E.response E.VSstar x a)
      + (Es n).β_T * (Es n).VTdef (Sanctions.clipS' (E.toParams.F x (E.response E.VSstar x a)))
      ≤ E.toParams.U_T x 0 (E.response E.VSstar x 0)
      + (Es n).β_T
        * (Es n).VTdef (Sanctions.clipS' (E.toParams.F x (E.response E.VSstar x 0))) := by
    intro n
    have h1 := hbr n x hx ha
    simp only [mem_setOf_eq] at h1
    rw [(Es n).joint_T_top_integrand_eq (Es n).VSstar_mem _ hx,
      (Es n).joint_T_top_integrand_eq (Es n).VSstar_mem _ hx, (Es n).joint_T_integrand_eq,
      (Es n).joint_T_integrand_eq, hresp n x hx a, hresp n x hx 0, hUT n, hF n] at h1
    exact h1
  have hle := le_of_tendsto_of_tendsto' (hlimit a) (hlimit 0) hn
  rw [E.joint_T_top_integrand_eq E.VSstar_mem _ hx, E.joint_T_top_integrand_eq E.VSstar_mem _ hx,
    E.joint_T_integrand_eq, E.joint_T_integrand_eq]
  exact hle

/-- **Existence of a full-defiance equilibrium passes to the limit in `β_T`.** -/
theorem exists_defiance_equilibrium_of_tendsto {E : ChordEconomy} (Es : ℕ → ChordEconomy)
    (hs : ∀ n, SameGameButβT E (Es n))
    (hlim : Tendsto (fun n => (Es n).β_T) atTop (𝓝 E.β_T))
    (hex : ∀ n, ∃ Eq : (Es n).toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0 :=
  (E.exists_defiance_equilibrium_iff).2
    (defianceBestReply_of_tendsto Es hs hlim
      (fun n => ((Es n).exists_defiance_equilibrium_iff).1 (hex n)))

/-! ### The one-parameter family in `β_T` on the base class (renovation item BH3.7) -/

/-- **The same chord economy with Target discount `b`.** Only `β_T` changes; no other field
of the class mentions it. Stated on the base class (renovation item BH3.7, 2026-10-06; until
then only on the enriched subclass, `ChordEconomyCs.withβT`, which is the same member,
`ChordEconomyCs.withβT_toChordEconomy`). General in `F`. -/
def withβT (E : ChordEconomy) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : ChordEconomy :=
  { E with β_T := b, β_T_mem := ⟨hb0.le, hb1⟩, hβT0 := hb0 }

@[simp] theorem withβT_β_T (E : ChordEconomy) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (E.withβT b hb0 hb1).β_T = b := rfl

/-- Two members of the same `β_T` family are the same game except for `β_T`. General in
`F`. -/
theorem withβT_sameGame (E : ChordEconomy) {b₁ b₂ : ℝ} (h₁0 : 0 < b₁) (h₁1 : b₁ < 1)
    (h₂0 : 0 < b₂) (h₂1 : b₂ < 1) :
    SameGameButβT (E.withβT b₁ h₁0 h₁1) (E.withβT b₂ h₂0 h₂1) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `E` and its family member are the same game except for `β_T`. General in `F`. -/
theorem sameGame_withβT (E : ChordEconomy) {b : ℝ} (h0 : 0 < b) (h1 : b < 1) :
    SameGameButβT E (E.withβT b h0 h1) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The discounts in `(0,1)` at which the family member has a full-defiance equilibrium.
On the base class (renovation item BH3.7, 2026-10-06). -/
def defianceExistenceSet (E : ChordEconomy) : Set ℝ :=
  {b | ∃ h : 0 < b ∧ b < 1, ∃ Eq : (E.withβT b h.1 h.2).toParams.FeedbackStackelbergEquilibriumTop,
    ∀ x ∈ Sanctions.I, Eq.α x = 0}

/-- **The lower end of the existence set is attained.** In the one-parameter family
`E.withβT`, if the infimum of the discounts that admit a full-defiance equilibrium is
positive, then the infimum itself admits one. With the patience result
(`ChordEconomy.exists_defiance_equilibrium_mono_βT_of_monotone`) the existence set is then
`[β*, 1)`. The set is not assumed nonempty (renovation item BG3.1, 2026-10-06): the infimum
of the empty set is `0` in `ℝ`, so a positive infimum already says that some discount admits
full defiance. Stated for every chord economy (renovation item BH3.7, 2026-10-06): the
enriched subclass's sanction-section semiconvexity (T6), which the earlier statement on
`ChordEconomyCs` carried, is dropped; the proof never read it. General in `F`. -/
theorem defianceExistence_sInf_mem (E : ChordEconomy)
    (hpos : 0 < sInf E.defianceExistenceSet) :
    sInf E.defianceExistenceSet ∈ E.defianceExistenceSet := by
  set B := E.defianceExistenceSet with hB
  have hne : B.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Real.sInf_empty] at hpos
    exact lt_irrefl 0 hpos
  have hbdd : BddBelow B := ⟨0, fun b hb => (hb.choose).1.le⟩
  obtain ⟨b₀, hb₀⟩ := hne
  have hlt1 : sInf B < 1 := lt_of_le_of_lt (csInf_le hbdd hb₀) hb₀.choose.2
  obtain ⟨u, -, hu_lim, hu_mem⟩ := exists_seq_tendsto_sInf ⟨b₀, hb₀⟩ hbdd
  refine ⟨⟨hpos, hlt1⟩, ?_⟩
  exact (E.withβT (sInf B) hpos hlt1).exists_defiance_equilibrium_of_tendsto
    (fun n => E.withβT (u n) (hu_mem n).choose.1 (hu_mem n).choose.2)
    (fun n => E.withβT_sameGame hpos hlt1 _ _) hu_lim
    (fun n => (hu_mem n).choose_spec)

end ChordEconomy

namespace ChordEconomyRelief

/-- **The same relief economy with Target discount `b`** (renovation item BH3.7,
2026-10-06). Only `β_T` changes; no field of the relief extension mentions it. Its base
economy is the base family member (`withβT_toChordEconomy`), so it has the same defiance
existence set; it carries the relief rates that the balance route of the defiance interval
reads (`ChordEconomyRelief.defianceExistence_upper`). General in `F`. -/
def withβT (E : ChordEconomyRelief) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ChordEconomyRelief :=
  { E with β_T := b, β_T_mem := ⟨hb0.le, hb1⟩, hβT0 := hb0 }

@[simp] theorem withβT_β_T (E : ChordEconomyRelief) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (E.withβT b hb0 hb1).β_T = b := rfl

/-- The relief family member's base economy is the base family member. -/
theorem withβT_toChordEconomy (E : ChordEconomyRelief) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (E.withβT b hb0 hb1).toChordEconomy = E.toChordEconomy.withβT b hb0 hb1 := rfl

end ChordEconomyRelief

namespace ChordEconomyCs

open ChordEconomy

/-- **The same enriched economy with Target discount `b`.** Only `β_T` changes; no other
field of the class mentions it. The relief side of `PlacableSenderExactThresholds.lean`
needs the enriched member; the defiance side uses the base family `ChordEconomy.withβT`,
the same member (`withβT_toChordEconomy`). -/
def withβT (E : ChordEconomyCs) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : ChordEconomyCs :=
  { E with β_T := b, β_T_mem := ⟨hb0.le, hb1⟩, hβT0 := hb0 }

@[simp] theorem withβT_β_T (E : ChordEconomyCs) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (E.withβT b hb0 hb1).β_T = b := rfl

/-- The enriched family member's relief economy is the relief family member (renovation
item BH3.7, 2026-10-06). -/
theorem withβT_toChordEconomyRelief (E : ChordEconomyCs) (b : ℝ) (hb0 : 0 < b)
    (hb1 : b < 1) :
    (E.withβT b hb0 hb1).toChordEconomyRelief = E.toChordEconomyRelief.withβT b hb0 hb1 := rfl

/-- The enriched family member's base economy is the base family member (renovation item
BH3.7, 2026-10-06). -/
theorem withβT_toChordEconomy (E : ChordEconomyCs) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    (E.withβT b hb0 hb1).toChordEconomy = E.toChordEconomy.withβT b hb0 hb1 := rfl

/-- Two members of the same `β_T` family are the same game except for `β_T`. -/
theorem withβT_sameGame (E : ChordEconomyCs) {b₁ b₂ : ℝ} (h₁0 : 0 < b₁) (h₁1 : b₁ < 1)
    (h₂0 : 0 < b₂) (h₂1 : b₂ < 1) :
    SameGameButβT (E.withβT b₁ h₁0 h₁1).toChordEconomy (E.withβT b₂ h₂0 h₂1).toChordEconomy :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `E` and its family member are the same game except for `β_T`. -/
theorem sameGame_withβT (E : ChordEconomyCs) {b : ℝ} (h0 : 0 < b) (h1 : b < 1) :
    SameGameButβT E.toChordEconomy (E.withβT b h0 h1).toChordEconomy :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The discounts in `(0,1)` at which the family member has a full-defiance equilibrium.
It is the base economy's set (`defianceExistenceSet_eq_toChordEconomy`, renovation item
BH3.7, 2026-10-06). -/
def defianceExistenceSet (E : ChordEconomyCs) : Set ℝ :=
  {b | ∃ h : 0 < b ∧ b < 1, ∃ Eq : (E.withβT b h.1 h.2).toParams.FeedbackStackelbergEquilibriumTop,
    ∀ x ∈ Sanctions.I, Eq.α x = 0}

/-- **The enriched existence set is the base one** (renovation item BH3.7, 2026-10-06): the
members `E.withβT b` and `E.toChordEconomy.withβT b` are the same game, so the two sets
agree by definition. General in `F`. -/
theorem defianceExistenceSet_eq_toChordEconomy (E : ChordEconomyCs) :
    E.defianceExistenceSet = E.toChordEconomy.defianceExistenceSet := rfl

/-- **The lower end of the existence set is attained**, on the enriched subclass: the base
theorem `ChordEconomy.defianceExistence_sInf_mem` at `E.toChordEconomy` (renovation item
BH3.7, 2026-10-06), kept under its old name. The set is not assumed nonempty (renovation
item BG3.1). General in `F`. -/
theorem defianceExistence_sInf_mem (E : ChordEconomyCs)
    (hpos : 0 < sInf E.defianceExistenceSet) :
    sInf E.defianceExistenceSet ∈ E.defianceExistenceSet :=
  E.toChordEconomy.defianceExistence_sInf_mem hpos

/-- **Full defiance exists at the collapse threshold.** At `β_T = β_T*` (an interior
threshold) a full-defiance equilibrium exists under the conditions of the collapse's
existence direction other than `β_T* < β_T`: `σ_V = M_s = τ_x = M_cx = M_mix = 0` and
`1 ≤ g_lo + d_lo` (renovation item BG3.3, 2026-10-06; until then the stage relief margin
and the fourteen tightness equalities). The members just above the threshold have one
(`exists_defiance_equilibrium_of_collapse`; neither these conditions nor `β_T*` involve
`β_T`), and existence passes to the limit. AFFINE BY HYPOTHESIS, as the collapse is: the
five zeros give `L_resp = 0`, which pins the affine law (`F_eq_affineF_of_Lresp_eq_zero`). -/
theorem exists_defiance_equilibrium_at_betaStar (E : ChordEconomyCs) (hSigV : E.SigV = 0)
    (hMs : E.Ms = 0) (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMmix : E.Mmix = 0)
    (hgd : 1 ≤ E.glo + E.dlo) (hβ : E.β_T = E.betaStar) :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0 := by
  have h0 : 0 < E.β_T := E.hβT0
  have h1 : E.β_T < 1 := E.hβT1
  set u : ℕ → ℝ := fun n => E.β_T + (1 - E.β_T) / ((n : ℝ) + 2) with hu
  have hu_gt : ∀ n, E.β_T < u n := by
    intro n
    have : 0 < (1 - E.β_T) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
    simp only [hu]; linarith
  have hu_lt : ∀ n, u n < 1 := by
    intro n
    have h2 : (1 - E.β_T) / ((n : ℝ) + 2) < 1 - E.β_T := by
      rw [div_lt_iff₀ (by positivity)]
      have : (1 : ℝ) < (n : ℝ) + 2 := by have := n.cast_nonneg (α := ℝ); linarith
      nlinarith
    simp only [hu]; linarith
  have hu_pos : ∀ n, 0 < u n := fun n => lt_trans h0 (hu_gt n)
  have hu_lim : Tendsto u atTop (𝓝 E.β_T) := by
    have hlim : Tendsto (fun n : ℕ => (1 - E.β_T) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h := tendsto_const_div_atTop_nhds_zero_nat (1 - E.β_T)
      have h' := (tendsto_add_atTop_iff_nat 2).2 h
      refine h'.congr (fun n => ?_)
      push_cast; ring_nf
    simpa [hu] using (tendsto_const_nhds (x := E.β_T)).add hlim
  refine E.toChordEconomy.exists_defiance_equilibrium_of_tendsto
    (fun n => (E.withβT (u n) (hu_pos n) (hu_lt n)).toChordEconomy)
    (fun n => E.sameGame_withβT (hu_pos n) (hu_lt n)) hu_lim (fun n => ?_)
  have hstar : (E.withβT (u n) (hu_pos n) (hu_lt n)).betaStar = E.betaStar := rfl
  have hgt : (E.withβT (u n) (hu_pos n) (hu_lt n)).betaStar
      < (E.withβT (u n) (hu_pos n) (hu_lt n)).β_T := by
    rw [hstar, withβT_β_T, ← hβ]; exact hu_gt n
  exact (E.withβT (u n) (hu_pos n) (hu_lt n)).exists_defiance_equilibrium_of_collapse hSigV
    hMs hτ hMcx hMmix hgd hgt

/-- **The exact closed threshold at the collapse.** Under placability and the collapse's
tightness equalities, a top-selector equilibrium with full defiance at every state exists
**if and only if** `β_T* ≤ β_T`, with no exception at the threshold
(`collapse_equilibrium_threshold` with the equality case closed). AFFINE BY HYPOTHESIS. -/
theorem collapse_equilibrium_threshold_le (E : ChordEconomyCs) (hInt : E.Interior)
    (hSR : E.StageRelief) (hP : E.Placable) (hSigV : E.SigV = 0) (hMs : E.Ms = 0)
    (hτ : E.τx = 0) (hMcx : E.Mcx = 0) (hMcs : E.Mcs = 0) (hMmix : E.Mmix = 0)
    (hQ : E.Qbar = E.q) (hk : E.klo = E.khi) (hℓ : E.ℓlo = E.ℓhi) (hp : E.plo = E.c)
    (hv : E.vlo = E.vhi) (hnhi : E.nhi = 0) (hg : E.glo = E.ghi) (hd : E.dlo = E.dhi) :
    (∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0)
      ↔ E.betaStar ≤ E.β_T := by
  rcases eq_or_ne E.β_T E.betaStar with heq | hne
  · rw [heq]
    exact ⟨fun _ => le_rfl, fun _ => E.exists_defiance_equilibrium_at_betaStar hSigV hMs hτ
      hMcx hMmix (E.glo_add_dlo_eq_one_of_tight hg hd).ge heq⟩
  · rw [E.collapse_equilibrium_threshold hInt hSR hP hSigV hMs hτ hMcx hMcs hMmix hQ hk hℓ hp hv
      hnhi hg hd hne]
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (Ne.symm hne)⟩

end ChordEconomyCs

end

#print axioms Sanctions.Examples.ChordEconomy.defianceBestReply_of_tendsto
#print axioms Sanctions.Examples.ChordEconomy.exists_defiance_equilibrium_of_tendsto
#print axioms Sanctions.Examples.ChordEconomy.defianceExistence_sInf_mem
#print axioms Sanctions.Examples.ChordEconomyCs.defianceExistence_sInf_mem
#print axioms Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_at_betaStar
#print axioms Sanctions.Examples.ChordEconomyCs.collapse_equilibrium_threshold_le

end Examples
end Sanctions
