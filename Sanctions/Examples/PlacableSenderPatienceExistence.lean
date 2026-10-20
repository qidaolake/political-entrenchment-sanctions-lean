/-
Sanctions/Examples/PlacableSenderPatienceExistence.lean

**A more patient Target keeps every full-defiance equilibrium** (round BB,
2026-09-28; doc 110 item G8(b)).

Until this file, monotonicity in the Target's discount factor `β_T` was proved
only for *certificates*: the sharp defiance side, the two relief sides and the
certified slope (`sharp_side_mono_βT`, `relief_side_anti_βT`,
`relief_side_notdef_anti_βT`, `certified_sharp_mono_βT`). None of them speaks
about the set of discount factors at which an equilibrium actually exists; in
the window between the sides the certificates identify no equilibrium at all.
This file proves the statement about equilibria.

1. **Existence of a full-defiance equilibrium is a best-reply test**
   (`exists_defiance_equilibrium_iff`). A top-selector feedback Stackelberg
   equilibrium whose Target policy is full defiance at every feasible state
   exists if and only if full defiance is a Target best reply at the two
   constructed defiance-profile values — the Sender's value `VSstar` (the
   Bellman fixed point at `α ≡ 0`) and the Target's value `VTdef` (the fixed
   point of the Target operator along the Sender's response). The predicate is
   `DefianceBestReply`, written directly over those constructed values (Rule 14).
   The forward direction is `values_eq_of_policy_zero`; the converse builds the
   equilibrium (`defianceEquilibrium`) exactly as `equilibriumTop_sharp` does,
   with the best-reply property in place of its sharp-side certificate.
2. **The best-reply test is inherited by a more patient Target**
   (`defianceBestReply_mono_βT_of_monotone`). Take two chord economies that are
   the same game except possibly for `β_T` (`SameGameButβT`: the same payoffs,
   transition and Sender discount factor). The Sender's value and response do not
   depend on `β_T`. Along the defiance path both Target values solve
   `Vᵢ = u + βᵢ·Vᵢ∘z`, with `u(x) = U_T(x,0,ρ(x))` and
   `z(x) = clip(F(x,ρ(x)))`, `ρ` the response at defiance; `z` is monotone when
   `ρ` is. A deviation to compliance `a` lowers the response
   (`response_antitoneOn_a`), hence the successor state. The gain from defying
   at the more patient member exceeds the gain at the less patient one by
   `W(z(x)) − W(z_a(x)) ≥ 0`, where `W = β₂V₂ − β₁V₁` is monotone by the
   patience increasing-differences lemma
   (`Foundations.DiscountedExtremum.monotone_sub_of_solves_of_monotone_left` /
   `_right`) whenever one of the two Target values is monotone.
3. **The monotone Target value is discharged** by the existing balance
   inequality of Proposition bracket (i) at any slope `g ≥ 0`
   (`VTdef_monotone_of_balance`, from `VTdef_lowerSlope`), in particular at
   `g = 0`, where it reads `c·L_resp/μ ≤ v_lo + n_lo·b` — the weak form of the
   existing `hvL`, and free of `β_T` (`VTdef_monotone_of_weak_hvL`).
4. **The existence set is an upper set** (`exists_defiance_equilibrium_mono_βT`
   and its balance and `SameButβT` forms).
5. **Direction, at two ordered concrete members** (Rule 16(a)): on the quartic
   chord economy (`qwChordCs`, non-affine transition `quadDiagF`), no
   full-defiance equilibrium exists at `β_T = 1/30`, one exists at `β_T = 1/2`,
   and existence at any `β₁` carries to every `β₂ ≥ β₁`
   (`qw_defianceExistence_direction`).

**Scope (Rule 9).** Items 2 and 4 are universal over the chord class under a
monotone response (`hmono`) and a monotone defiance-profile Target value at one
member. They are about *one profile* — full defiance, `α ≡ 0` on `[0,1]`: item 2
is the inheritance of its best-reply test, item 4 the resulting existence set.
They are not about the whole equilibrium correspondence: they say nothing about
equilibria with other policies, and a relief equilibrium may coexist. They
compare members of a family
that differ only in `β_T` (with the Sender's data held fixed). It is about
top-selector feedback Stackelberg equilibria (`FeedbackStackelbergEquilibriumTop`)
and does not assert that the threshold `inf {β_T : defiance exists}` is attained.
Item 5 is an instantiation: it witnesses the direction at one family, not a
magnitude and not genericity.

**Rule 22.** General in `F`: the transition enters only through its
monotonicity fields `F_mono_x`, `F_mono_s` and the chord class; the witness
in item 5 is off the affine law.

**Rule 3.** No new assumption. The hypotheses are the family relation (the
existing `SameButβT` implies `SameGameButβT`, `SameButβT.toSameGameButβT`), the
existing monotone-response hypothesis `hmono`, and a monotone Target value at one
member, which is itself implied by the existing balance hypothesis `hginv` at any
`g ≥ 0` together with `hmono`. `SameGameButβT` and `DefianceBestReply` are
relations written over data and constructed objects, not assumed primitives.

Round BC (2026-09-29; doc 110 R4, R5): interiority (`ChordEconomy.Interior`) and
the stage relief margin (`ChordEconomyRelief.StageRelief`) are hypotheses `hInt`, `hSR`
of the results here that read them, no longer class fields; results that read the
relief-side rates are stated on the relief extension `ChordEconomyRelief`.
-/
import Sanctions.Examples.PlacableSenderDefianceValues
import Sanctions.Examples.PlacableSenderBranchInvariance
import Sanctions.Examples.ChordEconomyQuarticWitness
import Sanctions.Foundations.DiscountedExtremum

namespace Sanctions
namespace Examples

open Set Filter Topology BoundedContinuousFunction AbstractGame

noncomputable section

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 1. Existence of a full-defiance equilibrium is a best-reply test -/

/-- **Full defiance is a Target best reply at the defiance-profile values**: at
every feasible state, compliance `0` maximises the Target's forward-looking
objective against the Sender's upper-selector response, when the Sender's value
is the constructed `VSstar` and the Target's continuation value is the
constructed `VTdef`. Written over those constructed values (Rule 14). -/
def DefianceBestReply : Prop :=
  ∀ x ∈ Sanctions.I,
    IsMaxOn (fun a => E.toParams.joint_T_top_integrand E.VTdef E.VSstar x a) Sanctions.I 0

/-- **The full-defiance equilibrium, built from the best-reply test.** The Sender
value is `VSstar`, the Target value `VTdef`, the policy full defiance; the
Target's Bellman equation holds because `0` attains the supremum, and the
Sender's because `VSstar` is its fixed point at `α ≡ 0`. The construction of
`equilibriumTop_sharp` with the best-reply property in place of the sharp side. -/
def defianceEquilibrium (h : E.DefianceBestReply) :
    E.toParams.FeedbackStackelbergEquilibriumTop where
  V_T := E.VTdef
  V_S := E.VSstar
  α := fun _ => 0
  hα := continuous_const
  α_mem := fun _ _ => ⟨le_refl 0, zero_le_one⟩
  V_S_fix := E.VSstar_fix.symm
  V_T_fix_top := by
    intro y
    have hgt : IsGreatest
        ((fun a => E.toParams.joint_T_top_integrand E.VTdef E.VSstar y.val a) '' Sanctions.I)
        (E.toParams.joint_T_top_integrand E.VTdef E.VSstar y.val 0) := by
      refine ⟨⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      exact h y.val y.property ha
    rw [hgt.csSup_eq, E.joint_T_top_integrand_eq E.VSstar_mem _ y.property,
      E.joint_T_integrand_eq]
    have hfix := congrArg (fun V : Val => V y) E.VTdef_fix
    simp only at hfix
    rw [targetOp_apply] at hfix
    exact hfix.symm
  α_opt_top := fun x hx => h x hx

/-- **A full-defiance equilibrium exists if and only if full defiance is a
Target best reply at the defiance-profile values.** Forward: any such
equilibrium has the constructed values (`values_eq_of_policy_zero`), and its
policy is a best reply there. Backward: `defianceEquilibrium`. General in `F`;
no hypothesis beyond the class. -/
theorem exists_defiance_equilibrium_iff :
    (∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0)
      ↔ E.DefianceBestReply := by
  constructor
  · rintro ⟨Eq, hα⟩ x hx
    obtain ⟨hVS, hVT, -⟩ := E.values_eq_of_policy_zero Eq hα
    have h := Eq.α_opt_top x hx
    rw [hα x hx, hVS, hVT] at h
    exact h
  · intro h
    exact ⟨E.defianceEquilibrium h, fun _ _ => rfl⟩

/-! ## 2. A monotone Target value at the defiance profile -/


end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy ChordEconomyTwoSided

variable (E : ChordEconomyRelief)

/-- **The defiance-profile Target value is nondecreasing in the state** under a
monotone response and the balance inequality at some slope `g ≥ 0` (the lower
slope `g` of `VTdef_lowerSlope` is nonnegative). -/
theorem VTdef_monotone_of_balance
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    {g : ℝ} (hg : 0 ≤ g)
    (hginv : g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor) :
    Monotone (E.VTdef : ↥(Sanctions.S : Set ℝ) → ℝ) := by
  intro y₁ y₂ hle
  have h := E.VTdef_lowerSlope hmono hg hginv y₁ y₂ y₁.property y₂.property hle
  have h0 : 0 ≤ g * dist y₁ y₂ := mul_nonneg hg dist_nonneg
  linarith


/-- **The balance at `g = 0` is the weak `hvL`**, `c·L_resp/μ ≤ v_lo + n_lo·b`
(`b = σ(0,0)` the sanction floor), a condition free of `β_T`; under it and a
monotone response the defiance-profile Target value is nondecreasing. -/
theorem VTdef_monotone_of_weak_hvL
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1))
    (hvL : E.c * (E.Lresp / E.mu) ≤ E.vlo + E.nlo * E.sfloor) :
    Monotone (E.VTdef : ↥(Sanctions.S : Set ℝ) → ℝ) := by
  refine E.VTdef_monotone_of_balance hmono le_rfl ?_
  rw [mul_zero, sub_zero, zero_mul, zero_add, max_eq_right E.c_pos.le]
  exact hvL

end ChordEconomyRelief

namespace ChordEconomy

variable (E : ChordEconomy)

/-! ## 3. Two members that are the same game except for `β_T` -/

/-- **The same game except possibly for the Target's discount factor**: the
same Sender and Target stage payoffs, the same transition and the same Sender
discount factor. The rate bounds of the chord class, which are certificates
rather than game data, may differ, and so may the static myopic selector `σ`
(it enters the balance only through `sfloor = σ(0,0)`). Implied by
`ChordEconomyCs.SameButβT`. -/
def SameGameButβT (E₁ E₂ : ChordEconomy) : Prop :=
  E₁.U_S = E₂.U_S ∧ E₁.U_T = E₂.U_T ∧ E₁.F = E₂.F ∧ E₁.β_S = E₂.β_S

/-- The constructed Sender values coincide (`VSstar_eq_of_sender_side_eq`). -/
theorem SameGameButβT.VSstar_eq {E₁ E₂ : ChordEconomy} (h : SameGameButβT E₁ E₂) :
    E₁.VSstar = E₂.VSstar :=
  VSstar_eq_of_sender_side_eq E₁ E₂ h.2.2.1 h.2.2.2 (fun x _ s _ => by rw [h.1])

/-- **The Sender's responses coincide** at every feasible state and every
compliance level, by the first member's argmax uniqueness on its carrier. -/
theorem SameGameButβT.response_eq {E₁ E₂ : ChordEconomy} (h : SameGameButβT E₁ E₂)
    {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) :
    E₂.response E₂.VSstar x a = E₁.response E₁.VSstar x a := by
  have hV := h.VSstar_eq
  obtain ⟨hUS, -, hF, hβS⟩ := h
  have hobj : ∀ s, E₂.senderObj E₂.VSstar x a s = E₁.senderObj E₁.VSstar x a s := by
    intro s
    simp only [senderObj]
    rw [hV, hUS, hF, hβS]
  have hmax₁ := E₁.response_isMaxOn E₁.VSstar x a
  have hmax₂ : IsMaxOn (fun s => E₁.senderObj E₁.VSstar x a s) Sanctions.I
      (E₂.response E₂.VSstar x a) := by
    intro s hs
    have hs' := E₂.response_isMaxOn E₂.VSstar x a hs
    simp only [mem_setOf_eq] at hs' ⊢
    rw [← hobj, ← hobj]
    exact hs'
  exact E₁.DAU_on_carrier E₁.VSstar_mem x hx a _ _ (E₂.response_mem _ _ _)
    (E₁.response_mem _ _ _) hmax₂ hmax₁

/-! ## 4. The best-reply test is inherited by a more patient Target -/

/-- **Defiance as a best reply is inherited by a more patient Target**, given a
monotone response and a monotone defiance-profile Target value at one of the two
members. Across two chord economies that are the same game except for `β_T`,
with `β_T(E₁) ≤ β_T(E₂)`: if full defiance is a Target best reply at the
defiance-profile values of `E₁`, it is one at those of `E₂`. The gain from
defying rises by `W(z(x)) − W(z_a(x)) ≥ 0`, where `W = β₂V₂ − β₁V₁` is
monotone (patience increasing differences, from the two Target Bellman
equations along the common defiance path `z`), and a deviation `a` lowers the
successor state to `z_a(x) ≤ z(x)`. General in `F`. -/
theorem defianceBestReply_mono_βT_of_monotone {E₁ E₂ : ChordEconomy}
    (h : SameGameButβT E₁ E₂) (hβ : E₁.β_T ≤ E₂.β_T)
    (hmono : MonotoneOn (E₁.responsePath E₁.VSstar) (Icc (0 : ℝ) 1))
    (hV : Monotone (E₁.VTdef : ↥(Sanctions.S : Set ℝ) → ℝ)
      ∨ Monotone (E₂.VTdef : ↥(Sanctions.S : Set ℝ) → ℝ))
    (h₁ : E₁.DefianceBestReply) : E₂.DefianceBestReply := by
  have hresp : ∀ x ∈ Sanctions.I, ∀ a : ℝ,
      E₂.response E₂.VSstar x a = E₁.response E₁.VSstar x a :=
    fun x hx a => h.response_eq hx a
  obtain ⟨-, hUT, hF, -⟩ := h
  -- The common defiance path `z` is monotone.
  have hz : Monotone (fun y : ↥(Sanctions.S : Set ℝ) =>
      Sanctions.clipS' (E₁.toParams.F y.val (E₁.responsePath E₁.VSstar y.val))) := by
    intro y₁ y₂ hle
    apply Sanctions.clipS'_mono
    have hle' : y₁.val ≤ y₂.val := hle
    have hρ : E₁.responsePath E₁.VSstar y₁.val ≤ E₁.responsePath E₁.VSstar y₂.val :=
      hmono y₁.property y₂.property hle'
    exact (E₁.F_mono_x (E₁.responsePath E₁.VSstar y₁.val) hle').trans
      (E₁.F_mono_s y₂.val hρ)
  -- Both Target values solve `Vᵢ = u + βᵢ·Vᵢ∘z` along it.
  have hV₁ : ∀ y : ↥(Sanctions.S : Set ℝ),
      E₁.VTdef y = E₁.toParams.U_T y.val 0 (E₁.responsePath E₁.VSstar y.val)
        + E₁.β_T * E₁.VTdef
            (Sanctions.clipS' (E₁.toParams.F y.val (E₁.responsePath E₁.VSstar y.val))) := by
    intro y
    have hfix := congrArg (fun V : Val => V y) E₁.VTdef_fix
    simp only at hfix
    rw [targetOp_apply] at hfix
    exact hfix.symm
  have hV₂ : ∀ y : ↥(Sanctions.S : Set ℝ),
      E₂.VTdef y = E₁.toParams.U_T y.val 0 (E₁.responsePath E₁.VSstar y.val)
        + E₂.β_T * E₂.VTdef
            (Sanctions.clipS' (E₁.toParams.F y.val (E₁.responsePath E₁.VSstar y.val))) := by
    intro y
    have hfix := congrArg (fun V : Val => V y) E₂.VTdef_fix
    simp only at hfix
    rw [targetOp_apply] at hfix
    have hr : E₂.responsePath E₂.VSstar y.val = E₁.responsePath E₁.VSstar y.val :=
      hresp y.val y.property 0
    rw [hr, ← hUT, ← hF] at hfix
    exact hfix.symm
  -- Bounds.
  have hb₁ : ∀ y : ↥(Sanctions.S : Set ℝ), |E₁.VTdef y| ≤ ‖E₁.VTdef‖ + ‖E₂.VTdef‖ := by
    intro y
    have h1 := BoundedContinuousFunction.norm_coe_le_norm E₁.VTdef y
    rw [Real.norm_eq_abs] at h1
    linarith [norm_nonneg E₂.VTdef]
  have hb₂ : ∀ y : ↥(Sanctions.S : Set ℝ), |E₂.VTdef y| ≤ ‖E₁.VTdef‖ + ‖E₂.VTdef‖ := by
    intro y
    have h1 := BoundedContinuousFunction.norm_coe_le_norm E₂.VTdef y
    rw [Real.norm_eq_abs] at h1
    linarith [norm_nonneg E₁.VTdef]
  -- Patience increasing differences: `β₂V₂ − β₁V₁` is monotone.
  have hW : Monotone (fun y : ↥(Sanctions.S : Set ℝ) =>
      E₂.β_T * E₂.VTdef y - E₁.β_T * E₁.VTdef y) := by
    rcases hV with hV | hV
    · exact Foundations.DiscountedExtremum.monotone_sub_of_solves_of_monotone_left
        E₁.hβT0.le hβ E₂.hβT1 hb₁ hb₂ hz hV₁ hV₂ hV
    · exact Foundations.DiscountedExtremum.monotone_sub_of_solves_of_monotone_right
        E₁.hβT0.le hβ E₂.hβT1 hb₁ hb₂ hz hV₁ hV₂ hV
  -- The comparison at each state and each deviation.
  intro x hx
  rw [isMaxOn_iff]
  intro a ha
  have h1 := h₁ x hx ha
  simp only [mem_setOf_eq] at h1
  rw [E₁.joint_T_top_integrand_eq E₁.VSstar_mem _ hx,
    E₁.joint_T_top_integrand_eq E₁.VSstar_mem _ hx, E₁.joint_T_integrand_eq,
    E₁.joint_T_integrand_eq] at h1
  rw [E₂.joint_T_top_integrand_eq E₂.VSstar_mem _ hx,
    E₂.joint_T_top_integrand_eq E₂.VSstar_mem _ hx, E₂.joint_T_integrand_eq,
    E₂.joint_T_integrand_eq, hresp x hx a, hresp x hx 0, ← hUT, ← hF]
  have hsucc : Sanctions.clipS' (E₁.toParams.F x (E₁.response E₁.VSstar x a))
      ≤ Sanctions.clipS' (E₁.toParams.F x (E₁.response E₁.VSstar x 0)) := by
    apply Sanctions.clipS'_mono
    exact E₁.F_mono_s x (E₁.response_antitoneOn_a E₁.VSstar_mem hx zero_mem_I ha ha.1)
  have hWle := hW hsucc
  simp only at hWle
  linarith

/-! ## 5. The existence set of full-defiance equilibria is an upper set in `β_T` -/

/-- **A more patient Target keeps the full-defiance equilibrium.** Across two
chord economies that are the same game except for `β_T`, with
`β_T(E₁) ≤ β_T(E₂)`, a monotone response, and a monotone defiance-profile Target
value at one member: if a top-selector feedback Stackelberg equilibrium with
full defiance at every feasible state exists at `E₁`, one exists at `E₂`. One
profile's existence set, not the whole equilibrium correspondence. General in
`F`. -/
theorem exists_defiance_equilibrium_mono_βT_of_monotone {E₁ E₂ : ChordEconomy}
    (h : SameGameButβT E₁ E₂) (hβ : E₁.β_T ≤ E₂.β_T)
    (hmono : MonotoneOn (E₁.responsePath E₁.VSstar) (Icc (0 : ℝ) 1))
    (hV : Monotone (E₁.VTdef : ↥(Sanctions.S : Set ℝ) → ℝ)
      ∨ Monotone (E₂.VTdef : ↥(Sanctions.S : Set ℝ) → ℝ))
    (h₁ : ∃ Eq : E₁.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    ∃ Eq : E₂.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0 :=
  (E₂.exists_defiance_equilibrium_iff).2
    (defianceBestReply_mono_βT_of_monotone h hβ hmono hV
      ((E₁.exists_defiance_equilibrium_iff).1 h₁))

end ChordEconomy

namespace ChordEconomyRelief

open ChordEconomy

/-! ### The balance route reads the relief rates (round BC)

The balance inequality discharges the monotone defiance-profile Target value
through `VTdef_monotone_of_balance`, which reads the upper compliance cost; the
two theorems below therefore live on the relief extension. -/

/-- **The balance left side falls as the Target's discount factor rises** (round
BD). For `g, g_lo, d_lo, L ≥ 0`, the map
`β ↦ g·(1 − β·g_lo) + max 0 (c − β·d_lo·g)·L` is antitone: both terms fall with
`β`. Pure real arithmetic; it is what makes the balance inequality an upper set
in `β_T`. -/
theorem balanceSide_anti {g gl dl c L β₁ β₂ : ℝ} (hg : 0 ≤ g) (hgl : 0 ≤ gl)
    (hdl : 0 ≤ dl) (hL : 0 ≤ L) (hβ : β₁ ≤ β₂) :
    g * (1 - β₂ * gl) + max 0 (c - β₂ * dl * g) * L
      ≤ g * (1 - β₁ * gl) + max 0 (c - β₁ * dl * g) * L := by
  have h1 : g * (1 - β₂ * gl) ≤ g * (1 - β₁ * gl) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hg
  have h2 : max 0 (c - β₂ * dl * g) ≤ max 0 (c - β₁ * dl * g) :=
    max_le_max le_rfl (by nlinarith [mul_nonneg hdl hg])
  nlinarith [mul_le_mul_of_nonneg_right h2 hL]

/-- **The balance inequality is an upper set in `β_T`** (round BD). If it holds at
an economy's own Target discount factor, it holds, every other datum fixed, at
every larger discount factor `β'`. It carries clause (i) of the paper's
patience-existence proposition on the relief extension: the enriched subclass's
sanction-section semiconvexity (T6) is not read (renovation item BH3.7,
2026-10-06). -/
theorem balance_of_le_βT (E : ChordEconomyRelief) {β' : ℝ} (hβ : E.β_T ≤ β') {g : ℝ}
    (hg : 0 ≤ g)
    (hginv : g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor) :
    g * (1 - β' * E.glo) + max 0 (E.c - β' * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor :=
  (balanceSide_anti hg E.hglo0 E.hdlo0.le (div_nonneg E.Lresp_nonneg E.mu_pos.le) hβ).trans
    hginv

/-- **Defiance as a best reply is inherited by a more patient Target**, with the
monotone Target value discharged by the balance inequality at some `g ≥ 0` at the
less patient member (the paper's Proposition bracket (i) input).

Balance at `E₁` is the stronger of the two choices: on a `SameButβT` family,
balance at `E₁` implies balance at `E₂`, because every other term agrees and the
left side falls as `β_T` rises (`ChordEconomyCs.SameButβT.balance_of_balance`,
through `balance_of_le_βT`). Balance at `E₂` instead, with the response monotone
there, is covered by `defianceBestReply_mono_βT_of_monotone` through `Or.inr`. -/
theorem defianceBestReply_mono_βT {E₁ E₂ : ChordEconomyRelief}
    (h : SameGameButβT E₁.toChordEconomy E₂.toChordEconomy) (hβ : E₁.β_T ≤ E₂.β_T)
    (hmono : MonotoneOn (E₁.responsePath E₁.VSstar) (Icc (0 : ℝ) 1))
    {g : ℝ} (hg : 0 ≤ g)
    (hginv : g * (1 - E₁.β_T * E₁.glo) + max 0 (E₁.c - E₁.β_T * E₁.dlo * g) * (E₁.Lresp / E₁.mu)
      ≤ E₁.vlo + E₁.nlo * E₁.sfloor)
    (h₁ : E₁.DefianceBestReply) : E₂.DefianceBestReply :=
  defianceBestReply_mono_βT_of_monotone h hβ hmono
    (Or.inl (E₁.VTdef_monotone_of_balance hmono hg hginv)) h₁

/-- **A more patient Target keeps the full-defiance equilibrium**, with the
monotone Target value discharged by the balance inequality at some `g ≥ 0` at the
less patient member.

Balance at `E₁` is the stronger of the two choices (on a `SameButβT` family it
implies balance at `E₂`; see `defianceBestReply_mono_βT`). Balance at `E₂`
instead is covered by `exists_defiance_equilibrium_mono_βT_of_monotone` through
`Or.inr`.

This is clause (ii) of the paper's patience-existence proposition on the relief
extension (renovation item BH3.7, 2026-10-06): the two members need only be the
same game except for `β_T` (`SameGameButβT`: the same payoffs, transition and
Sender discount factor; the certificate constants may differ), and the enriched
subclass's sanction-section semiconvexity (T6) is not read. General in `F`. -/
theorem exists_defiance_equilibrium_mono_βT {E₁ E₂ : ChordEconomyRelief}
    (h : SameGameButβT E₁.toChordEconomy E₂.toChordEconomy) (hβ : E₁.β_T ≤ E₂.β_T)
    (hmono : MonotoneOn (E₁.responsePath E₁.VSstar) (Icc (0 : ℝ) 1))
    {g : ℝ} (hg : 0 ≤ g)
    (hginv : g * (1 - E₁.β_T * E₁.glo) + max 0 (E₁.c - E₁.β_T * E₁.dlo * g) * (E₁.Lresp / E₁.mu)
      ≤ E₁.vlo + E₁.nlo * E₁.sfloor)
    (h₁ : ∃ Eq : E₁.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    ∃ Eq : E₂.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0 :=
  exists_defiance_equilibrium_mono_βT_of_monotone h hβ hmono
    (Or.inl (E₁.VTdef_monotone_of_balance hmono hg hginv)) h₁

end ChordEconomyRelief

namespace ChordEconomyCs

/-- The existing family relation `SameButβT` (everything but `β_T` agrees)
implies the game-level one. -/
theorem SameButβT.toSameGameButβT {E₁ E₂ : ChordEconomyCs} (h : SameButβT E₁ E₂) :
    ChordEconomy.SameGameButβT E₁.toChordEconomy E₂.toChordEconomy := by
  obtain ⟨hUS, hUT, -, hF, -, -, -, -, -, -, -, -, -, -, hβS, -⟩ := h
  exact ⟨hUS, hUT, hF, hβS⟩

/-- **The existence set is an upper set, on the existing `SameButβT` family**:
across enriched chord economies that differ only in `β_T`, a monotone response
and the balance inequality at some `g ≥ 0` at the less patient member carry a
full-defiance equilibrium to every more patient member. General in `F`.

Balance at `E₁` is the stronger of the two choices: on this family it implies
balance at `E₂` (`SameButβT.balance_of_balance`). Balance at `E₂` instead is
covered by `ChordEconomy.exists_defiance_equilibrium_mono_βT_of_monotone` through
`Or.inr`.

Its body is `ChordEconomyRelief.exists_defiance_equilibrium_mono_βT` through
`SameButβT.toSameGameButβT`: of the 31 conjuncts of `SameButβT` only four are read,
and the sanction-section semiconvexity (T6) of the enriched subclass is not read
(renovation item BH3.7, 2026-10-06). -/
theorem exists_defiance_equilibrium_mono_βT {E₁ E₂ : ChordEconomyCs} (h : SameButβT E₁ E₂)
    (hβ : E₁.β_T ≤ E₂.β_T)
    (hmono : MonotoneOn (E₁.responsePath E₁.VSstar) (Icc (0 : ℝ) 1))
    {g : ℝ} (hg : 0 ≤ g)
    (hginv : g * (1 - E₁.β_T * E₁.glo) + max 0 (E₁.c - E₁.β_T * E₁.dlo * g) * (E₁.Lresp / E₁.mu)
      ≤ E₁.vlo + E₁.nlo * E₁.sfloor)
    (h₁ : ∃ Eq : E₁.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    ∃ Eq : E₂.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0 :=
  ChordEconomyRelief.exists_defiance_equilibrium_mono_βT (E₁ := E₁.toChordEconomyRelief)
    (E₂ := E₂.toChordEconomyRelief) h.toSameGameButβT hβ hmono hg hginv h₁

/-- **Balance at the less patient member gives balance at the more patient one**
(round BD; previously argued in the docstrings above and not formalised). Across
enriched chord economies that differ only in `β_T`, with `β_T(E₁) ≤ β_T(E₂)`, the
balance inequality at some `g ≥ 0` at `E₁` holds at `E₂`: every term other than
`β_T` agrees (`SameButβT.consts` for `L_resp`, `μ`, the floor) and the left side
falls as `β_T` rises (`ChordEconomyRelief.balance_of_le_βT`). The sanction-section
semiconvexity (T6) of the enriched subclass is not read; the relief form, one member at
two discounts, is `ChordEconomyRelief.balance_of_le_βT` (renovation item BH3.7,
2026-10-06). -/
theorem SameButβT.balance_of_balance {E₁ E₂ : ChordEconomyCs} (h : SameButβT E₁ E₂)
    (hβ : E₁.β_T ≤ E₂.β_T) {g : ℝ} (hg : 0 ≤ g)
    (hginv : g * (1 - E₁.β_T * E₁.glo) + max 0 (E₁.c - E₁.β_T * E₁.dlo * g) * (E₁.Lresp / E₁.mu)
      ≤ E₁.vlo + E₁.nlo * E₁.sfloor) :
    g * (1 - E₂.β_T * E₂.glo) + max 0 (E₂.c - E₂.β_T * E₂.dlo * g) * (E₂.Lresp / E₂.mu)
      ≤ E₂.vlo + E₂.nlo * E₂.sfloor := by
  obtain ⟨-, hmu, -, hL, -, -, -, -, hsf⟩ := h.consts
  obtain ⟨-, -, -, -, hglo, -, hdlo, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc, -,
    hvlo, hnlo, -, -, -⟩ := h
  rw [← hglo, ← hdlo, ← hc, ← hL, ← hmu, ← hvlo, ← hnlo, ← hsf]
  exact E₁.toChordEconomyRelief.balance_of_le_βT hβ hg hginv

end ChordEconomyCs

/-! ## 6. Direction at two ordered concrete members (Rule 16(a))

On the quartic chord economy (`ChordEconomyQuarticWitness.lean`: quartic Sender
payoff, quadratic Target payoff, transition `quadDiagF`, not the affine law at
any rate), the members at every `β_T ∈ (0,1)` are the same game except for
`β_T`, the rally margin holds at every `β_T` (so the response is monotone), and
the weak `hvL` holds at every `β_T` (`c·L_resp/μ = (9/2)(93/100)/(141/50) ≤ 28`).
So the set of `β_T` with a full-defiance equilibrium is an upper set; it misses
`β_T = 1/30` (the relief side rejects defiance there, `qwRelief_relief_notdef`)
and contains `β_T = 1/2` (the loss-offset margin, `qwDefiance_lossOffset`). -/

/-- The weak `hvL` at every member of the quartic family. -/
theorem qw_weak_hvL (βT : ℝ) (h0 : 0 < βT) (h1 : βT < 1) :
    (qwChordCs βT h0 h1).c * ((qwChordCs βT h0 h1).Lresp / (qwChordCs βT h0 h1).mu)
      ≤ (qwChordCs βT h0 h1).vlo + (qwChordCs βT h0 h1).nlo * (qwChordCs βT h0 h1).sfloor := by
  rw [qw_Lresp, qw_mu]
  have hs : 0 ≤ (qwChordCs βT h0 h1).sfloor := (qwChordCs βT h0 h1).sfloor_mem.1
  change (9 / 2 : ℝ) * (93 / 100 / (141 / 50)) ≤ 28 + 3 / 4 * (qwChordCs βT h0 h1).sfloor
  have e : (9 / 2 : ℝ) * (93 / 100 / (141 / 50)) ≤ 28 := by norm_num
  linarith

/-- **Upper set on the quartic family**: a full-defiance equilibrium at `β₁`
carries to every `β₂ ≥ β₁`. -/
theorem qw_exists_defiance_equilibrium_mono (β₁ β₂ : ℝ) (h0₁ : 0 < β₁) (h1₁ : β₁ < 1)
    (h0₂ : 0 < β₂) (h1₂ : β₂ < 1) (hβ : β₁ ≤ β₂)
    (h₁ : ∃ Eq : (qwChordCs β₁ h0₁ h1₁).toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, Eq.α x = 0) :
    ∃ Eq : (qwChordCs β₂ h0₂ h1₂).toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, Eq.α x = 0 :=
  ChordEconomy.exists_defiance_equilibrium_mono_βT_of_monotone
    (E₁ := (qwChordCs β₁ h0₁ h1₁).toChordEconomy) (E₂ := (qwChordCs β₂ h0₂ h1₂).toChordEconomy)
    ⟨rfl, rfl, rfl, rfl⟩ hβ
    ((qwChordCs β₁ h0₁ h1₁).toChordEconomyTwoSided.responsePath_monotoneOn_of_margin
      (qw_rallyMargin β₁ h0₁ h1₁))
    (Or.inl ((qwChordCs β₁ h0₁ h1₁).toChordEconomyRelief.VTdef_monotone_of_weak_hvL
      ((qwChordCs β₁ h0₁ h1₁).toChordEconomyTwoSided.responsePath_monotoneOn_of_margin
        (qw_rallyMargin β₁ h0₁ h1₁))
      (qw_weak_hvL β₁ h0₁ h1₁)))
    h₁

/-- At `β_T = 1/30` full defiance is not a best reply (the relief side rejects it
at the state `0`, `defiance_not_maxOn_of_relief_side`). -/
theorem qwRelief_not_defianceBestReply : ¬ qwRelief.DefianceBestReply := by
  intro h
  have h0 := h 0 ChordEconomy.zero_mem_I
  apply qwRelief.defiance_not_maxOn_of_relief_side (qwChordCs_interior _ _ _) (qw_placable _ _ _)
      (qw_γ _ _ _)
    qwRelief_relief_notdef ChordEconomy.zero_mem_I
  intro a ha
  have h1 := h0 ha
  simp only [mem_setOf_eq] at h1 ⊢
  rwa [qwRelief.joint_T_top_integrand_eq qwRelief.VSstar_mem _ ChordEconomy.zero_mem_I,
    qwRelief.joint_T_top_integrand_eq qwRelief.VSstar_mem _ ChordEconomy.zero_mem_I] at h1

/-- **The direction, at two ordered concrete members.** On the quartic family
(non-affine transition): no full-defiance equilibrium exists at `β_T = 1/30`, one
exists at `β_T = 1/2`, and existence is inherited upward in `β_T`. A witness of
the direction; the threshold between `1/30` and `1/2` is not located. -/
theorem qw_defianceExistence_direction :
    (¬ ∃ Eq : qwRelief.toParams.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Sanctions.I, Eq.α x = 0) ∧
    (∃ Eq : qwDefiance.toParams.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Sanctions.I, Eq.α x = 0) ∧
    ∀ (β₁ β₂ : ℝ) (h0₁ : 0 < β₁) (h1₁ : β₁ < 1) (h0₂ : 0 < β₂) (h1₂ : β₂ < 1), β₁ ≤ β₂ →
      (∃ Eq : (qwChordCs β₁ h0₁ h1₁).toParams.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Sanctions.I, Eq.α x = 0) →
      ∃ Eq : (qwChordCs β₂ h0₂ h1₂).toParams.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Sanctions.I, Eq.α x = 0 := by
  refine ⟨fun hex => qwRelief_not_defianceBestReply
      ((qwRelief.toChordEconomy.exists_defiance_equilibrium_iff).1 hex), ?_,
    fun β₁ β₂ h0₁ h1₁ h0₂ h1₂ hβ h₁ =>
      qw_exists_defiance_equilibrium_mono β₁ β₂ h0₁ h1₁ h0₂ h1₂ hβ h₁⟩
  exact ⟨qwDefiance.equilibriumTop_of_margin qwDefiance_lossOffset (qw_rallyMargin _ _ _),
    fun _ _ => rfl⟩

end

end Examples
end Sanctions

#print axioms Sanctions.Examples.ChordEconomy.defianceEquilibrium
#print axioms Sanctions.Examples.ChordEconomy.exists_defiance_equilibrium_iff
#print axioms Sanctions.Examples.ChordEconomyRelief.VTdef_monotone_of_balance
#print axioms Sanctions.Examples.ChordEconomyRelief.VTdef_monotone_of_weak_hvL
#print axioms Sanctions.Examples.ChordEconomy.SameGameButβT.VSstar_eq
#print axioms Sanctions.Examples.ChordEconomy.SameGameButβT.response_eq
#print axioms Sanctions.Examples.ChordEconomy.defianceBestReply_mono_βT_of_monotone
#print axioms Sanctions.Examples.ChordEconomyRelief.defianceBestReply_mono_βT
#print axioms Sanctions.Examples.ChordEconomy.exists_defiance_equilibrium_mono_βT_of_monotone
#print axioms Sanctions.Examples.ChordEconomyRelief.exists_defiance_equilibrium_mono_βT
#print axioms Sanctions.Examples.ChordEconomyCs.SameButβT.toSameGameButβT
#print axioms Sanctions.Examples.ChordEconomyCs.exists_defiance_equilibrium_mono_βT
#print axioms Sanctions.Examples.ChordEconomyRelief.balanceSide_anti
#print axioms Sanctions.Examples.ChordEconomyRelief.balance_of_le_βT
#print axioms Sanctions.Examples.ChordEconomyCs.SameButβT.balance_of_balance
#print axioms Sanctions.Examples.qw_weak_hvL
#print axioms Sanctions.Examples.qw_exists_defiance_equilibrium_mono
#print axioms Sanctions.Examples.qwRelief_not_defianceBestReply
#print axioms Sanctions.Examples.qw_defianceExistence_direction
