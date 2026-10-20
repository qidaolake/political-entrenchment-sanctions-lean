/-
Sanctions/Examples/SymbolicCertifiedFamilyGeneralFRecovery.lean

**What the general-`F` reroute costs, and why the answer is nothing.**

The family's headline consequences were rerouted from the legacy affine route
(`three_goals_local_uniform_starts`, which hard-requires `hF`) to the
Milgrom–Shannon general-transition route. The reroute sheds conclusions: Goal 1
loses the `s̄` sanction floor and the per-period Target-argmax certificate,
Goal 3 loses the floor, and the myopic comparator changes from the
certificate's own field to `myopicFeedbackEquilibrium_canonical`.

This file recovers all of them, in **strictly stronger** form:

* the sanction floor — not merely `s̄ ≤ σ_n` but `σ_n = 1` exactly, along both
  the natural and the post-shock general-`F` trajectory, so *any* floor `≤ 1`
  follows (`realizedRule_eq_one`). The family no longer carries a floor `s̄`
  (plan item BJ4.1, 2026-10-07), so the separate `s̄ ≤ σ_n` conjuncts, which
  `σ_n = 1` already implied, were dropped;
* the per-period Target-argmax certificate — directly from `α_opt_top` at the
  confined path;
* the comparator swap — shown immaterial, because **every** myopic feedback
  equilibrium realises zero sanction, not merely the canonical selection
  (`any_myopic_sigma_eq_zero`, `regime_separation_any_myopic`). That the myopic
  problem does not see the transition at all is isolated as
  `myopic_problem_transition_free`.

So the reroute is a change of route, not a weakening of the conclusion set.
`wobbleEconMS_legacy_route_unavailable` records why the legacy route could not
simply have been kept: that witness's transition is not affine for **any**
adjustment rate.

## READ THIS BEFORE CLASSIFYING ANYTHING IN THIS FILE (audit note)

**The results here are universals over a family, not witness instances.** They
are quantified over the symbolic economy variable declared below -- every
admissible member -- so they license universal statements about the family, and
Rule 9's "a witness proves only existence" restriction does **not** apply to
them.

The file sits under `Examples/` because the family fixes a *functional form* for
the stage payoffs, not because its theorems are point checks. Rule 19 keeps
`Theory/` for statements over an arbitrary `Params`; a coefficient-parameterised
algebraic family is narrower than that, so `Examples/` is the correct home and
the file is deliberately not moved.

This banner exists because the filing has already misled an audit. A 2026-08-16
review classified `prop:equilibrium-patience-feedback` as a paper universal
backed only by a witness, having found the numeric `eeCertB_*` names cited in
the formalization map and not the `symbolic_*` siblings in this cluster. The
paper was right and the audit was wrong. If you are deciding what a paper claim
rests on, grep this cluster before concluding that a family-level claim has only
witness backing.
-/

import Sanctions.Examples.SymbolicCertifiedFamilyGeneralFCertificate

namespace Sanctions

namespace Examples

open Set AbstractGame

noncomputable section

namespace SymbolicEconomyF

variable (E : SymbolicEconomyF)

/-! ### Probe 0 — the shed pieces exist as named theorems already -/

-- per-period Target argmax analogue (W4 of the certificate file)
#check @SymbolicEconomyF.zero_isMaxOn_joint
-- top-selector corner pin (W3)
#check @SymbolicEconomyF.σ_dyn_top_eq_one
-- every myopic stage argmax zeroes the sanction (W10)
#check @SymbolicEconomyF.myopic_argmax_sigma_eq_zero
#check @SymbolicEconomyF.canonical_myopic_sigma_eq_zero

/-! ### R1 — the realised dynamic rule is the top corner at every feasible state -/

/-- **The realised forward-looking sanction is exactly full**, at every
feasible state, for any equilibrium whose Sender value lies in the carrier. -/
theorem realizedRule_eq_one
    (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS : Eq.V_S ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.S) :
    E.toParams.dynamicTopRealizedRule Eq.V_S Eq.α x = 1 :=
  E.σ_dyn_top_eq_one hVS hx (Eq.α_mem x hx)

/-! ### R2 — the full conclusion set on the general-`F` trajectory -/

/-- **General-`F` three goals, with every legacy conjunct restored.**

Goal 1 carries five conjuncts and Goal 3 three, each including the sanction
*equality* `σ_n = 1`. General in `F`.

**Edited in place (plan item BJ4.1, 2026-10-07).** Goal 1 and Goal 3 each had
one more conjunct, the sanction floor `s̄ ≤ σ_n`. The family no longer carries
`s̄`, and the equality `σ_n = 1` already gives every floor `≤ 1`, so the floor
conjuncts were dropped; nothing else changed.

**Dropped hypothesis (plan item BG3.7, 2026-10-06).** The strict placation
margin `u₀ + r < k` is no longer an argument. It reached this theorem only
through `certificateMS`, which no longer needs it: Goal 2 compares the
forward-looking sanction with the canonical myopic one, and that comparison
needs only the myopic ceiling, not a zero myopic sanction at the top state. -/
theorem three_goals_generalF_full
    (hxb_pos : 0 < E.xb) :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT
      ∧ Eq.V_S ∈ E.carrierS
      ∧ (∀ x₀ ∈ Set.Icc E.xb 1,
          (∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc E.xb 1) ∧
          (∀ n, E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀ n = 1) ∧
          (∀ n, E.xb ≤ E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀ n) ∧
          Monotone (E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S
                        (E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n) a)
            Sanctions.I
            (Eq.α (E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc E.xb 1,
           E.toParams.σ x
               (E.toParams.myopicFeedbackEquilibrium_canonical.α x)
             ≤ E.toParams.dynamicTopRealizedRule Eq.V_S Eq.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α
                    (E.toParams.shockPathF x₀shock N) n
                    ∈ Set.Icc E.xb 1) ∧
            (∀ n, E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α
                    (E.toParams.shockPathF x₀shock N) n = 1) ∧
            (∀ n, E.xb ≤ E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α
                    (E.toParams.shockPathF x₀shock N) n)) := by
  obtain ⟨Eq, hVT, hVS, hG1, hG2, hG3⟩ :=
    (E.certificateMS hxb_pos).three_goals_local_MS_generalF
      (p := E.toParams) E.hF_top
  have hmax : max (E.certificateMS hxb_pos).xT
      (E.certificateMS hxb_pos).xS = E.xb := max_self E.xb
  rw [hmax] at hG1 hG2 hG3
  refine ⟨Eq, hVT, hVS, ?_, hG2, ?_⟩
  · intro x₀ hx₀
    obtain ⟨h1, _h2, h3⟩ := hG1 x₀ hx₀
    have hfeas : ∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
        ∈ Sanctions.S := fun n =>
      ⟨le_trans E.hxb0 (h1 n).1, (h1 n).2⟩
    have heq : ∀ n, E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀ n = 1 :=
      fun n => E.realizedRule_eq_one Eq hVS (hfeas n)
    refine ⟨h1, heq, ?_, h3, ?_⟩
    · intro n; rw [heq n]; exact E.xb_le_one
    · intro n; exact Eq.α_opt_top _ (hfeas n)
  · intro x₀shock hnn hle
    obtain ⟨N, h1, _h3⟩ := hG3 x₀shock hnn hle
    have hfeas : ∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α
        (E.toParams.shockPathF x₀shock N) n ∈ Sanctions.S := fun n =>
      ⟨le_trans E.hxb0 (h1 n).1, (h1 n).2⟩
    have heq : ∀ n, E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α
        (E.toParams.shockPathF x₀shock N) n = 1 :=
      fun n => E.realizedRule_eq_one Eq hVS (hfeas n)
    refine ⟨N, h1, heq, ?_⟩
    intro n; rw [heq n]; exact E.xb_le_one

/-! ### R3 — the myopic comparator: transition-free, and comparator-invariant -/

/-- **The myopic stage problem is literally transition-free.** Two members of
the family with the same payoff coefficients — and arbitrary, possibly
different, transitions `F` — pose the same myopic stage problem. -/
theorem myopic_problem_transition_free (E₁ E₂ : SymbolicEconomyF)
    (hq : E₁.q = E₂.q) (hu₀ : E₁.u₀ = E₂.u₀) (hk : E₁.k = E₂.k) (hr : E₁.r = E₂.r)
    (hℓ : E₁.ℓ = E₂.ℓ) (hc : E₁.c = E₂.c) (hn : E₁.n = E₂.n) (hv : E₁.v = E₂.v) :
    E₁.toParams.σ = E₂.toParams.σ ∧ E₁.toParams.U_T = E₂.toParams.U_T := by
  constructor
  · rw [toParams_σ, toParams_σ, hq, hu₀, hk, hr]
  · rw [toParams_U_T, toParams_U_T, hℓ, hc, hn, hv]

/-- **EVERY myopic feedback equilibrium realises no sanction** — not merely
the canonical one. This is what makes the comparator swap immaterial. -/
theorem any_myopic_sigma_eq_zero (hk_strict : E.u₀ + E.r < E.k)
    (M : E.toParams.MyopicFeedbackEquilibrium) {x : ℝ} (hx : x ∈ Sanctions.S) :
    E.toParams.σ x (M.α x) = 0 :=
  E.myopic_argmax_sigma_eq_zero hk_strict hx (M.α_mem x hx) (M.α_opt x hx)

/-- **Comparator invariance.** Any two myopic comparators realise the same
sanction at every feasible state, so the reroute's swap of `C.M` for
`myopicFeedbackEquilibrium_canonical` changes nothing. -/
theorem myopic_comparator_invariant (hk_strict : E.u₀ + E.r < E.k)
    (M M' : E.toParams.MyopicFeedbackEquilibrium) :
    ∀ x ∈ Sanctions.S,
      E.toParams.myopicEquilibriumRule M x
        = E.toParams.myopicEquilibriumRule M' x := by
  intro x hx
  show E.toParams.σ x (M.α x) = E.toParams.σ x (M'.α x)
  rw [E.any_myopic_sigma_eq_zero hk_strict M hx,
    E.any_myopic_sigma_eq_zero hk_strict M' hx]

/-- **Maximal regime separation against an ARBITRARY myopic comparator.**
General in `F`. It keeps the strict placation margin `u₀ + r < k`, because it
asserts a zero myopic sanction at the top state `x = 1` too. -/
theorem regime_separation_any_myopic
    (hxb_pos : 0 < E.xb) (hk_strict : E.u₀ + E.r < E.k) :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT ∧ Eq.V_S ∈ E.carrierS
      ∧ ∀ M : E.toParams.MyopicFeedbackEquilibrium, ∀ x ∈ Sanctions.S,
          E.toParams.myopicEquilibriumRule M x = 0
          ∧ E.toParams.dynamicEquilibriumRule Eq x = 1 := by
  obtain ⟨Eq, hVT, hVS, _hG1, _hG2, _hG3⟩ :=
    (E.certificateMS hxb_pos).three_goals_local_MS_generalF
      (p := E.toParams) E.hF_top
  exact ⟨Eq, hVT, hVS, fun M x hx =>
    ⟨E.any_myopic_sigma_eq_zero hk_strict M hx,
     E.σ_dyn_top_eq_one hVS hx (Eq.α_mem x hx)⟩⟩

/-! ### R3′ — the family's own optimised myopic comparator (plan item BJ4.6)

`any_myopic_sigma_eq_zero` needs the strict placation margin because it covers
every myopic equilibrium, at the top state too. The affine family states maximal
regime separation against its own optimised myopic comparator
`SymbolicEconomy.symMyopic`, which needs no margin. The general family has the
same comparator: the myopic problem does not see `F`
(`myopic_problem_transition_free`), so the affine construction transfers
verbatim. -/

/-- **The family's own myopic feedback equilibrium.** The myopic Target complies
exactly enough, `a = (u₀ + r·x)/k`, to zero the static Sender's sanction, and
that is its stage argmax: the compliance it buys never costs more than the
sanction pain it avoids (`ℓ ≤ c − n·x` and `q ≤ k`). Rule 1: `α_opt` is proved,
not assumed, by the raw-coefficient lemma `symMyopic_isMaxOn` that the affine
`SymbolicEconomy.symMyopic` also reads. Transition-free, hence general in
`F`. -/
def symMyopic : E.toParams.MyopicFeedbackEquilibrium where
  α := E.myopicAlpha
  α_mem := fun _ hx => E.myopicAlpha_mem hx
  α_opt := by
    intro x hx
    change IsMaxOn (fun a => symU_T E.ℓ E.c E.n E.v x a (symσ E.q E.u₀ E.k E.r x a))
      Sanctions.I ((E.u₀ + E.r * x) / E.k)
    exact symMyopic_isMaxOn E.hq E.k_pos E.q_lt_k.le E.hℓ
      (by nlinarith [E.hcn, mul_nonneg E.hn (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x)])
      (by nlinarith [E.hk, E.r_pos, hx.2])

/-- **The family's own myopic regime imposes no sanction at any state.** No
placation margin is needed: the myopic compliance zeroes the static sanction
by construction. Transition-free, hence general in `F`. -/
theorem symMyopic_rule_eq_zero (x : ℝ) :
    E.toParams.myopicEquilibriumRule E.symMyopic x = 0 :=
  E.myopic_sigma_eq_zero x

/-! ### R6 — equilibrium value feedback from Sender patience (plan item BJ4.6)

`prop:equilibrium-patience-feedback` on the general family: "share `δ`" becomes
"share `F`". At every equilibrium whose Sender value lies in the carrier, the
Sender plays the full sanction and the Target full defiance at every feasible
state (`eq_α_eq_zero`), so both value functions solve corner Bellman equations
along the constant action pair `(a, s) = (0, 1)` (`eq_V_S_bellman`,
`eq_V_T_bellman`). The patience identities then follow with no functional form
for `F`, proved directly from those two Bellman equations. They state on the
family what `senderValue_patience_decomposition_of_bellman` and its siblings
(`Theory/LockIn/LockInComparativeStatics.lean`) state abstractly, without being
derived from them; the affine `symbolic_equilibrium_feedback_decomposition` and
siblings are separate closed-form statements about `vS` and `VTstar`, consistent
with these at `F = affineF δ`. The equilibria are any carrier equilibria: within-carrier
uniqueness is not used. General in `F`. -/

/-- **The Target's top-selector integrand in closed form** on the carrier: with
the Sender at the full sanction, compliance only costs `ℓ` per unit. The
top-selector analogue of `joint_T_integrand_eq`. General in `F`. -/
theorem joint_T_top_integrand_eq (V_T : AbstractGame.Params.Val)
    {V_S : AbstractGame.Params.Val} (hV_S : V_S ∈ E.carrierS)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Sanctions.I) :
    E.toParams.joint_T_top_integrand V_T V_S x a
      = -E.ℓ * a + (E.stageT0 + E.stageSlopeT * x)
        + E.βT * V_T (Sanctions.clipS' (E.F x 1)) := by
  have hσ := E.σ_dyn_top_eq_one hV_S hx ha
  simp only [AbstractGame.Params.joint_T_top_integrand, hσ]
  simp only [toParams_U_T, symU_T, toParams_β_T, toParams_F, stageT0, stageSlopeT]
  ring

/-- **At an equilibrium with a carrier Sender value, the Target fully defies**
at every feasible state: its policy is `α x = 0`. Complying costs `ℓ > 0` per
unit and does not move the Sender off the full sanction. General in `F`. -/
theorem eq_α_eq_zero (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS : Eq.V_S ∈ E.carrierS) {x : ℝ} (hx : x ∈ Sanctions.S) : Eq.α x = 0 := by
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_refl 0, zero_le_one⟩
  have hmem := Eq.α_mem x hx
  have hopt : E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S x 0
      ≤ E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S x (Eq.α x) :=
    isMaxOn_iff.mp (Eq.α_opt_top x hx) 0 h0I
  rw [E.joint_T_top_integrand_eq Eq.V_T hVS hx h0I,
    E.joint_T_top_integrand_eq Eq.V_T hVS hx hmem] at hopt
  have hℓ := E.hℓ
  have h0 : Eq.α x ≤ 0 := by nlinarith [hmem.1]
  exact le_antisymm h0 hmem.1

/-- **The Sender's corner Bellman equation at an equilibrium**: with a carrier
Sender value, `V_S(y) = U_S(y, 0, 1) + β_S·V_S(F(y, 1))` at every feasible
state. General in `F`. -/
theorem eq_V_S_bellman (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS : Eq.V_S ∈ E.carrierS) (y : ↥(Sanctions.S : Set ℝ)) :
    Eq.V_S y = E.stageS0 + E.stageSlopeS * y.val
      + E.βS * Eq.V_S (Sanctions.clipS' (E.F y.val 1)) := by
  have h1I : (1 : ℝ) ∈ Sanctions.I := ⟨zero_le_one, le_refl 1⟩
  have hα := E.eq_α_eq_zero Eq hVS y.property
  have hmono := E.senderObj_strictMonoOn hVS y.property (Eq.α_mem y.val y.property)
  have hmax : IsMaxOn
      (fun s => E.toParams.U_S y.val (Eq.α y.val) s
        + E.toParams.β_S * Eq.V_S (Sanctions.clipS' (E.toParams.F y.val s)))
      Sanctions.I 1 := by
    rw [isMaxOn_iff]
    intro s hs
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · rw [heq]
    · exact le_of_lt (hmono hs h1I hlt)
  have hfix : Eq.V_S y = E.toParams.bellmanS_BCF Eq.α Eq.hα Eq.V_S y :=
    DFunLike.congr_fun Eq.V_S_fix y
  rw [hfix, WitnessKit.bellmanS_image_of_isMaxOn (p := E.toParams) Eq.hα Eq.V_S y
    h1I hmax, hα]
  simp only [toParams_U_S, symU_S, toParams_β_S, toParams_F, stageS0, stageSlopeS]
  ring

/-- **The Target's corner Bellman equation at an equilibrium**: with a carrier
Sender value, `V_T(y) = U_T(y, 0, 1) + β_T·V_T(F(y, 1))` at every feasible
state. General in `F`. -/
theorem eq_V_T_bellman (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS : Eq.V_S ∈ E.carrierS) (y : ↥(Sanctions.S : Set ℝ)) :
    Eq.V_T y = E.stageT0 + E.stageSlopeT * y.val
      + E.βT * Eq.V_T (Sanctions.clipS' (E.F y.val 1)) := by
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_refl 0, zero_le_one⟩
  have hgt : IsGreatest
      ((fun a => E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S y.val a)
        '' Sanctions.I)
      (E.stageT0 + E.stageSlopeT * y.val
        + E.βT * Eq.V_T (Sanctions.clipS' (E.F y.val 1))) := by
    constructor
    · refine ⟨0, h0I, ?_⟩
      change E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S y.val 0 = _
      rw [E.joint_T_top_integrand_eq Eq.V_T hVS y.property h0I]
      ring
    · rintro z ⟨a, ha, rfl⟩
      change E.toParams.joint_T_top_integrand Eq.V_T Eq.V_S y.val a ≤ _
      rw [E.joint_T_top_integrand_eq Eq.V_T hVS y.property ha]
      linarith [mul_nonneg E.hℓ.le ha.1]
  rw [Eq.V_T_fix_top y, hgt.csSup_eq]

/-- **A corner Bellman equation has at most one bounded solution.** If two
bounded value functions both satisfy `V(y) = g(y) + β·V(φ(y))` with `0 ≤ β < 1`,
they are equal: their gap at any state is at most `β` times their sup gap. The
uniqueness half of the Banach fixed-point theorem, for one affine operator.
Free of the economy, and general in `F` (the successor map `φ` is
arbitrary). -/
theorem corner_bellman_unique {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {g : ℝ → ℝ} {φ : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.S : Set ℝ)}
    {V W : AbstractGame.Params.Val}
    (hV : ∀ y, V y = g y.val + β * V (φ y)) (hW : ∀ y, W y = g y.val + β * W (φ y)) :
    V = W := by
  have hd : ∀ y, dist (V y) (W y) ≤ β * dist V W := by
    intro y
    rw [hV y, hW y, Real.dist_eq,
      show g y.val + β * V (φ y) - (g y.val + β * W (φ y))
        = β * (V (φ y) - W (φ y)) by ring,
      abs_mul, abs_of_nonneg hβ0, ← Real.dist_eq]
    exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.dist_coe_le_dist _) hβ0
  have hle : dist V W ≤ β * dist V W :=
    (BoundedContinuousFunction.dist_le (mul_nonneg hβ0 dist_nonneg)).mpr hd
  have hnn : 0 ≤ dist V W := dist_nonneg
  have h0 : dist V W = 0 := le_antisymm (by nlinarith) hnn
  exact dist_eq_zero.mp h0

/-- **Equilibrium feedback decomposition on the general family.** For two
members that share the transition `F` and the Sender's corner stage payoff, and
any equilibria whose Sender values lie in the carriers, the change in the
Sender's equilibrium value at any state splits into a **direct patience effect**
(the higher weight `β₂ − β₁` on the same continuation) and a **continuation
feedback effect** (the old weight `β₁` on the change in the continuation value
itself). "Share `δ`" of the affine statement
(`symbolic_equilibrium_feedback_decomposition`) becomes "share `F`". General in
`F`. -/
theorem equilibrium_feedback_decomposition (E₁ E₂ : SymbolicEconomyF)
    (hF : E₁.F = E₂.F)
    (h0 : E₁.stageS0 = E₂.stageS0) (hsl : E₁.stageSlopeS = E₂.stageSlopeS)
    (Eq₁ : E₁.toParams.FeedbackStackelbergEquilibriumTop)
    (Eq₂ : E₂.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS₁ : Eq₁.V_S ∈ E₁.carrierS) (hVS₂ : Eq₂.V_S ∈ E₂.carrierS)
    (y : ↥(Sanctions.S : Set ℝ)) :
    Eq₂.V_S y - Eq₁.V_S y
      = (E₂.βS - E₁.βS) * Eq₂.V_S (Sanctions.clipS' (E₂.F y.val 1))
        + E₁.βS * (Eq₂.V_S (Sanctions.clipS' (E₂.F y.val 1))
            - Eq₁.V_S (Sanctions.clipS' (E₂.F y.val 1))) := by
  have h₁ := E₁.eq_V_S_bellman Eq₁ hVS₁ y
  have h₂ := E₂.eq_V_S_bellman Eq₂ hVS₂ y
  rw [hF, h0, hsl] at h₁
  linarith

/-- **The lock-in value is the corner flow capitalised**: at any equilibrium
with a carrier Sender value, `V_S(1) = U_S(1, 0, 1)/(1 − β_S)`. The top state is
absorbing under the full sanction because `F(1, 1) = 1` (`F_diag`), so no
functional form for `F` is used. -/
theorem lockinValue_eq (Eq : E.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS : Eq.V_S ∈ E.carrierS) :
    Eq.V_S (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
      = E.cornerStagePayoff / (1 - E.βS) := by
  have hne : (1 : ℝ) - E.βS ≠ 0 := by linarith [E.hβS1]
  have h := E.eq_V_S_bellman Eq hVS ⟨1, by constructor <;> norm_num⟩
  dsimp only at h
  have htop : Sanctions.clipS' (E.F 1 1)
      = (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ)) := by
    apply Subtype.ext
    rw [Sanctions.clipS'_val_eq_of_mem (by rw [E.F_diag 1]; constructor <;> norm_num),
      E.F_diag 1]
  rw [htop] at h
  rw [eq_div_iff hne]
  change _ = E.stageS0 + E.stageSlopeS
  linear_combination h

/-- **Lock-in amplification on the general family.** For two members with the
same corner stage payoff, and any carrier equilibria, the gain in lock-in value
from extra Sender patience, scaled by the old horizon factor `1 − β₁`, equals
the patience increment times the new lock-in value. No shared transition is
needed: the top state is absorbing for every `F`. General in `F`. -/
theorem lockin_amplification (E₁ E₂ : SymbolicEconomyF)
    (hC : E₁.cornerStagePayoff = E₂.cornerStagePayoff)
    (Eq₁ : E₁.toParams.FeedbackStackelbergEquilibriumTop)
    (Eq₂ : E₂.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS₁ : Eq₁.V_S ∈ E₁.carrierS) (hVS₂ : Eq₂.V_S ∈ E₂.carrierS) :
    (1 - E₁.βS) * (Eq₂.V_S (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
        - Eq₁.V_S (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ)))
      = (E₂.βS - E₁.βS)
          * Eq₂.V_S (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ)) := by
  have hne₁ : (1 : ℝ) - E₁.βS ≠ 0 := by linarith [E₁.hβS1]
  have hne₂ : (1 : ℝ) - E₂.βS ≠ 0 := by linarith [E₂.hβS1]
  rw [E₁.lockinValue_eq Eq₁ hVS₁, E₂.lockinValue_eq Eq₂ hVS₂, hC]
  field_simp
  ring

/-- **Lock-in monotonicity in Sender patience is exactly a sign condition**, on
the general family: with the same corner stage payoff and `β₁ < β₂`, the more
patient Sender's lock-in value is strictly higher **if and only if** the corner
stage payoff is positive. General in `F`. -/
theorem lockin_strict_iff (E₁ E₂ : SymbolicEconomyF)
    (hC : E₁.cornerStagePayoff = E₂.cornerStagePayoff) (hβ : E₁.βS < E₂.βS)
    (Eq₁ : E₁.toParams.FeedbackStackelbergEquilibriumTop)
    (Eq₂ : E₂.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS₁ : Eq₁.V_S ∈ E₁.carrierS) (hVS₂ : Eq₂.V_S ∈ E₂.carrierS) :
    Eq₁.V_S (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
        < Eq₂.V_S (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
      ↔ 0 < E₁.cornerStagePayoff := by
  have hne₁ : (0 : ℝ) < 1 - E₁.βS := by linarith [E₁.hβS1]
  have hne₂ : (0 : ℝ) < 1 - E₂.βS := by linarith [E₂.hβS1]
  rw [E₁.lockinValue_eq Eq₁ hVS₁, E₂.lockinValue_eq Eq₂ hVS₂, hC,
    div_lt_div_iff₀ hne₁ hne₂]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **Patience strictly raises the lock-in value, unconditionally on the general
family.** The sign condition of `lockin_strict_iff` holds at every member: the
corner stage payoff is positive (`cornerStagePayoff_pos`, which since plan item
BJ4.1 follows from `hCorner` alone). General in `F`. -/
theorem lockin_strict (E₁ E₂ : SymbolicEconomyF)
    (hC : E₁.cornerStagePayoff = E₂.cornerStagePayoff) (hβ : E₁.βS < E₂.βS)
    (Eq₁ : E₁.toParams.FeedbackStackelbergEquilibriumTop)
    (Eq₂ : E₂.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS₁ : Eq₁.V_S ∈ E₁.carrierS) (hVS₂ : Eq₂.V_S ∈ E₂.carrierS) :
    Eq₁.V_S (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ))
      < Eq₂.V_S (⟨1, by constructor <;> norm_num⟩ : ↥(Sanctions.S : Set ℝ)) :=
  (lockin_strict_iff E₁ E₂ hC hβ Eq₁ Eq₂ hVS₁ hVS₂).mpr E₁.cornerStagePayoff_pos

/-- **The Target's equilibrium value is invariant to Sender patience**, on the
general family. Two members that share the transition, the Target's discount
factor and the Target's corner stage payoff (`−c` and `n + v`) have the same
Target value at any carrier equilibria, whatever their Sender discount factors
(and whatever their compliance costs `ℓ`). Both values solve the same corner
Bellman equation, whose bounded solution is unique (`corner_bellman_unique`):
the Sender's corner response does not depend on `β_S`, so the Target's Bellman
operator never sees it. "Share `δ`" of the affine statement
(`symbolic_VTstar_βS_invariant`) becomes "share `F`". General in `F`. -/
theorem VT_βS_invariant (E₁ E₂ : SymbolicEconomyF)
    (hF : E₁.F = E₂.F) (hβT : E₁.βT = E₂.βT)
    (hT0 : E₁.stageT0 = E₂.stageT0) (hTsl : E₁.stageSlopeT = E₂.stageSlopeT)
    (Eq₁ : E₁.toParams.FeedbackStackelbergEquilibriumTop)
    (Eq₂ : E₂.toParams.FeedbackStackelbergEquilibriumTop)
    (hVS₁ : Eq₁.V_S ∈ E₁.carrierS) (hVS₂ : Eq₂.V_S ∈ E₂.carrierS) :
    Eq₁.V_T = Eq₂.V_T := by
  refine corner_bellman_unique E₂.hβT0 E₂.hβT1
    (g := fun z => E₂.stageT0 + E₂.stageSlopeT * z)
    (φ := fun y => Sanctions.clipS' (E₂.F y.val 1)) (fun y => ?_) (fun y => ?_)
  · have h := E₁.eq_V_T_bellman Eq₁ hVS₁ y
    rw [hF, hβT, hT0, hTsl] at h
    exact h
  · exact E₂.eq_V_T_bellman Eq₂ hVS₂ y

end SymbolicEconomyF

/-! ### R4 — non-vacuity of the recoveries at the non-affine witness -/

/-- **The full general-`F` conclusion set at the non-affine witness
`wobbleEconMS`** (pinned headline row 12b). General in `F`: the witness's
transition is the non-affine `wobbleF (1/2) (1/100)`.

**Edited in place (plan item BJ4.1, 2026-10-07)**, with
`three_goals_generalF_full`: the two sanction-floor conjuncts `s̄ ≤ σ_n` were
dropped, because the family no longer carries `s̄` and `σ_n = 1` is still
stated. -/
theorem wobbleEconMS_three_goals_full :
    ∃ Eq : wobbleEconMS.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ wobbleEconMS.carrierT
      ∧ Eq.V_S ∈ wobbleEconMS.carrierS
      ∧ (∀ x₀ ∈ Set.Icc wobbleEconMS.xb 1,
          (∀ n, wobbleEconMS.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc wobbleEconMS.xb 1) ∧
          (∀ n, wobbleEconMS.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀ n = 1) ∧
          (∀ n, wobbleEconMS.xb ≤ wobbleEconMS.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀ n) ∧
          Monotone (wobbleEconMS.toParams.dynamicTopLockInSanctionsF
                  Eq.V_S Eq.α x₀) ∧
          (∀ n, IsMaxOn
            (fun a => wobbleEconMS.toParams.joint_T_top_integrand Eq.V_T Eq.V_S
                        (wobbleEconMS.toParams.dynamicTopLockInPathF
                          Eq.V_S Eq.α x₀ n) a)
            Sanctions.I
            (Eq.α (wobbleEconMS.toParams.dynamicTopLockInPathF
                     Eq.V_S Eq.α x₀ n))))
      ∧ (∀ x ∈ Set.Icc wobbleEconMS.xb 1,
           wobbleEconMS.toParams.σ x
               (wobbleEconMS.toParams.myopicFeedbackEquilibrium_canonical.α x)
             ≤ wobbleEconMS.toParams.dynamicTopRealizedRule Eq.V_S Eq.α x)
      ∧ (∀ x₀shock : ℝ, 0 ≤ x₀shock → x₀shock ≤ 1 →
          ∃ N : ℕ,
            (∀ n, wobbleEconMS.toParams.dynamicTopLockInPathF Eq.V_S Eq.α
                    (wobbleEconMS.toParams.shockPathF x₀shock N) n
                    ∈ Set.Icc wobbleEconMS.xb 1) ∧
            (∀ n, wobbleEconMS.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α
                    (wobbleEconMS.toParams.shockPathF x₀shock N) n = 1) ∧
            (∀ n, wobbleEconMS.xb ≤
                  wobbleEconMS.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α
                    (wobbleEconMS.toParams.shockPathF x₀shock N) n)) :=
  wobbleEconMS.three_goals_generalF_full wobbleEconMS_xb_pos

theorem wobbleEconMS_regime_separation_any_myopic :
    ∃ Eq : wobbleEconMS.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ wobbleEconMS.carrierT ∧ Eq.V_S ∈ wobbleEconMS.carrierS
      ∧ ∀ M : wobbleEconMS.toParams.MyopicFeedbackEquilibrium,
          ∀ x ∈ Sanctions.S,
            wobbleEconMS.toParams.myopicEquilibriumRule M x = 0
            ∧ wobbleEconMS.toParams.dynamicEquilibriumRule Eq x = 1 :=
  wobbleEconMS.regime_separation_any_myopic wobbleEconMS_xb_pos
    wobbleEconMS_k_strict

/-! ### R5 — the legacy affine route is provably unavailable at the witness

`three_goals_local_uniform_starts` hard-requires `hF : p.F = affineF p.δ`.
At `wobbleEconMS` that hypothesis is FALSE, so the reroute is forced, not
elective. -/

theorem wobbleEconMS_legacy_route_unavailable :
    wobbleEconMS.toParams.F ≠ AbstractGame.affineF wobbleEconMS.toParams.δ :=
  wobbleEconMS_F_ne_affineF _

end

end Examples

end Sanctions

#print axioms Sanctions.Examples.wobbleEconMS_legacy_route_unavailable
#print axioms Sanctions.Examples.SymbolicEconomyF.realizedRule_eq_one
#print axioms Sanctions.Examples.SymbolicEconomyF.three_goals_generalF_full
#print axioms Sanctions.Examples.SymbolicEconomyF.myopic_problem_transition_free
#print axioms Sanctions.Examples.SymbolicEconomyF.any_myopic_sigma_eq_zero
#print axioms Sanctions.Examples.SymbolicEconomyF.myopic_comparator_invariant
#print axioms Sanctions.Examples.SymbolicEconomyF.regime_separation_any_myopic
#print axioms Sanctions.Examples.wobbleEconMS_three_goals_full
#print axioms Sanctions.Examples.wobbleEconMS_regime_separation_any_myopic
#print axioms Sanctions.Examples.SymbolicEconomyF.symMyopic
#print axioms Sanctions.Examples.SymbolicEconomyF.symMyopic_rule_eq_zero
#print axioms Sanctions.Examples.SymbolicEconomyF.eq_α_eq_zero
#print axioms Sanctions.Examples.SymbolicEconomyF.eq_V_S_bellman
#print axioms Sanctions.Examples.SymbolicEconomyF.eq_V_T_bellman
#print axioms Sanctions.Examples.SymbolicEconomyF.corner_bellman_unique
#print axioms Sanctions.Examples.SymbolicEconomyF.equilibrium_feedback_decomposition
#print axioms Sanctions.Examples.SymbolicEconomyF.lockinValue_eq
#print axioms Sanctions.Examples.SymbolicEconomyF.lockin_amplification
#print axioms Sanctions.Examples.SymbolicEconomyF.lockin_strict_iff
#print axioms Sanctions.Examples.SymbolicEconomyF.lockin_strict
#print axioms Sanctions.Examples.SymbolicEconomyF.VT_βS_invariant
