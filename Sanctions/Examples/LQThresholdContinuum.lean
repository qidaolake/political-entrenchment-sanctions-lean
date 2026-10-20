/-
Sanctions/Examples/LQThresholdContinuum.lean

**At the threshold `β_T = β_T*` the benchmark has a continuum of constant-compliance equilibria
joining relief to full defiance** (step 2, target 2c, part B; 2026-10-10; plan `STEP2_2c.md`,
Proposition LQ-2).

In the linear–quadratic benchmark (`LQBenchmark.lean`), at `β_T = β_T*` the net weight of the
sanction in the Target's objective is exactly `ℓq/k` (`k_mul_pT_of_threshold`): a unit of
compliance below the relief price `A/k` costs `ℓ` and lowers the sanction by `k/q`, worth exactly
`ℓ`. So the Target is indifferent among all compliance levels in `[0, A/k]`
(`joint_threshold_eq`, `joint_threshold_le`), and for every `a₀ ∈ [0, A/k]` the profile

    α ≡ a₀,   s ≡ (A − k a₀)/q,   V_S = g_S x + (q/2)((A − k a₀)/q)²/(1 − β_S),
    V_T = g_T x − ℓ(A/k)/(1 − β_T),

is a top-selector equilibrium (`constEquilibrium`). The Target value does not depend on `a₀`.
At `a₀ = A/k` it is relief (zero sanction), at `a₀ = 0` full defiance, and the steady state
`(A − k a₀)/q` falls strictly in `a₀` from `A/q` to `0` (`threshold_continuum`). This is the
equality case that `relief_iff` and `defiance_iff` leave with both regimes present.

**Scope.** The linear–quadratic benchmark only, at the single discount `β_T = β_T*`; it rests on
the Target's indifference, which needs the linear compliance cost. **Rule 3.** No new
hypothesis. **Rule 1.** The response is the unique Sender maximiser at every compliance level,
and the policy a Target maximiser at every state (weakly). **Rule 22.** AFFINE.
-/
import Sanctions.Examples.LQBenchmark

namespace Sanctions
namespace Examples

open Set Filter Topology AbstractGame

noncomputable section

namespace LQData

variable (P : LQData)

/-- **At `β_T = β_T*` the net sanction weight is `ℓq/k`**: `k (c − β_T δ g_T) = ℓ q`, under
the stage relief margin.
Scope: linear–quadratic benchmark only. -/
theorem k_mul_pT_of_threshold (hSR : P.E.StageRelief) (hβ : P.βT = P.E.betaStar) :
    P.k * P.pT = P.ℓ * P.q := by
  have h1 : P.βT * P.δ * P.gT ≤ P.D := (P.βT_δ_gT_le_iff hSR).2 (le_of_eq hβ)
  have heq : P.βT * P.δ * P.gT = P.D := by
    rcases lt_or_eq_of_le h1 with h | h
    · exact absurd ((P.βT_δ_gT_lt_iff hSR).1 h) (by rw [hβ, P.betaStar_eq]; exact lt_irrefl _)
    · exact h
  unfold pT
  rw [heq]
  unfold D
  rw [sub_sub_cancel, mul_div_cancel₀ _ P.hk.ne']

/-- **On the compliance plateau the Target is indifferent**: at `β_T = β_T*`, for every
compliance `a ≤ A/k`, the Target's objective against `g_T x + C_T` and `g_S x + C` equals its
value at the relief price, the state terms minus `ℓ(A/k)`.
Scope: linear–quadratic benchmark only. -/
theorem joint_threshold_eq (hInt : P.A < P.q) (hpT : P.k * P.pT = P.ℓ * P.q) (C CT : ℝ)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) (haA : a ≤ P.A / P.k) :
    P.E.toParams.joint_T_top_integrand (ChordEconomy.affBCF P.gT CT)
        (ChordEconomy.affBCF P.gS C) x a
      = (P.v * x + P.βT * P.gT * (1 - P.δ) * x + P.βT * CT) - P.ℓ * (P.A / P.k) := by
  rw [P.joint_aff C CT hInt hx ha, max_eq_right ((P.vtx_nonneg_iff a).2 haA)]
  have hkv := P.q_mul_vtx a
  have hkA : P.k * (P.A / P.k) = P.A := mul_div_cancel₀ _ P.hk.ne'
  have key : P.k * (P.ℓ * a + P.pT * P.vtx a) = P.k * (P.ℓ * (P.A / P.k)) := by
    linear_combination (P.vtx a) * hpT + P.ℓ * hkv - P.ℓ * hkA
  have := mul_left_cancel₀ P.hk.ne' key
  linarith

/-- **Above the plateau compliance is pure cost**: at `β_T = β_T*` the Target's objective at
every compliance level is at most its plateau value.
Scope: linear–quadratic benchmark only. -/
theorem joint_threshold_le (hInt : P.A < P.q) (hpT : P.k * P.pT = P.ℓ * P.q) (C CT : ℝ)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    P.E.toParams.joint_T_top_integrand (ChordEconomy.affBCF P.gT CT)
        (ChordEconomy.affBCF P.gS C) x a
      ≤ (P.v * x + P.βT * P.gT * (1 - P.δ) * x + P.βT * CT) - P.ℓ * (P.A / P.k) := by
  rcases le_total a (P.A / P.k) with haA | haA
  · exact le_of_eq (P.joint_threshold_eq hInt hpT C CT hx ha haA)
  · rw [P.joint_aff C CT hInt hx ha]
    have hv : P.vtx a ≤ 0 := by
      have hkv := P.q_mul_vtx a
      have hka : P.A ≤ P.k * a := by
        have := (div_le_iff₀ P.hk).1 haA
        linarith
      by_contra hpos
      nlinarith [mul_pos P.hq (not_le.mp hpos)]
    rw [max_eq_left hv]
    nlinarith [P.hℓ]

/-- The relief Target value in plateau form: `g_T x + c_R` is the state terms minus `ℓ(A/k)`.
Scope: linear–quadratic benchmark only. -/
theorem affBCF_gT_cR_eq (y : ↥(Sanctions.S : Set ℝ)) :
    ChordEconomy.affBCF P.gT P.cR y
      = (P.v * y.val + P.βT * P.gT * (1 - P.δ) * y.val + P.βT * P.cR) - P.ℓ * (P.A / P.k) := by
  rw [ChordEconomy.affBCF_apply]
  linear_combination y.val * P.gT_spec + P.cR_spec

/-- **The constant-compliance equilibrium at the threshold.** At `β_T = β_T*`, for a compliance
level `a₀ ∈ [0, A/k]`: Target policy `α ≡ a₀`, Sender value `g_S x + CS(a₀)`, Target value
`g_T x − ℓ(A/k)/(1 − β_T)`. The Sender's Bellman equation holds at its unique maximiser, the
vertex `(A − k a₀)/q`; the Target's because every compliance level up to `A/k` attains its
maximum.
Scope: linear–quadratic benchmark only (at the single discount `β_T = β_T*`). -/
def constEquilibrium (hInt : P.E.Interior) (hSR : P.E.StageRelief) (hP : P.E.Placable)
    (hβ : P.βT = P.E.betaStar) (a₀ : ℝ) (ha₀ : a₀ ∈ Icc (0 : ℝ) (P.A / P.k)) :
    P.E.toParams.FeedbackStackelbergEquilibriumTop where
  V_T := ChordEconomy.affBCF P.gT P.cR
  V_S := ChordEconomy.affBCF P.gS (P.CS a₀)
  α := fun _ => a₀
  hα := continuous_const
  α_mem := fun _ _ => ⟨ha₀.1, le_trans ha₀.2 (P.Ak_mem ((P.placable_iff).1 hP)).2⟩
  V_S_fix := by
    have hI : a₀ ∈ Sanctions.I := ⟨ha₀.1, le_trans ha₀.2 (P.Ak_mem ((P.placable_iff).1 hP)).2⟩
    exact (P.bellmanS_const_fix ((P.interior_iff).1 hInt) hI ((P.vtx_nonneg_iff a₀).2 ha₀.2)).symm
  V_T_fix_top := by
    intro y
    have hInt' := (P.interior_iff).1 hInt
    have hpT := P.k_mul_pT_of_threshold hSR hβ
    have hI : a₀ ∈ Sanctions.I := ⟨ha₀.1, le_trans ha₀.2 (P.Ak_mem ((P.placable_iff).1 hP)).2⟩
    have hgt : IsGreatest ((fun a => P.E.toParams.joint_T_top_integrand
        (ChordEconomy.affBCF P.gT P.cR) (ChordEconomy.affBCF P.gS (P.CS a₀)) y.val a)
        '' Sanctions.I) (ChordEconomy.affBCF P.gT P.cR y) := by
      refine ⟨⟨a₀, hI, ?_⟩, ?_⟩
      · dsimp only
        rw [P.joint_threshold_eq hInt' hpT (P.CS a₀) P.cR y.property hI ha₀.2, P.affBCF_gT_cR_eq]
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        rw [P.affBCF_gT_cR_eq]
        exact P.joint_threshold_le hInt' hpT (P.CS a₀) P.cR y.property ha
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => by
    have hInt' := (P.interior_iff).1 hInt
    have hpT := P.k_mul_pT_of_threshold hSR hβ
    have hI : a₀ ∈ Sanctions.I := ⟨ha₀.1, le_trans ha₀.2 (P.Ak_mem ((P.placable_iff).1 hP)).2⟩
    intro a ha
    change P.E.toParams.joint_T_top_integrand (ChordEconomy.affBCF P.gT P.cR)
        (ChordEconomy.affBCF P.gS (P.CS a₀)) x a
      ≤ P.E.toParams.joint_T_top_integrand (ChordEconomy.affBCF P.gT P.cR)
        (ChordEconomy.affBCF P.gS (P.CS a₀)) x a₀
    rw [P.joint_threshold_eq hInt' hpT (P.CS a₀) P.cR hx hI ha₀.2]
    exact P.joint_threshold_le hInt' hpT (P.CS a₀) P.cR hx ha

/-- **The realised sanction of the constant-compliance equilibrium is `(A − k a₀)/q`** at every
state.
Scope: linear–quadratic benchmark only. -/
theorem constEquilibrium_rule (hInt : P.E.Interior) (hSR : P.E.StageRelief) (hP : P.E.Placable)
    (hβ : P.βT = P.E.betaStar) (a₀ : ℝ) (ha₀ : a₀ ∈ Icc (0 : ℝ) (P.A / P.k)) {x : ℝ}
    (hx : x ∈ Sanctions.I) :
    P.E.toParams.dynamicEquilibriumRule (P.constEquilibrium hInt hSR hP hβ a₀ ha₀) x
      = (P.A - P.k * a₀) / P.q := by
  have hI : a₀ ∈ Sanctions.I := ⟨ha₀.1, le_trans ha₀.2 (P.Ak_mem ((P.placable_iff).1 hP)).2⟩
  change P.E.toParams.σ_dyn_top (ChordEconomy.affBCF P.gS (P.CS a₀)) x a₀ = _
  rw [P.σ_aff (P.CS a₀) ((P.interior_iff).1 hInt) hx hI,
    max_eq_right ((P.vtx_nonneg_iff a₀).2 ha₀.2)]
  rfl

/-- **The threshold continuum** (plan LQ-1(c), LQ-2). In the linear–quadratic benchmark, under
interiority, the stage relief margin and placability, at `β_T = β_T*`:
(i) for every compliance level `a₀ ∈ [0, A/k]` there is a top-selector equilibrium whose policy
is `a₀` and whose realised sanction is `(A − k a₀)/q` at every state, and along it the state from
any `x₀ ∈ [0,1]` is `(A − k a₀)/q + (1 − δ)ᵗ(x₀ − (A − k a₀)/q)`, converging to the steady state
`(A − k a₀)/q`;
(ii) the endpoint `a₀ = A/k` is relief (zero sanction at every state) and the endpoint `a₀ = 0`
is full defiance;
(iii) the steady state strictly falls in `a₀`, so distinct compliance levels give distinct
equilibria and distinct long-run states, from `A/q` (defiance) down to `0` (relief).
Scope: linear–quadratic benchmark only (at the single discount `β_T = β_T*`). -/
theorem threshold_continuum (hInt : P.E.Interior) (hSR : P.E.StageRelief) (hP : P.E.Placable)
    (hβ : P.βT = P.E.betaStar) :
    (∀ a₀ ∈ Icc (0 : ℝ) (P.A / P.k), ∃ Eq : P.E.toParams.FeedbackStackelbergEquilibriumTop,
      (∀ x ∈ Sanctions.I, Eq.α x = a₀)
      ∧ (∀ x ∈ Sanctions.I, P.E.toParams.dynamicEquilibriumRule Eq x = (P.A - P.k * a₀) / P.q)
      ∧ (∀ x₀ ∈ Sanctions.I, ∀ t : ℕ,
          P.E.toParams.rulePathF (P.E.toParams.dynamicEquilibriumRule Eq) x₀ t
            = (P.A - P.k * a₀) / P.q + (1 - P.δ) ^ t * (x₀ - (P.A - P.k * a₀) / P.q)))
    ∧ (P.A - P.k * (P.A / P.k)) / P.q = 0 ∧ (P.A - P.k * 0) / P.q = P.A / P.q
    ∧ StrictAntiOn (fun a₀ => (P.A - P.k * a₀) / P.q) (Icc (0 : ℝ) (P.A / P.k)) := by
  refine ⟨fun a₀ ha₀ => ⟨P.constEquilibrium hInt hSR hP hβ a₀ ha₀, fun _ _ => rfl,
    fun x hx => P.constEquilibrium_rule hInt hSR hP hβ a₀ ha₀ hx,
    fun x₀ hx₀ t => P.rulePathF_eq_of_const_rule _
      (fun x hx => P.constEquilibrium_rule hInt hSR hP hβ a₀ ha₀ hx) hx₀ t⟩, ?_, ?_, ?_⟩
  · rw [mul_div_cancel₀ _ P.hk.ne', sub_self, zero_div]
  · rw [mul_zero, sub_zero]
  · intro a₁ _ a₂ _ hlt
    apply div_lt_div_of_pos_right _ P.hq
    nlinarith [mul_lt_mul_of_pos_left hlt P.hk]

end LQData

end

end Examples
end Sanctions
