/-
Sanctions/Examples/LQBenchmark.lean

**The linear–quadratic benchmark, characterised in both discount factors** (step 2, target 2c,
part A; 2026-10-10; plan `STEP2_2c.md`, Theorem LQ-1).

The benchmark is the quadratic–linear family at `r = n = 0` with partial adjustment
`x' = (1 − δ)x + δs`: Sender stage payoff `−(q/2)s² + s(u₀ − k a) + w x`, Target stage payoff
`−ℓ a − c s + v x`, discount factors `β_S`, `β_T`, every rate `δ ∈ (0,1)`. `LQData` collects
the ten coefficients with their signs; `LQData.toFcs` is the member of the existing family
`PlacableEconomyFcs` at those coefficients (chord constants `g_lo = g_hi = 1 − δ`,
`d_lo = d_hi = δ`, all moduli zero, supplied Sender modulus `σ_V = 0`), and `LQData.E` the
enriched chord economy. With `g_S = w/(1 − β_S(1 − δ))`, `A = u₀ + β_S δ g_S`,
`g_T = v/(1 − β_T(1 − δ))`, `D = c − ℓq/k` and `β_T* = D/(δv + (1 − δ)D)`:

1. **Closed forms** (`VS01_eq`, `zeroLevel_eq`, `VTrel_eq`, `VSstar_eq`, `VTdef_eq`): the
   zero-sanction Sender value is `g_S x`, the zero level is the constant `A/k`, the relief
   Target value is `g_T x − ℓA/(k(1 − β_T))`, the Sender value at full defiance is
   `g_S x + A²/(2q(1 − β_S))`, and the defiance-profile Target value is
   `g_T x − (c − β_T δ g_T)A/(q(1 − β_T))`. Each is the unique fixed point of the operator
   that defines it.
2. **Relief exists iff `β_T ≤ β_T*`** (`relief_iff`), with the exact relief test
   `exists_relief_equilibrium_iff` read at the closed forms. In particular **no equilibrium
   with zero sanctions exists above `β_T*`** (`no_relief_above`), where the class theorem
   `reliefExistence_lt_margin` excludes relief only from `c/(δv + c(1 − δ))` up, a strictly
   larger bound (`βstar_lt_margin`).
3. **Full defiance exists iff `β_T* ≤ β_T`** (`defiance_iff`): the nine-condition theorem
   `collapse_equilibrium_threshold_le_tight` at the benchmark.
4. **Relief is unique among equilibria with an affine Sender value** below `β_T*`
   (`relief_unique_carrier`): at the benchmark the two-sided carrier `carrierS2` is exactly the
   affine values of slope `g_S` within the norm bound `M_S` (`mem_carrierS2_iff`), and every
   equilibrium whose Sender value lies in it is the relief equilibrium. Equilibria outside that
   class are not classified here.
4b. **Mutual entrenchment** (`value_gaps`, `entrenchment`): the defiance-profile Target value
   exceeds the relief value by `A(β_T δ g_T − D)/(q(1 − β_T))`, so the Target weakly prefers it
   exactly when `β_T* ≤ β_T`; the Sender's value at defiance exceeds its zero-sanction value by
   `A²/(2q(1 − β_S)) > 0` at every `β_T`.
5. **Equilibrium levels** (`relief_policy_eq`, `defiance_rule_eq`, `rulePath_eq_of_const_rule`,
   `defiance_path_tendsto`): every zero-sanction equilibrium complies at `A/k` at every state;
   every full-defiance equilibrium sanctions at `A/q` at every state, and its state path
   converges to the steady state `A/q` at rate `1 − δ`.
6. **Comparative statics** (`lqAppetite_lt_of_βS_lt`, `_of_w_lt`, `_of_δ_lt`,
   `levels_lt_of_A_lt`, `comparative_statics_βS`, `_w`, `_δ`): the relief price `A/k`, the
   defiance sanction `A/q` and the defiance steady state `A/q` strictly increase in `β_S`, `w`
   and `δ`, with `∂A/∂β_S = δw/(1 − β_S(1 − δ))²`, `∂A/∂w = β_S δ/(1 − β_S(1 − δ))` and
   `∂A/∂δ = β_S(1 − β_S)w/(1 − β_S(1 − δ))²` (`hasDerivAt_lqAppetite_βS`, `_w`, `_δ`);
   `β_T*` does not depend on `β_S`, `w` or `u₀` (`betaStar_indep`).

The abstract companion (`CollapseReliefThreshold.lean`) proves item 2 on the general class under
the paper's nine tightness conditions; the proofs here are independent and use closed forms.

**Scope.** Everything here is the linear–quadratic benchmark (the family at `r = n = 0` with
the affine law); no statement is claimed beyond it. **Rule 3.** No new hypothesis: the fields
of `LQData` are the existing family's sign fields at `r = n = 0`, and interiority, placability
and the stage relief margin are the existing predicates `Interior`, `Placable`,
`StageRelief`. **Rule 22.** AFFINE: the transition is `affineF δ`. **Rule 1.** Every value is
derived as the fixed point of its operator; the Sender's response is the clipped vertex of a
strictly concave parabola (`σ_dyn_top_eq_clip`).
-/
import Sanctions.Examples.PlacableSenderCollapseInstance
import Sanctions.Examples.ExplicitEquilibriumKit

namespace Sanctions
namespace Examples

open Set Filter Topology AbstractGame Sanctions.Semiconcave Sanctions.TransitionChords

noncomputable section

/-! ## 0. The sanction chords of the affine law at a general rate -/

/-- **The affine law at rate `d` has lower sanction chord `d`**: `affineF d x s₂ −
affineF d x s₁ = d (s₂ − s₁)`. The general-rate form of `affineF_half_lo`.
Scope: general class (a fact about the affine law at any rate `d`). -/
theorem sanctionLowerChord_affineF (d : ℝ) : SanctionLowerChord (affineF d) d := by
  intro x s₁ s₂ _ _ _ _
  exact le_of_eq (by unfold affineF; ring)

/-- **The affine law at rate `d` has upper sanction chord `d`**. The general-rate form of
`affineF_half_hi`.
Scope: general class (a fact about the affine law at any rate `d`). -/
theorem sanctionUpperChord_affineF (d : ℝ) : SanctionUpperChord (affineF d) d := by
  intro x s₁ s₂ _ _ _ _
  exact le_of_eq (by unfold affineF; ring)

/-! ## 1. The benchmark data and its member of the family -/

/-- **The linear–quadratic benchmark's coefficients.** Adjustment rate `δ`, discount factors
`β_S`, `β_T`, Sender curvature `q`, appetite floor `u₀`, placation rate `k`, state slope `w`;
Target compliance cost `ℓ`, sanction pain `c`, state valuation `v`. The sign fields are those of
`PlacableEconomyF` at `r = n = 0` (`0 < q` is what the family's curvature margin reads at
`σ_V = M_s = 0`, `0 < c` its field `n < c` at `n = 0`). -/
structure LQData where
  δ : ℝ
  βS : ℝ
  βT : ℝ
  q : ℝ
  u₀ : ℝ
  k : ℝ
  w : ℝ
  ℓ : ℝ
  c : ℝ
  v : ℝ
  hδ0 : 0 < δ
  hδ1 : δ < 1
  hβS0 : 0 < βS
  hβS1 : βS < 1
  hβT0 : 0 < βT
  hβT1 : βT < 1
  hq : 0 < q
  hu₀ : 0 < u₀
  hk : 0 < k
  hw : 0 < w
  hℓ : 0 < ℓ
  hc : 0 < c
  hv : 0 < v

namespace LQData

variable (P : LQData)

/-- **The benchmark as a member of the quadratic–linear family**: transition `affineF δ`,
state chords `1 − δ`, sanction chords `δ`, all moduli zero, `r = n = 0`, `σ_V = 0`. -/
def toF : PlacableEconomyF where
  F := affineF P.δ
  F_continuous := affineF_continuous _
  F_mono_x := affineF_mono_x ⟨P.hδ0, P.hδ1⟩
  F_mono_s := affineF_mono_s ⟨P.hδ0, P.hδ1⟩
  F_diag := affineF_diag _
  glo := 1 - P.δ
  ghi := 1 - P.δ
  dlo := P.δ
  dhi := P.δ
  Mx := 0
  Mm := 0
  Ms := 0
  hbandAll := stateChordBandAll_of_eqOn_affineF (fun _ _ _ _ => rfl)
  hSlo := sanctionLowerChord_affineF P.δ
  hShi := sanctionUpperChord_affineF P.δ
  hFjsc := jointSemiconcaveOn_of_eqOn_affineF (fun _ _ _ _ => rfl) le_rfl le_rfl neg_zero.le
  hglo0 := by linarith [P.hδ1]
  hghi1 := by linarith [P.hδ0]
  hdlo0 := P.hδ0
  hMx0 := le_rfl
  hMm0 := le_rfl
  hMs0 := le_rfl
  Mcx := 0
  hMcx0 := le_rfl
  hFcx := semiconvexOnSet_state_of_eqOn_affineF (fun _ _ _ _ => rfl)
  Mmix := 0
  hFmix := mixedChordBound_of_eqOn_affineF (fun _ _ _ _ => rfl)
  δ := P.δ
  βS := P.βS
  βT := P.βT
  hδ0 := P.hδ0
  hδ1 := P.hδ1
  hβS0 := P.hβS0
  hβS1 := P.hβS1
  hβT0 := P.hβT0
  hβT1 := P.hβT1
  q := P.q
  u₀ := P.u₀
  k := P.k
  r := 0
  w := P.w
  ℓ := P.ℓ
  c := P.c
  n := 0
  v := P.v
  hu₀ := P.hu₀
  hr := le_rfl
  hw := P.hw
  hℓ := P.hℓ
  hn := le_rfl
  SigV := 0
  hCurv := by simpa using P.hq
  hSigV := by simp [plSigImg, plSig, plRho, plMu]
  hk := P.hk
  hv := P.hv
  hcn := P.hc

/-- The benchmark in the enriched subclass (sanction-section modulus `0`). -/
def toFcs : PlacableEconomyFcs where
  toPlacableEconomyF := P.toF
  Mcs := 0
  hMcs0 := le_rfl
  hFcs := semiconvexOnSet_sanction_of_eqOn_affineF (fun _ _ _ _ => rfl)

/-- The benchmark as an enriched chord economy. -/
abbrev E : ChordEconomyCs := P.toFcs.toChordCs

/-! ### Closed-form constants -/

/-- The Sender's value slope `g_S = w/(1 − β_S(1 − δ))`. -/
def gS : ℝ := P.w / (1 - P.βS * (1 - P.δ))

/-- **The appetite** `A = u₀ + β_S δ g_S`: the Sender's marginal return to the first unit of
sanction at full defiance, stage plus continuation. -/
def A : ℝ := P.u₀ + P.βS * P.δ * P.gS

/-- The Target's value slope `g_T = v/(1 − β_T(1 − δ))`. -/
def gT : ℝ := P.v / (1 - P.βT * (1 - P.δ))

/-- The net-of-compliance pain `D = c − ℓq/k`. -/
def D : ℝ := P.c - P.ℓ * P.q / P.k

/-- **The threshold** `β_T* = D/(δv + (1 − δ)D)`. -/
def βstar : ℝ := P.D / (P.δ * P.v + (1 - P.δ) * P.D)

/-- The relief Target value's intercept `−ℓ(A/k)/(1 − β_T)`. -/
def cR : ℝ := -(P.ℓ * (P.A / P.k) / (1 - P.βT))

/-- The vertex of the Sender's objective against a value of slope `g_S`, at compliance `a`:
`(A − k a)/q`. -/
def vtx (a : ℝ) : ℝ := (P.A - P.k * a) / P.q

/-- The Sender value's intercept at a constant compliance `a`: `(q/2)·vtx(a)²/(1 − β_S)`. -/
def CS (a : ℝ) : ℝ := P.q / 2 * P.vtx a ^ 2 / (1 - P.βS)

/-- The net weight of the sanction in the Target's objective against a value of slope `g_T`:
`c − β_T δ g_T`. -/
def pT : ℝ := P.c - P.βT * P.δ * P.gT

/-- The defiance-profile Target value's intercept `−(c − β_T δ g_T)(A/q)/(1 − β_T)`. -/
def cD : ℝ := -(P.pT * (P.A / P.q) / (1 - P.βT))

/-! ### Signs and defining identities -/

/-- `1 − β_S(1 − δ) > 0`.
Scope: linear–quadratic benchmark only. -/
theorem one_sub_βS_pos : 0 < 1 - P.βS * (1 - P.δ) := by
  have := P.hβS1; have := P.hδ0; have := P.hδ1; have := P.hβS0
  nlinarith

/-- `1 − β_T(1 − δ) > 0`.
Scope: linear–quadratic benchmark only. -/
theorem one_sub_βT_pos : 0 < 1 - P.βT * (1 - P.δ) := by
  have := P.hβT1; have := P.hδ0; have := P.hδ1; have := P.hβT0
  nlinarith

/-- `g_S > 0`.
Scope: linear–quadratic benchmark only. -/
theorem gS_pos : 0 < P.gS := div_pos P.hw P.one_sub_βS_pos

/-- The appetite is positive, `A > 0`.
Scope: linear–quadratic benchmark only. -/
theorem A_pos : 0 < P.A := by
  unfold A
  have := mul_pos (mul_pos P.hβS0 P.hδ0) P.gS_pos
  linarith [P.hu₀]

/-- `g_T > 0`.
Scope: linear–quadratic benchmark only. -/
theorem gT_pos : 0 < P.gT := div_pos P.hv P.one_sub_βT_pos

/-- The defining identity `g_S (1 − β_S(1 − δ)) = w`.
Scope: linear–quadratic benchmark only. -/
theorem gS_spec : P.gS * (1 - P.βS * (1 - P.δ)) = P.w :=
  div_mul_cancel₀ _ P.one_sub_βS_pos.ne'

/-- The defining identity `g_T (1 − β_T(1 − δ)) = v`.
Scope: linear–quadratic benchmark only. -/
theorem gT_spec : P.gT * (1 - P.βT * (1 - P.δ)) = P.v :=
  div_mul_cancel₀ _ P.one_sub_βT_pos.ne'

/-- The defining identity of the relief Target intercept, `c_R (1 − β_T) = −ℓ(A/k)`.
Scope: linear–quadratic benchmark only. -/
theorem cR_spec : P.cR * (1 - P.βT) = -(P.ℓ * (P.A / P.k)) := by
  unfold cR
  rw [neg_mul, div_mul_cancel₀ _ (by linarith [P.hβT1] : (1 : ℝ) - P.βT ≠ 0)]

/-- The defining identity of the defiance Target intercept,
`c_D (1 − β_T) = −(c − β_T δ g_T)(A/q)`.
Scope: linear–quadratic benchmark only. -/
theorem cD_spec : P.cD * (1 - P.βT) = -(P.pT * (P.A / P.q)) := by
  unfold cD
  rw [neg_mul, div_mul_cancel₀ _ (by linarith [P.hβT1] : (1 : ℝ) - P.βT ≠ 0)]

/-- The defining identity of the Sender intercept at constant compliance `a`,
`β_S·CS(a) + (q/2)·vtx(a)² = CS(a)`.
Scope: linear–quadratic benchmark only. -/
theorem CS_spec (a : ℝ) : P.βS * P.CS a + P.q / 2 * P.vtx a ^ 2 = P.CS a := by
  have h : (1 : ℝ) - P.βS ≠ 0 := by linarith [P.hβS1]
  unfold CS
  field_simp
  ring

/-- `q·vtx(a) = A − k a`.
Scope: linear–quadratic benchmark only. -/
theorem q_mul_vtx (a : ℝ) : P.q * P.vtx a = P.A - P.k * a := by
  unfold vtx
  field_simp [P.hq.ne']

/-- Under interiority `A < q` the vertex is below full sanction at every `a ≥ 0`.
Scope: linear–quadratic benchmark only. -/
theorem vtx_lt_one (hInt : P.A < P.q) {a : ℝ} (ha : 0 ≤ a) : P.vtx a < 1 := by
  unfold vtx
  rw [div_lt_one P.hq]
  nlinarith [mul_nonneg P.hk.le ha]

/-- The vertex is nonnegative exactly up to the relief price, `0 ≤ vtx(a) ↔ a ≤ A/k`.
Scope: linear–quadratic benchmark only. -/
theorem vtx_nonneg_iff (a : ℝ) : 0 ≤ P.vtx a ↔ a ≤ P.A / P.k := by
  rw [le_div_iff₀ P.hk]
  have h := P.q_mul_vtx a
  constructor
  · intro hv
    nlinarith [mul_nonneg P.hq.le hv]
  · intro ha
    by_contra hneg
    nlinarith [mul_neg_of_pos_of_neg P.hq (not_le.mp hneg)]

/-- At the relief price the vertex vanishes, `vtx(A/k) = 0`.
Scope: linear–quadratic benchmark only. -/
theorem vtx_Ak : P.vtx (P.A / P.k) = 0 := by
  unfold vtx
  rw [mul_div_cancel₀ _ P.hk.ne', sub_self, zero_div]

/-- At full defiance the vertex is `A/q`.
Scope: linear–quadratic benchmark only. -/
theorem vtx_zero : P.vtx 0 = P.A / P.q := by
  unfold vtx; rw [mul_zero, sub_zero]

/-- Under placability `A ≤ k` the relief price `A/k` is a feasible compliance level.
Scope: linear–quadratic benchmark only. -/
theorem Ak_mem (hP : P.A ≤ P.k) : P.A / P.k ∈ Sanctions.I :=
  ⟨div_nonneg P.A_pos.le P.hk.le, (div_le_one P.hk).2 hP⟩

/-- Under interiority `A < q` the defiance sanction `A/q` is a feasible sanction.
Scope: linear–quadratic benchmark only. -/
theorem Aq_mem (hInt : P.A < P.q) : P.A / P.q ∈ Sanctions.I :=
  ⟨div_nonneg P.A_pos.le P.hq.le, ((div_le_one P.hq).2 hInt.le)⟩

/-! ### The benchmark's chord data and hypotheses -/

/-- **The fourteen tightness equalities hold at every benchmark economy.**
Scope: linear–quadratic benchmark only. -/
theorem tight :
    P.E.SigV = 0 ∧ P.E.Ms = 0 ∧ P.E.τx = 0 ∧ P.E.Mcx = 0 ∧ P.E.Mcs = 0 ∧ P.E.Mmix = 0
      ∧ P.E.Qbar = P.E.q ∧ P.E.klo = P.E.khi ∧ P.E.ℓlo = P.E.ℓhi ∧ P.E.plo = P.E.c
      ∧ P.E.vlo = P.E.vhi ∧ P.E.nhi = 0 ∧ P.E.glo = P.E.ghi ∧ P.E.dlo = P.E.dhi := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  exact sub_zero P.c

/-- The benchmark's game: Sender payoff `symU_S q u₀ k 0 w`.
Scope: linear–quadratic benchmark only. -/
theorem U_S_eq : P.E.toParams.U_S = symU_S P.q P.u₀ P.k 0 P.w := rfl

/-- The benchmark's game: Target payoff `symU_T ℓ c 0 v`.
Scope: linear–quadratic benchmark only. -/
theorem U_T_eq : P.E.toParams.U_T = symU_T P.ℓ P.c 0 P.v := rfl

/-- The benchmark's game: transition `affineF δ`.
Scope: linear–quadratic benchmark only. -/
theorem F_eq : P.E.toParams.F = affineF P.δ := rfl

/-- The transition keeps the state feasible.
Scope: linear–quadratic benchmark only. -/
theorem F_mem {x s : ℝ} (hx : x ∈ Sanctions.I) (hs : s ∈ Sanctions.I) :
    P.E.toParams.F x s ∈ (Sanctions.S : Set ℝ) :=
  affineF_mem ⟨P.hδ0, P.hδ1⟩ x s hx hs

/-- **The chord economy's appetite is the benchmark's** `A = u₀ + β_S δ g_S`.
Scope: linear–quadratic benchmark only. -/
theorem E_A : P.E.A = P.A := by
  change P.u₀ + 0 + P.βS * chKS P.βS (1 - P.δ) (0 + P.w) * P.δ = P.A
  unfold chKS A gS
  ring

/-- **Interiority at the benchmark is `A < q`.**
Scope: linear–quadratic benchmark only. -/
theorem interior_iff : P.E.Interior ↔ P.A < P.q := by
  have e : P.u₀ + 0 + P.βS * chKS P.βS (1 - P.δ) (0 + P.w) * P.δ = P.A := by
    unfold chKS A gS; ring
  change P.u₀ + 0 + P.βS * chKS P.βS (1 - P.δ) (0 + P.w) * P.δ < P.q ↔ P.A < P.q
  rw [e]

/-- **Placability at the benchmark is `A ≤ k`.**
Scope: linear–quadratic benchmark only. -/
theorem placable_iff : P.E.Placable ↔ P.A ≤ P.k := by
  change P.E.A ≤ P.k ↔ P.A ≤ P.k
  rw [P.E_A]

/-- **The stage relief margin at the benchmark is `ℓq < kc`.**
Scope: linear–quadratic benchmark only. -/
theorem stageRelief_iff : P.E.StageRelief ↔ P.ℓ * P.q < P.k * P.c := by
  change P.ℓ * P.q < P.k * (P.c - 0) ↔ _
  rw [sub_zero]

/-- **The chord economy's `β_T*` is the benchmark's** `D/(δv + (1 − δ)D)`.
Scope: linear–quadratic benchmark only. -/
theorem betaStar_eq : P.E.betaStar = P.βstar := rfl

/-- **Zero-sanction neutrality holds at the benchmark.**
Scope: linear–quadratic benchmark only. -/
theorem neutral : P.E.ZeroSanctionNeutral :=
  P.toF.toChord_zeroSanctionNeutral

/-- **`D > 0` under the stage relief margin.**
Scope: linear–quadratic benchmark only. -/
theorem D_pos (hSR : P.E.StageRelief) : 0 < P.D := by
  have h := (P.stageRelief_iff).1 hSR
  unfold D
  rw [sub_pos, div_lt_iff₀ P.hk]
  linarith

/-- The threshold's denominator `δv + (1 − δ)D` is positive under the stage relief margin.
Scope: linear–quadratic benchmark only. -/
theorem den_pos (hSR : P.E.StageRelief) : 0 < P.δ * P.v + (1 - P.δ) * P.D := by
  have := P.D_pos hSR
  have := mul_pos P.hδ0 P.hv
  have := mul_nonneg (by linarith [P.hδ1] : (0 : ℝ) ≤ 1 - P.δ) (P.D_pos hSR).le
  linarith

/-- **The threshold algebra**: `β_T δ g_T ≤ D ↔ β_T ≤ β_T*`, under the stage relief margin.
Scope: linear–quadratic benchmark only. -/
theorem βT_δ_gT_le_iff (hSR : P.E.StageRelief) : P.βT * P.δ * P.gT ≤ P.D ↔ P.βT ≤ P.βstar := by
  have h1 := P.one_sub_βT_pos
  have hden := P.den_pos hSR
  have e : P.βT * P.δ * P.gT = P.βT * P.δ * P.v / (1 - P.βT * (1 - P.δ)) := by
    unfold gT; ring
  unfold βstar
  rw [e, div_le_iff₀ h1, le_div_iff₀ hden]
  constructor <;> intro h <;> linarith

/-- **The threshold algebra, strict form**: `β_T δ g_T < D ↔ β_T < β_T*`.
Scope: linear–quadratic benchmark only. -/
theorem βT_δ_gT_lt_iff (hSR : P.E.StageRelief) : P.βT * P.δ * P.gT < P.D ↔ P.βT < P.βstar := by
  have h1 := P.one_sub_βT_pos
  have hden := P.den_pos hSR
  have e : P.βT * P.δ * P.gT = P.βT * P.δ * P.v / (1 - P.βT * (1 - P.δ)) := by
    unfold gT; ring
  unfold βstar
  rw [e, div_lt_iff₀ h1, lt_div_iff₀ hden]
  constructor <;> intro h <;> linarith

/-! ## 2. The Sender's objective against an affine value of slope `g_S` -/

/-- **Against `g_S x + C` the Sender's objective is a concave parabola** with curvature `q`
and vertex `vtx a = (A − k a)/q`, whatever the intercept `C`.
Scope: linear–quadratic benchmark only. -/
theorem senderObj_aff (C : ℝ) {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ}
    (hs : s ∈ Sanctions.I) :
    P.E.toParams.U_S x a s
        + P.E.toParams.β_S * ChordEconomy.affBCF P.gS C (Sanctions.clipS' (P.E.toParams.F x s))
      = (P.gS * x + P.βS * C + P.q / 2 * P.vtx a ^ 2) - P.q / 2 * (s - P.vtx a) ^ 2 := by
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (P.F_mem hx hs)]
  change symU_S P.q P.u₀ P.k 0 P.w x a s + P.βS * (P.gS * affineF P.δ x s + C) = _
  unfold symU_S affineF
  have h1 := P.gS_spec
  have h2 := P.q_mul_vtx a
  unfold A at h2
  linear_combination (-x) * h1 + (-s) * h2

/-- **The Sender's top response against `g_S x + C` is the positive part of the vertex**,
under interiority `A < q`.
Scope: linear–quadratic benchmark only. -/
theorem σ_aff (C : ℝ) (hInt : P.A < P.q) {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I) :
    P.E.toParams.σ_dyn_top (ChordEconomy.affBCF P.gS C) x a = max 0 (P.vtx a) := by
  rw [σ_dyn_top_eq_clip P.E.toParams _ (by linarith [P.hq] : (0 : ℝ) < P.q / 2)
    (fun s hs => P.senderObj_aff C hx a hs)]
  rw [min_eq_right (P.vtx_lt_one hInt ha.1).le]

/-- The positive part of the vertex is a feasible sanction, under interiority.
Scope: linear–quadratic benchmark only. -/
theorem max_vtx_mem (hInt : P.A < P.q) {a : ℝ} (ha : a ∈ Sanctions.I) :
    max 0 (P.vtx a) ∈ Sanctions.I :=
  ⟨le_max_left _ _, max_le zero_le_one (P.vtx_lt_one hInt ha.1).le⟩

/-- **The Target's objective against `g_T x + C_T` and `g_S x + C`**: the state terms, minus the
compliance cost `ℓ a`, minus the net sanction weight `c − β_T δ g_T` times the response.
Scope: linear–quadratic benchmark only. -/
theorem joint_aff (C CT : ℝ) (hInt : P.A < P.q) {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I) :
    P.E.toParams.joint_T_top_integrand (ChordEconomy.affBCF P.gT CT)
        (ChordEconomy.affBCF P.gS C) x a
      = (P.v * x + P.βT * P.gT * (1 - P.δ) * x + P.βT * CT) - P.ℓ * a
        - P.pT * max 0 (P.vtx a) := by
  simp only [Params.joint_T_top_integrand]
  rw [P.σ_aff C hInt hx ha, ChordEconomy.affBCF_apply,
    Sanctions.clipS'_val_eq_of_mem (P.F_mem hx (P.max_vtx_mem hInt ha))]
  change symU_T P.ℓ P.c 0 P.v x a (max 0 (P.vtx a))
      + P.βT * (P.gT * affineF P.δ x (max 0 (P.vtx a)) + CT) = _
  unfold symU_T affineF pT
  ring

/-! ## 3. The constructed values in closed form -/

/-- **The zero-sanction Sender value is `g_S x`**: the unique fixed point of the zero-sanction
operator.
Scope: linear–quadratic benchmark only. -/
theorem VS01_eq : P.E.VS01 = ChordEconomy.affBCF P.gS 0 := by
  have hfix : P.E.relaxOp (ChordEconomy.affBCF P.gS 0) = ChordEconomy.affBCF P.gS 0 := by
    ext y
    rw [ChordEconomyCs.relaxOp_apply, ChordEconomy.affBCF_apply, ChordEconomy.affBCF_apply,
      Sanctions.clipS'_val_eq_of_mem (P.F_mem y.property ⟨le_rfl, zero_le_one⟩)]
    change symU_S P.q P.u₀ P.k 0 P.w y.val 0 0 + P.βS * (P.gS * affineF P.δ y.val 0 + 0)
      = P.gS * y.val + 0
    unfold symU_S affineF
    linear_combination (-y.val) * P.gS_spec
  exact P.E.relaxOp_contracting.fixedPoint_unique' P.E.VS01_fix hfix

/-- **The zero level is the constant `A/k`**, under interiority and placability.
Scope: linear–quadratic benchmark only. -/
theorem zeroLevel_eq (hInt : P.E.Interior) (hP : P.E.Placable) {x : ℝ}
    (hx : x ∈ Sanctions.I) : P.E.zeroLevel x = P.A / P.k := by
  have hInt' := (P.interior_iff).1 hInt
  have hP' := (P.placable_iff).1 hP
  have key : ∀ a ∈ Sanctions.I, P.E.response P.E.VS01 x a = max 0 (P.vtx a) := by
    intro a ha
    rw [P.E.response_eq_top P.E.VS01_mem hx, P.VS01_eq]
    exact P.σ_aff 0 hInt' hx ha
  have hset : P.E.zeroSet x = Icc (P.A / P.k) 1 := by
    ext a
    constructor
    · rintro ⟨ha, hz⟩
      have hz0 : P.E.response P.E.VS01 x a = 0 := hz
      rw [key a ha] at hz0
      have hv : P.vtx a ≤ 0 := max_eq_left_iff.mp hz0
      refine ⟨?_, ha.2⟩
      have h := P.q_mul_vtx a
      have hka : P.A ≤ P.k * a := by nlinarith [mul_nonpos_iff.2 (Or.inl ⟨P.hq.le, hv⟩)]
      rw [div_le_iff₀ P.hk]
      linarith
    · rintro ⟨h1, h2⟩
      have ha : a ∈ Sanctions.I := ⟨le_trans (P.Ak_mem hP').1 h1, h2⟩
      refine ⟨ha, ?_⟩
      change P.E.response P.E.VS01 x a = 0
      rw [key a ha]
      apply max_eq_left
      have h := P.q_mul_vtx a
      have hka : P.A ≤ P.k * a := by
        have := (div_le_iff₀ P.hk).1 h1
        linarith
      by_contra hpos
      nlinarith [mul_pos P.hq (not_le.mp hpos)]
  rw [ChordEconomyCs.zeroLevel_eq_sInf, hset, csInf_Icc (P.Ak_mem hP').2]

/-- **The relief Target value is `g_T x − ℓ(A/k)/(1 − β_T)`**: the unique fixed point of the
relief operator.
Scope: linear–quadratic benchmark only. -/
theorem VTrel_eq (hInt : P.E.Interior) (hP : P.E.Placable) :
    P.E.VTrel hInt hP = ChordEconomy.affBCF P.gT P.cR := by
  have hfix : P.E.reliefOp hInt hP (ChordEconomy.affBCF P.gT P.cR)
      = ChordEconomy.affBCF P.gT P.cR := by
    ext y
    rw [ChordEconomyCs.reliefOp_apply, P.zeroLevel_eq hInt hP y.property,
      ChordEconomy.affBCF_apply, ChordEconomy.affBCF_apply,
      Sanctions.clipS'_val_eq_of_mem (P.F_mem y.property ⟨le_rfl, zero_le_one⟩)]
    change symU_T P.ℓ P.c 0 P.v y.val (P.A / P.k) 0
        + P.βT * (P.gT * affineF P.δ y.val 0 + P.cR) = P.gT * y.val + P.cR
    unfold symU_T affineF
    linear_combination (-y.val) * P.gT_spec - P.cR_spec
  exact (P.E.reliefOp_contracting hInt hP).fixedPoint_unique' (P.E.VTrel_fix hInt hP) hfix

/-- The Sender's Bellman operator against a constant compliance `a₀` (with the vertex feasible)
has the fixed point `g_S x + CS a₀`.
Scope: linear–quadratic benchmark only. -/
theorem bellmanS_const_fix (hInt : P.A < P.q) {a₀ : ℝ} (ha₀ : a₀ ∈ Sanctions.I)
    (hv : 0 ≤ P.vtx a₀) :
    P.E.toParams.bellmanS_BCF (fun _ => a₀) continuous_const
        (ChordEconomy.affBCF P.gS (P.CS a₀))
      = ChordEconomy.affBCF P.gS (P.CS a₀) := by
  ext y
  change sSup ((fun s => P.E.toParams.integrandS (fun _ => a₀)
    (fun z => ChordEconomy.affBCF P.gS (P.CS a₀) z) (y.val, s)) '' Sanctions.I)
      = ChordEconomy.affBCF P.gS (P.CS a₀) y
  have hval : ∀ s ∈ Sanctions.I,
      P.E.toParams.integrandS (fun _ => a₀) (fun z => ChordEconomy.affBCF P.gS (P.CS a₀) z)
          (y.val, s)
        = (P.gS * y.val + P.βS * P.CS a₀ + P.q / 2 * P.vtx a₀ ^ 2)
          - P.q / 2 * (s - P.vtx a₀) ^ 2 := by
    intro s hs
    have := P.senderObj_aff (P.CS a₀) y.property a₀ hs
    simp only [Params.integrandS]
    rw [this]
  have hvI : P.vtx a₀ ∈ Sanctions.I := ⟨hv, (P.vtx_lt_one hInt ha₀.1).le⟩
  have hspec := P.CS_spec a₀
  have hgt : IsGreatest ((fun s => P.E.toParams.integrandS (fun _ => a₀)
      (fun z => ChordEconomy.affBCF P.gS (P.CS a₀) z) (y.val, s)) '' Sanctions.I)
      (ChordEconomy.affBCF P.gS (P.CS a₀) y) := by
    refine ⟨⟨P.vtx a₀, hvI, ?_⟩, ?_⟩
    · dsimp only
      rw [hval _ hvI, sub_self, ChordEconomy.affBCF_apply]
      linear_combination hspec
    · rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [hval s hs, ChordEconomy.affBCF_apply]
      nlinarith [mul_nonneg P.hq.le (sq_nonneg (s - P.vtx a₀))]
  exact hgt.csSup_eq

/-- **The Sender value at full defiance is `g_S x + A²/(2q(1 − β_S))`**: the unique fixed point
of the Sender's Bellman operator against full defiance.
Scope: linear–quadratic benchmark only. -/
theorem VSstar_eq (hInt : P.E.Interior) : P.E.VSstar = ChordEconomy.affBCF P.gS (P.CS 0) := by
  have hInt' := (P.interior_iff).1 hInt
  have hv : 0 ≤ P.vtx 0 := by rw [P.vtx_zero]; exact div_nonneg P.A_pos.le P.hq.le
  exact (P.E.toParams.bellmanS_BCF_contracting (α := fun _ => 0)
    continuous_const).fixedPoint_unique' P.E.VSstar_fix
    (P.bellmanS_const_fix hInt' ⟨le_rfl, zero_le_one⟩ hv)

/-- **The defiance-profile Target value is `g_T x − (c − β_T δ g_T)(A/q)/(1 − β_T)`**: the
unique fixed point of the Target operator at the Sender value of full defiance.
Scope: linear–quadratic benchmark only. -/
theorem VTdef_eq (hInt : P.E.Interior) : P.E.VTdef = ChordEconomy.affBCF P.gT P.cD := by
  have hInt' := (P.interior_iff).1 hInt
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have hfix : P.E.targetOp P.E.VSstar_mem (ChordEconomy.affBCF P.gT P.cD)
      = ChordEconomy.affBCF P.gT P.cD := by
    ext y
    have e : P.E.targetOp P.E.VSstar_mem (ChordEconomy.affBCF P.gT P.cD) y
        = P.E.toParams.joint_T_top_integrand (ChordEconomy.affBCF P.gT P.cD) P.E.VSstar
            y.val 0 := by
      rw [P.E.joint_T_top_integrand_eq P.E.VSstar_mem _ y.property]
      rfl
    rw [e, P.VSstar_eq hInt, P.joint_aff (P.CS 0) P.cD hInt' y.property h0I, P.vtx_zero,
      max_eq_right (div_nonneg P.A_pos.le P.hq.le), ChordEconomy.affBCF_apply]
    linear_combination (-y.val) * P.gT_spec - P.cD_spec
  exact (((P.E.targetOp_contracting P.E.VSstar_mem).fixedPoint_unique hfix)).symm

/-! ## 4. The relief side: existence exactly up to `β_T*` -/

/-- **The Target's objective at the relief values.**
Scope: linear–quadratic benchmark only. -/
theorem joint_rel (hInt : P.E.Interior) (hP : P.E.Placable) {x : ℝ} (hx : x ∈ Sanctions.I)
    {a : ℝ} (ha : a ∈ Sanctions.I) :
    P.E.toParams.joint_T_top_integrand (P.E.VTrel hInt hP) P.E.VS01 x a
      = (P.v * x + P.βT * P.gT * (1 - P.δ) * x + P.βT * P.cR) - P.ℓ * a
        - P.pT * max 0 (P.vtx a) := by
  rw [P.VTrel_eq hInt hP, P.VS01_eq]
  exact P.joint_aff 0 P.cR ((P.interior_iff).1 hInt) hx ha

/-- **The relief best reply at the benchmark is `ℓq ≤ k(c − β_T δ g_T)`**: at every state
complying at `A/k` instead of `a < A/k` costs `ℓ(A/k − a)` and saves `(c − β_T δ g_T)(A − ka)/q`
in sanction and continuation.
Scope: linear–quadratic benchmark only. -/
theorem reliefBestReply_iff_pT (hInt : P.E.Interior) (hP : P.E.Placable) :
    P.E.ReliefBestReply hInt hP ↔ P.ℓ * P.q ≤ P.k * P.pT := by
  have hP' := (P.placable_iff).1 hP
  have h0I : (0 : ℝ) ∈ Sanctions.I := ⟨le_rfl, zero_le_one⟩
  have hAk := P.Ak_mem hP'
  unfold ChordEconomyCs.ReliefBestReply
  constructor
  · intro h
    have hopt := isMaxOn_iff.mp (h 0 h0I) 0 h0I
    simp only at hopt
    rw [P.zeroLevel_eq hInt hP h0I, P.joint_rel hInt hP h0I h0I,
      P.joint_rel hInt hP h0I hAk, P.vtx_zero, P.vtx_Ak, max_self,
      max_eq_right (div_nonneg P.A_pos.le P.hq.le)] at hopt
    have h1 : P.ℓ * (P.A / P.k) ≤ P.pT * (P.A / P.q) := by linarith
    have e1 : P.ℓ * (P.A / P.k) * (P.k * P.q) = P.ℓ * P.A * P.q := by
      rw [show P.ℓ * (P.A / P.k) * (P.k * P.q) = P.ℓ * P.q * (P.A / P.k * P.k) by ring,
        div_mul_cancel₀ _ P.hk.ne']
      ring
    have e2 : P.pT * (P.A / P.q) * (P.k * P.q) = P.pT * P.A * P.k := by
      rw [show P.pT * (P.A / P.q) * (P.k * P.q) = P.pT * P.k * (P.A / P.q * P.q) by ring,
        div_mul_cancel₀ _ P.hq.ne']
      ring
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_pos P.hk P.hq).le
    rw [e1, e2] at h2
    by_contra hcon
    have := mul_pos P.A_pos (sub_pos.2 (not_le.mp hcon))
    linarith
  · intro hb x hx
    rw [P.zeroLevel_eq hInt hP hx, isMaxOn_iff]
    intro a ha
    rw [P.joint_rel hInt hP hx ha, P.joint_rel hInt hP hx hAk, P.vtx_Ak, max_self]
    have hkv := P.q_mul_vtx a
    have hkA : P.k * (P.A / P.k) = P.A := mul_div_cancel₀ _ P.hk.ne'
    rcases le_total (P.vtx a) 0 with h | h
    · rw [max_eq_left h]
      have : P.A ≤ P.k * a := by nlinarith [mul_nonpos_iff.2 (Or.inl ⟨P.hq.le, h⟩)]
      have hle : P.A / P.k ≤ a := by rw [div_le_iff₀ P.hk]; linarith
      nlinarith [P.hℓ]
    · rw [max_eq_right h]
      have hk := P.hk
      have key : P.k * (P.ℓ * (P.A / P.k) - P.ℓ * a - P.pT * P.vtx a)
          = P.vtx a * (P.ℓ * P.q - P.k * P.pT) := by
        linear_combination P.ℓ * hkA - P.ℓ * hkv
      have hneg : P.vtx a * (P.ℓ * P.q - P.k * P.pT) ≤ 0 :=
        mul_nonpos_iff.2 (Or.inl ⟨h, by linarith⟩)
      have : P.ℓ * (P.A / P.k) - P.ℓ * a - P.pT * P.vtx a ≤ 0 := by
        by_contra hc
        have := mul_pos hk (not_le.mp hc)
        linarith
      linarith

/-- **The relief best reply at the benchmark holds exactly up to `β_T*`.**
Scope: linear–quadratic benchmark only. -/
theorem reliefBestReply_iff (hInt : P.E.Interior) (hSR : P.E.StageRelief)
    (hP : P.E.Placable) : P.E.ReliefBestReply hInt hP ↔ P.βT ≤ P.E.betaStar := by
  rw [P.reliefBestReply_iff_pT hInt hP, P.betaStar_eq, ← P.βT_δ_gT_le_iff hSR]
  unfold pT D
  have hk := P.hk
  constructor
  · intro h
    have : P.ℓ * P.q / P.k ≤ P.c - P.βT * P.δ * P.gT := by
      rw [div_le_iff₀ hk]; linarith
    linarith
  · intro h
    have : P.ℓ * P.q / P.k ≤ P.c - P.βT * P.δ * P.gT := by linarith
    rw [div_le_iff₀ hk] at this
    linarith

/-- **Relief exists exactly up to `β_T*`** (plan LQ-1(a), the existence half). In the
linear–quadratic benchmark, under interiority `A < q`, the stage relief margin `ℓq < kc` and
placability `A ≤ k`, a top-selector equilibrium whose realised sanction is zero at every state
exists if and only if `β_T ≤ β_T* = D/(δv + (1 − δ)D)`. It is the exact relief test
`exists_relief_equilibrium_iff` read at the closed-form values.
Scope: linear–quadratic benchmark only. -/
theorem relief_iff (hInt : P.E.Interior) (hSR : P.E.StageRelief) (hP : P.E.Placable) :
    (∃ Eq : P.E.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, P.E.toParams.dynamicEquilibriumRule Eq x = 0)
      ↔ P.βT ≤ P.E.betaStar :=
  (P.E.exists_relief_equilibrium_iff hInt hP P.neutral).trans
    (P.reliefBestReply_iff hInt hSR hP)

/-- **No relief above `β_T*`**: every equilibrium with zero sanctions at every state has
`β_T ≤ β_T*`. The class theorem `reliefExistence_lt_margin` excludes relief only from the
strictly larger bound `c/(δv + c(1 − δ))` up (`βstar_lt_margin`).
Scope: linear–quadratic benchmark only. -/
theorem no_relief_above (hInt : P.E.Interior) (hSR : P.E.StageRelief) (hP : P.E.Placable)
    (hβ : P.E.betaStar < P.βT) (Eq : P.E.toParams.FeedbackStackelbergEquilibriumTop) :
    ¬ ∀ x ∈ Sanctions.I, P.E.toParams.dynamicEquilibriumRule Eq x = 0 := fun h =>
  absurd ((P.relief_iff hInt hSR hP).1 ⟨Eq, h⟩) (not_le.2 hβ)

/-- **`β_T*` lies strictly below the loss-offset patience bound** `c/(δv + c(1 − δ))` of
`reliefExistence_lt_margin`, under the stage relief margin.
Scope: linear–quadratic benchmark only. -/
theorem βstar_lt_margin (hSR : P.E.StageRelief) :
    P.βstar < P.c / (P.δ * P.v + P.c * (1 - P.δ)) := by
  have hD := P.D_pos hSR
  have hden := P.den_pos hSR
  have hDc : P.D < P.c := by
    unfold D
    have := div_pos (mul_pos P.hℓ P.hq) P.hk
    linarith
  have hden2 : 0 < P.δ * P.v + P.c * (1 - P.δ) := by
    have := mul_pos P.hδ0 P.hv
    have := mul_pos P.hc (by linarith [P.hδ1] : (0 : ℝ) < 1 - P.δ)
    linarith
  unfold βstar
  rw [div_lt_div_iff₀ hden hden2]
  nlinarith [mul_pos (mul_pos P.hδ0 P.hv) (sub_pos.2 hDc)]

/-! ## 5. The defiance side: existence exactly from `β_T*` -/

/-- **Full defiance exists exactly from `β_T*`** (plan LQ-1(b), the existence half). In the
benchmark, under interiority, the stage relief margin and placability, a top-selector
equilibrium with full defiance at every state exists if and only if `β_T* ≤ β_T`:
`collapse_equilibrium_threshold_le_tight` with the benchmark's tightness equalities.
Scope: linear–quadratic benchmark only. -/
theorem defiance_iff (hInt : P.E.Interior) (hSR : P.E.StageRelief) (hP : P.E.Placable) :
    (∃ Eq : P.E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0)
      ↔ P.E.betaStar ≤ P.βT := by
  obtain ⟨h1, -, h3, -, -, -, h7, h8, h9, h10, h11, h12, -, h14⟩ := P.tight
  exact ChordEconomyRelief.collapse_equilibrium_threshold_le_tight (E := P.E.toChordEconomyRelief)
    hInt hSR hP h1 h3 h7 h8 h9 h10 h11 h12 h14

/-- **The two regimes meet at `β_T*`** (plan LQ-1(a)–(b)): relief exists iff `β_T ≤ β_T*`, full
defiance exists iff `β_T* ≤ β_T`, so at `β_T = β_T*` both exist, below only relief and above only
full defiance.
Scope: linear–quadratic benchmark only. -/
theorem characterisation (hInt : P.E.Interior) (hSR : P.E.StageRelief) (hP : P.E.Placable) :
    ((∃ Eq : P.E.toParams.FeedbackStackelbergEquilibriumTop,
        ∀ x ∈ Sanctions.I, P.E.toParams.dynamicEquilibriumRule Eq x = 0) ↔ P.βT ≤ P.βstar)
    ∧ ((∃ Eq : P.E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0)
        ↔ P.βstar ≤ P.βT)
    ∧ P.βstar = P.D / (P.δ * P.v + (1 - P.δ) * P.D) :=
  ⟨P.relief_iff hInt hSR hP, P.defiance_iff hInt hSR hP, rfl⟩

/-! ## 6. Uniqueness of relief among equilibria with an affine Sender value -/

/-- **At the benchmark the two-sided carrier consists of affine values of slope `g_S`**: a value
in `carrierS2` has lower slope `g_S` and Lipschitz constant `K_S = g_S`, so it rises by exactly
`g_S` per unit of state.
Scope: linear–quadratic benchmark only. -/
theorem carrierS2_affine {V : ChordEconomy.Val} (hV : V ∈ P.E.carrierS2)
    (y : ↥(Sanctions.S : Set ℝ)) :
    V y = P.gS * y.val + V ⟨0, ⟨le_rfl, zero_le_one⟩⟩ := by
  obtain ⟨⟨⟨-, hLip, hlow⟩, -⟩, -⟩ := hV
  set y0 : ↥(Sanctions.S : Set ℝ) := ⟨0, ⟨le_rfl, zero_le_one⟩⟩ with hy0
  have hle : y0 ≤ y := y.property.1
  have hdist : dist y0 y = y.val := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    change |y.val - 0| = y.val
    rw [sub_zero, abs_of_nonneg y.property.1]
  have hKS : P.E.KS = P.gS := by
    change chKS P.βS (1 - P.δ) (0 + P.w) = P.gS
    unfold chKS gS; ring
  have hgS : P.E.gS = P.gS := by
    change chGS P.βS (1 - P.δ) P.w = P.gS
    unfold chGS gS; ring
  have h1 := hlow y0 y ⟨le_rfl, zero_le_one⟩ y.property hle
  have h2 := hLip y0 y
  rw [hdist, hgS] at h1
  rw [hdist, hKS] at h2
  have h3 := (abs_le.1 h2).2
  linarith

/-- **Conversely, every affine value of slope `g_S` within the norm bound `M_S` is in the
two-sided carrier**: it is `g_S`-Lipschitz with lower slope `g_S`, and both chord defects vanish.
Scope: linear–quadratic benchmark only. -/
theorem mem_carrierS2_of_affine {V : ChordEconomy.Val} {C : ℝ}
    (hV : ∀ y : ↥(Sanctions.S : Set ℝ), V y = P.gS * y.val + C) (hM : ‖V‖ ≤ P.E.MS) :
    V ∈ P.E.carrierS2 := by
  have hKS : P.E.KS = P.gS := by
    change chKS P.βS (1 - P.δ) (0 + P.w) = P.gS
    unfold chKS gS; ring
  have hgS : P.E.gS = P.gS := by
    change chGS P.βS (1 - P.δ) P.w = P.gS
    unfold chGS gS; ring
  have hSigC : P.E.SigC = 0 := by
    change chSigC P.βS 0 P.E.KS 0 (1 - P.δ) = 0
    unfold chSigC; simp
  have hSigV : P.E.SigV = 0 := rfl
  refine ⟨⟨⟨hM, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro y₁ y₂
    rw [hV, hV, hKS, Subtype.dist_eq, Real.dist_eq,
      show P.gS * y₂.val + C - (P.gS * y₁.val + C) = P.gS * (y₂.val - y₁.val) by ring,
      abs_mul, abs_of_pos P.gS_pos, abs_sub_comm]
  · intro y₁ y₂ _ _ hle
    have hle' : y₁.val ≤ y₂.val := hle
    rw [hV, hV, hgS, Subtype.dist_eq, Real.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 hle')]
    exact le_of_eq (by ring)
  · intro z₁ hz₁ z₂ hz₂ t ht0 ht1
    have hm := mem_Icc_convexComb hz₁ hz₂ ht0 ht1
    simp only
    rw [hV, hV, hV, Sanctions.clipS'_val_eq_of_mem hz₁, Sanctions.clipS'_val_eq_of_mem hz₂,
      Sanctions.clipS'_val_eq_of_mem hm, hSigV]
    exact le_of_eq (by ring)
  · intro z₁ hz₁ z₂ hz₂ t ht0 ht1
    have hm := mem_Icc_convexComb hz₁ hz₂ ht0 ht1
    simp only
    rw [hV, hV, hV, Sanctions.clipS'_val_eq_of_mem hz₁, Sanctions.clipS'_val_eq_of_mem hz₂,
      Sanctions.clipS'_val_eq_of_mem hm, hSigC]
    exact le_of_eq (by ring)

/-- **At the benchmark the two-sided carrier is exactly the affine values of slope `g_S` within
the norm bound `M_S`.**
Scope: linear–quadratic benchmark only. -/
theorem mem_carrierS2_iff {V : ChordEconomy.Val} :
    V ∈ P.E.carrierS2 ↔ (∀ y : ↥(Sanctions.S : Set ℝ),
      V y = P.gS * y.val + V ⟨0, ⟨le_rfl, zero_le_one⟩⟩) ∧ ‖V‖ ≤ P.E.MS :=
  ⟨fun hV => ⟨P.carrierS2_affine hV, hV.1.1.1⟩, fun h => P.mem_carrierS2_of_affine h.1 h.2⟩

/-- **Relief is the unique equilibrium with an affine Sender value below `β_T*`** (plan
LQ-1(f), the carrier half). In the benchmark, under interiority, the stage relief margin and
placability, if `β_T < β_T*`, every top-selector equilibrium whose Sender value lies in the
two-sided carrier (at the benchmark: affine values of slope `g_S`, `carrierS2_affine`) complies
at `A/k` at every state, has the Sender value `g_S x` and the Target value
`g_T x − ℓ(A/k)/(1 − β_T)`, and realises a zero sanction at every state. It is
`unique_equilibrium_of_relief_side` with the strict relief side read off
`collapse_threshold'` and the loop condition from `L_resp = 0`.
Scope: linear–quadratic benchmark only; equilibria with Sender value in the carrier (affine
Sender values) only (not general). -/
theorem relief_unique_carrier (hInt : P.E.Interior) (hSR : P.E.StageRelief)
    (hP : P.E.Placable) (hβ : P.βT < P.E.betaStar)
    (Eq : P.E.toParams.FeedbackStackelbergEquilibriumTop) (hVS : Eq.V_S ∈ P.E.carrierS2) :
    (∀ x ∈ Sanctions.I, Eq.α x = P.A / P.k) ∧ Eq.V_S = ChordEconomy.affBCF P.gS 0
      ∧ Eq.V_T = ChordEconomy.affBCF P.gT P.cR
      ∧ ∀ x ∈ Sanctions.I, P.E.toParams.dynamicEquilibriumRule Eq x = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := P.tight
  have hrel := ((P.E.collapse_threshold' hSR h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    h14).2.2).2 hβ
  have hL : P.E.Lresp = 0 := P.E.collapse_Lresp' h1 h3 h4 h6
  have hγ : P.E.β_T * P.E.LloopSharp < 1 := by
    unfold ChordEconomyTwoSided.LloopSharp
    rw [hL, zero_div, mul_zero, add_zero]
    exact P.E.βT_ghi_lt_one
  obtain ⟨hα, hV, hT, hr⟩ := P.E.unique_equilibrium_of_relief_side hInt hP hγ hrel P.neutral Eq hVS
  refine ⟨fun x hx => ?_, hV.trans P.VS01_eq, hT.trans (P.VTrel_eq hInt hP), hr⟩
  rw [hα x hx, P.zeroLevel_eq hInt hP hx]

/-! ## 6b. Mutual entrenchment: the value gaps between the two profiles -/

/-- **The value gaps between the defiance and relief profiles** (plan LQ-1(e)). In the
benchmark, under interiority and placability, at every state the defiance-profile Target value
exceeds the relief value by `A(β_T δ g_T − D)/(q(1 − β_T))`, and the Sender's value at full
defiance exceeds its zero-sanction value by `A²/(2q(1 − β_S)) > 0`.
Scope: linear–quadratic benchmark only. -/
theorem value_gaps (hInt : P.E.Interior) (hP : P.E.Placable) (y : ↥(Sanctions.S : Set ℝ)) :
    P.E.VTdef y - P.E.VTrel hInt hP y
        = P.A * (P.βT * P.δ * P.gT - P.D) / (P.q * (1 - P.βT))
      ∧ P.E.VSstar y - P.E.VS01 y = P.A ^ 2 / (2 * P.q * (1 - P.βS)) := by
  have hq := P.hq.ne'
  have hk := P.hk.ne'
  have hT : (1 : ℝ) - P.βT ≠ 0 := by linarith [P.hβT1]
  have hS : (1 : ℝ) - P.βS ≠ 0 := by linarith [P.hβS1]
  rw [P.VTdef_eq hInt, P.VTrel_eq hInt hP, P.VSstar_eq hInt, P.VS01_eq]
  simp only [ChordEconomy.affBCF_apply]
  constructor
  · unfold cD cR pT D
    field_simp
    ring
  · unfold CS vtx
    field_simp
    ring

/-- **Mutual entrenchment** (plan LQ-1(e)). In the benchmark, under interiority, the stage relief
margin and placability, the Target weakly prefers the defiance profile's value to the relief
value at every state exactly when `β_T* ≤ β_T`, while the Sender strictly prefers full defiance
at every state for every `β_T`.
Scope: linear–quadratic benchmark only. -/
theorem entrenchment (hInt : P.E.Interior) (hSR : P.E.StageRelief) (hP : P.E.Placable) :
    ((∀ y : ↥(Sanctions.S : Set ℝ), P.E.VTrel hInt hP y ≤ P.E.VTdef y) ↔ P.E.betaStar ≤ P.βT)
      ∧ ∀ y : ↥(Sanctions.S : Set ℝ), P.E.VS01 y < P.E.VSstar y := by
  have hden : 0 < P.q * (1 - P.βT) := mul_pos P.hq (by linarith [P.hβT1])
  have hA := P.A_pos
  have y0 : ↥(Sanctions.S : Set ℝ) := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
  refine ⟨⟨fun h => ?_, fun hβ y => ?_⟩, fun y => ?_⟩
  · have hgap := (P.value_gaps hInt hP y0).1
    have h0 := h y0
    have hnn : 0 ≤ P.A * (P.βT * P.δ * P.gT - P.D) / (P.q * (1 - P.βT)) := by linarith
    have hnn' : 0 ≤ P.A * (P.βT * P.δ * P.gT - P.D) :=
      (div_nonneg_iff.1 hnn).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hden))
    have hD : P.D ≤ P.βT * P.δ * P.gT := by
      by_contra hc
      have := mul_neg_of_pos_of_neg hA (sub_neg.2 (not_le.mp hc))
      linarith
    rw [P.betaStar_eq]
    by_contra hc
    exact absurd ((P.βT_δ_gT_lt_iff hSR).2 (not_le.mp hc)) (not_lt.2 hD)
  · have hgap := (P.value_gaps hInt hP y).1
    rw [P.betaStar_eq] at hβ
    have hD : P.D ≤ P.βT * P.δ * P.gT := by
      by_contra hc
      exact absurd ((P.βT_δ_gT_lt_iff hSR).1 (not_le.mp hc)) (not_lt.2 hβ)
    have : 0 ≤ P.A * (P.βT * P.δ * P.gT - P.D) / (P.q * (1 - P.βT)) :=
      div_nonneg (mul_nonneg hA.le (sub_nonneg.2 hD)) hden.le
    linarith
  · have hgap := (P.value_gaps hInt hP y).2
    have : 0 < P.A ^ 2 / (2 * P.q * (1 - P.βS)) :=
      div_pos (pow_pos hA 2) (mul_pos (mul_pos two_pos P.hq) (by linarith [P.hβS1]))
    linarith

/-! ## 7. Equilibrium levels and the state path -/

/-- **Every zero-sanction equilibrium complies at `A/k`** at every state (the relief price).
Scope: linear–quadratic benchmark only. -/
theorem relief_policy_eq (hInt : P.E.Interior) (hP : P.E.Placable)
    (Eq : P.E.toParams.FeedbackStackelbergEquilibriumTop)
    (hzero : ∀ x ∈ Sanctions.I, P.E.toParams.dynamicEquilibriumRule Eq x = 0)
    {x : ℝ} (hx : x ∈ Sanctions.I) : Eq.α x = P.A / P.k := by
  obtain ⟨hα, -, -⟩ := P.E.relief_equilibrium_of_zero_rule hInt hP P.neutral Eq hzero
  rw [hα x hx, P.zeroLevel_eq hInt hP hx]

/-- **Every full-defiance equilibrium sanctions at `A/q`** at every state (the defiance
sanction).
Scope: linear–quadratic benchmark only. -/
theorem defiance_rule_eq (hInt : P.E.Interior)
    (Eq : P.E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {x : ℝ} (hx : x ∈ Sanctions.I) : P.E.toParams.dynamicEquilibriumRule Eq x = P.A / P.q := by
  have hInt' := (P.interior_iff).1 hInt
  obtain ⟨hVS, -, -⟩ := P.E.values_eq_of_policy_zero Eq hα
  change P.E.toParams.σ_dyn_top Eq.V_S x (Eq.α x) = _
  rw [hVS, P.VSstar_eq hInt, hα x hx, P.σ_aff (P.CS 0) hInt' hx ⟨le_rfl, zero_le_one⟩, P.vtx_zero,
    max_eq_right (div_nonneg P.A_pos.le P.hq.le)]

/-- **The state path under a constant realised sanction `s̄`**: along any equilibrium whose rule
is `s̄` at every feasible state, the state from `x₀ ∈ [0,1]` is `s̄ + (1 − δ)ᵗ(x₀ − s̄)`.
Scope: linear–quadratic benchmark only. -/
theorem rulePathF_eq_of_const_rule (Eq : P.E.toParams.FeedbackStackelbergEquilibriumTop)
    {sbar : ℝ} (hrule : ∀ x ∈ Sanctions.I, P.E.toParams.dynamicEquilibriumRule Eq x = sbar)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) (t : ℕ) :
    P.E.toParams.rulePathF (P.E.toParams.dynamicEquilibriumRule Eq) x₀ t
      = sbar + (1 - P.δ) ^ t * (x₀ - sbar) := by
  have hmem : ∀ n, P.E.toParams.rulePathF (P.E.toParams.dynamicEquilibriumRule Eq) x₀ n
      ∈ Sanctions.I :=
    fun n => P.E.toParams.rulePathF_mem_I
      (fun x _ => P.E.toParams.σ_dyn_top_mem_I Eq.V_S x (Eq.α x)) hx₀ n
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Params.rulePathF_succ]
    unfold Params.ruleStepF
    rw [hrule _ (hmem n), ih, P.F_eq]
    unfold affineF
    ring

/-- **The defiance path converges to the steady state `A/q`**: along any full-defiance
equilibrium the state from `x₀ ∈ [0,1]` is `A/q + (1 − δ)ᵗ(x₀ − A/q)`, which tends to `A/q`.
Scope: linear–quadratic benchmark only. -/
theorem defiance_path_tendsto (hInt : P.E.Interior)
    (Eq : P.E.toParams.FeedbackStackelbergEquilibriumTop) (hα : ∀ x ∈ Sanctions.I, Eq.α x = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Sanctions.I) :
    (∀ t, P.E.toParams.rulePathF (P.E.toParams.dynamicEquilibriumRule Eq) x₀ t
        = P.A / P.q + (1 - P.δ) ^ t * (x₀ - P.A / P.q))
      ∧ Tendsto (fun t => P.E.toParams.rulePathF (P.E.toParams.dynamicEquilibriumRule Eq) x₀ t)
          atTop (𝓝 (P.A / P.q)) := by
  have hpath := P.rulePathF_eq_of_const_rule Eq (fun x hx => P.defiance_rule_eq hInt Eq hα hx) hx₀
  refine ⟨hpath, ?_⟩
  have hpow : Tendsto (fun t : ℕ => (1 - P.δ) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [P.hδ1]) (by linarith [P.hδ0])
  have h := (hpow.mul_const (x₀ - P.A / P.q)).const_add (P.A / P.q)
  rw [zero_mul, add_zero] at h
  exact h.congr (fun t => (hpath t).symm)

/-! ## 8. Comparative statics -/

/-- **The appetite as a function of the Sender's data**: `u₀ + β_S δ w/(1 − β_S(1 − δ))`. -/
def lqAppetite (δ βS u₀ w : ℝ) : ℝ := u₀ + βS * δ * (w / (1 - βS * (1 - δ)))

/-- The benchmark's appetite is `lqAppetite δ β_S u₀ w`.
Scope: linear–quadratic benchmark only. -/
theorem A_eq_lqAppetite : P.A = lqAppetite P.δ P.βS P.u₀ P.w := rfl

/-- **The appetite strictly increases in the Sender's patience `β_S`.**
Scope: linear–quadratic benchmark only. -/
theorem lqAppetite_lt_of_βS_lt {δ β₁ β₂ u₀ w : ℝ} (hδ0 : 0 < δ) (hw : 0 < w)
    (hβ₁ : 0 < β₁) (hβ : β₁ < β₂) (hβ₂ : β₂ < 1) :
    lqAppetite δ β₁ u₀ w < lqAppetite δ β₂ u₀ w := by
  unfold lqAppetite
  have h1 : 0 < 1 - β₁ * (1 - δ) := by nlinarith
  have h2 : 0 < 1 - β₂ * (1 - δ) := by nlinarith
  have e : ∀ β : ℝ, β * δ * (w / (1 - β * (1 - δ))) = β * δ * w / (1 - β * (1 - δ)) :=
    fun β => by ring
  rw [e, e, add_lt_add_iff_left, div_lt_div_iff₀ h1 h2]
  nlinarith [mul_pos (mul_pos hδ0 hw) (sub_pos.2 hβ)]

/-- **The appetite strictly increases in the Sender's state slope `w`.**
Scope: linear–quadratic benchmark only. -/
theorem lqAppetite_lt_of_w_lt {δ βS u₀ w₁ w₂ : ℝ} (hδ0 : 0 < δ) (hβ0 : 0 < βS)
    (hβ1 : βS < 1) (hw : w₁ < w₂) : lqAppetite δ βS u₀ w₁ < lqAppetite δ βS u₀ w₂ := by
  unfold lqAppetite
  have h1 : 0 < 1 - βS * (1 - δ) := by nlinarith
  have : w₁ / (1 - βS * (1 - δ)) < w₂ / (1 - βS * (1 - δ)) := div_lt_div_of_pos_right hw h1
  have := mul_lt_mul_of_pos_left this (mul_pos hβ0 hδ0)
  linarith

/-- **The appetite strictly increases in the adjustment rate `δ`.**
Scope: linear–quadratic benchmark only. -/
theorem lqAppetite_lt_of_δ_lt {δ₁ δ₂ βS u₀ w : ℝ} (hδ₁ : 0 < δ₁) (hδ : δ₁ < δ₂)
    (hβ0 : 0 < βS) (hβ1 : βS < 1) (hw : 0 < w) :
    lqAppetite δ₁ βS u₀ w < lqAppetite δ₂ βS u₀ w := by
  unfold lqAppetite
  have h1 : 0 < 1 - βS * (1 - δ₁) := by nlinarith
  have h2 : 0 < 1 - βS * (1 - δ₂) := by nlinarith
  have e : ∀ d : ℝ, βS * d * (w / (1 - βS * (1 - d))) = βS * d * w / (1 - βS * (1 - d)) :=
    fun d => by ring
  rw [e, e, add_lt_add_iff_left, div_lt_div_iff₀ h1 h2]
  nlinarith [mul_pos (mul_pos (mul_pos hβ0 hw) (sub_pos.2 hβ1)) (sub_pos.2 hδ)]

/-- **Equilibrium levels are ordered by the appetite.** For two benchmark economies with the same
placation rate `k` and curvature `q`, if the first has the smaller appetite `A`, then every
zero-sanction equilibrium of the first complies less than every zero-sanction equilibrium of the
second, at every state (relief price `A/k`); every full-defiance equilibrium of the first
sanctions less than every full-defiance equilibrium of the second, at every state (defiance
sanction `A/q`); and the defiance steady state `A/q` of the first is lower.
Scope: linear–quadratic benchmark only. -/
theorem levels_lt_of_A_lt (P₁ P₂ : LQData) (hk : P₁.k = P₂.k) (hq : P₁.q = P₂.q)
    (hA : P₁.A < P₂.A) (hInt₁ : P₁.E.Interior) (hP₁ : P₁.E.Placable) (hInt₂ : P₂.E.Interior)
    (hP₂ : P₂.E.Placable) :
    (∀ Eq₁ : P₁.E.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ Eq₂ : P₂.E.toParams.FeedbackStackelbergEquilibriumTop,
        (∀ x ∈ Sanctions.I, P₁.E.toParams.dynamicEquilibriumRule Eq₁ x = 0) →
        (∀ x ∈ Sanctions.I, P₂.E.toParams.dynamicEquilibriumRule Eq₂ x = 0) →
        ∀ x ∈ Sanctions.I, Eq₁.α x < Eq₂.α x)
    ∧ (∀ Eq₁ : P₁.E.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ Eq₂ : P₂.E.toParams.FeedbackStackelbergEquilibriumTop,
        (∀ x ∈ Sanctions.I, Eq₁.α x = 0) → (∀ x ∈ Sanctions.I, Eq₂.α x = 0) →
        ∀ x ∈ Sanctions.I, P₁.E.toParams.dynamicEquilibriumRule Eq₁ x
          < P₂.E.toParams.dynamicEquilibriumRule Eq₂ x)
    ∧ P₁.A / P₁.q < P₂.A / P₂.q := by
  have hAq : P₁.A / P₁.q < P₂.A / P₂.q := by
    rw [hq]; exact div_lt_div_of_pos_right hA P₂.hq
  refine ⟨fun Eq₁ Eq₂ h₁ h₂ x hx => ?_, fun Eq₁ Eq₂ h₁ h₂ x hx => ?_, hAq⟩
  · rw [P₁.relief_policy_eq hInt₁ hP₁ Eq₁ h₁ hx, P₂.relief_policy_eq hInt₂ hP₂ Eq₂ h₂ hx, hk]
    exact div_lt_div_of_pos_right hA P₂.hk
  · rw [P₁.defiance_rule_eq hInt₁ Eq₁ h₁ hx, P₂.defiance_rule_eq hInt₂ Eq₂ h₂ hx]
    exact hAq

/-- **Comparative statics in the Sender's patience** (plan LQ-1(d)). Two benchmark economies that
differ only in `β_S`, with `β_S¹ < β_S²`: the relief price `A/k`, the defiance sanction `A/q` and
the defiance steady state `A/q` are strictly higher at `β_S²`, in every equilibrium of the
respective kind; `β_T*` is the same.
Scope: linear–quadratic benchmark only. -/
theorem comparative_statics_βS (P₁ P₂ : LQData) (hδ : P₁.δ = P₂.δ) (hu : P₁.u₀ = P₂.u₀)
    (hw : P₁.w = P₂.w) (hk : P₁.k = P₂.k) (hq : P₁.q = P₂.q) (hℓ : P₁.ℓ = P₂.ℓ)
    (hc : P₁.c = P₂.c) (hv : P₁.v = P₂.v) (hβ : P₁.βS < P₂.βS) :
    P₁.A < P₂.A ∧ P₁.A / P₁.k < P₂.A / P₂.k ∧ P₁.A / P₁.q < P₂.A / P₂.q
      ∧ P₁.E.betaStar = P₂.E.betaStar := by
  have hA : P₁.A < P₂.A := by
    rw [A_eq_lqAppetite, A_eq_lqAppetite, hδ, hu, hw]
    exact lqAppetite_lt_of_βS_lt P₂.hδ0 P₂.hw P₁.hβS0 hβ P₂.hβS1
  refine ⟨hA, ?_, ?_, ?_⟩
  · rw [hk]; exact div_lt_div_of_pos_right hA P₂.hk
  · rw [hq]; exact div_lt_div_of_pos_right hA P₂.hq
  · rw [betaStar_eq, betaStar_eq]
    unfold βstar D
    rw [hδ, hq, hk, hℓ, hc, hv]

/-- **Comparative statics in the Sender's state slope** (plan LQ-1(d)). Two benchmark economies
that differ only in `w`, with `w¹ < w²`: the relief price, the defiance sanction and the defiance
steady state are strictly higher at `w²`; `β_T*` is the same.
Scope: linear–quadratic benchmark only. -/
theorem comparative_statics_w (P₁ P₂ : LQData) (hδ : P₁.δ = P₂.δ) (hu : P₁.u₀ = P₂.u₀)
    (hβS : P₁.βS = P₂.βS) (hk : P₁.k = P₂.k) (hq : P₁.q = P₂.q) (hℓ : P₁.ℓ = P₂.ℓ)
    (hc : P₁.c = P₂.c) (hv : P₁.v = P₂.v) (hw : P₁.w < P₂.w) :
    P₁.A < P₂.A ∧ P₁.A / P₁.k < P₂.A / P₂.k ∧ P₁.A / P₁.q < P₂.A / P₂.q
      ∧ P₁.E.betaStar = P₂.E.betaStar := by
  have hA : P₁.A < P₂.A := by
    rw [A_eq_lqAppetite, A_eq_lqAppetite, hδ, hu, hβS]
    exact lqAppetite_lt_of_w_lt P₂.hδ0 P₂.hβS0 P₂.hβS1 hw
  refine ⟨hA, ?_, ?_, ?_⟩
  · rw [hk]; exact div_lt_div_of_pos_right hA P₂.hk
  · rw [hq]; exact div_lt_div_of_pos_right hA P₂.hq
  · rw [betaStar_eq, betaStar_eq]
    unfold βstar D
    rw [hδ, hq, hk, hℓ, hc, hv]

/-- **Comparative statics in the adjustment rate** (plan LQ-1(d)). Two benchmark economies that
differ only in `δ`, with `δ¹ < δ²`: the relief price, the defiance sanction and the defiance steady
state are strictly higher at `δ²`. (`β_T*` moves with `δ`.)
Scope: linear–quadratic benchmark only. -/
theorem comparative_statics_δ (P₁ P₂ : LQData) (hβS : P₁.βS = P₂.βS) (hu : P₁.u₀ = P₂.u₀)
    (hw : P₁.w = P₂.w) (hk : P₁.k = P₂.k) (hq : P₁.q = P₂.q) (hδ : P₁.δ < P₂.δ) :
    P₁.A < P₂.A ∧ P₁.A / P₁.k < P₂.A / P₂.k ∧ P₁.A / P₁.q < P₂.A / P₂.q := by
  have hA : P₁.A < P₂.A := by
    rw [A_eq_lqAppetite, A_eq_lqAppetite, hβS, hu, hw]
    exact lqAppetite_lt_of_δ_lt P₁.hδ0 hδ P₂.hβS0 P₂.hβS1 P₂.hw
  refine ⟨hA, ?_, ?_⟩
  · rw [hk]; exact div_lt_div_of_pos_right hA P₂.hk
  · rw [hq]; exact div_lt_div_of_pos_right hA P₂.hq

/-- **The appetite's derivative in the Sender's patience**:
`∂A/∂β_S = δ w/(1 − β_S(1 − δ))²`. The relief price `A/k` and the defiance sanction `A/q` move
with `1/k` and `1/q` times it.
Scope: linear–quadratic benchmark only. -/
theorem hasDerivAt_lqAppetite_βS {δ β u₀ w : ℝ} (hden : 1 - β * (1 - δ) ≠ 0) :
    HasDerivAt (fun b => lqAppetite δ b u₀ w) (δ * w / (1 - β * (1 - δ)) ^ 2) β := by
  have h1 : HasDerivAt (fun b : ℝ => 1 - b * (1 - δ)) (-(1 - δ)) β := by
    simpa using ((hasDerivAt_id β).mul_const (1 - δ)).const_sub 1
  have h2 := (hasDerivAt_const β w).div h1 hden
  have h3 : HasDerivAt (fun b : ℝ => b * δ) δ β := by
    simpa using (hasDerivAt_id β).mul_const δ
  have h4 := (h3.mul h2).const_add u₀
  unfold lqAppetite
  convert h4 using 1
  simp only [Pi.div_apply]
  field_simp
  ring

/-- **The appetite's derivative in the Sender's state slope**:
`∂A/∂w = β_S δ/(1 − β_S(1 − δ))`.
Scope: linear–quadratic benchmark only. -/
theorem hasDerivAt_lqAppetite_w {δ βS u₀ w : ℝ} :
    HasDerivAt (fun x => lqAppetite δ βS u₀ x) (βS * δ * (1 / (1 - βS * (1 - δ)))) w := by
  have h := ((hasDerivAt_id' w).div_const (1 - βS * (1 - δ))).const_mul (βS * δ)
  exact h.const_add u₀

/-- **The appetite's derivative in the adjustment rate**:
`∂A/∂δ = β_S(1 − β_S) w/(1 − β_S(1 − δ))²`.
Scope: linear–quadratic benchmark only. -/
theorem hasDerivAt_lqAppetite_δ {δ βS u₀ w : ℝ} (hden : 1 - βS * (1 - δ) ≠ 0) :
    HasDerivAt (fun d => lqAppetite d βS u₀ w) (βS * (1 - βS) * w / (1 - βS * (1 - δ)) ^ 2) δ := by
  have h1 : HasDerivAt (fun d : ℝ => 1 - βS * (1 - d)) βS δ := by
    simpa using (((hasDerivAt_id δ).const_sub 1).const_mul βS).const_sub 1
  have h2 := (hasDerivAt_const δ w).div h1 hden
  have h3 : HasDerivAt (fun d : ℝ => βS * d) βS δ := by
    simpa using (hasDerivAt_id δ).const_mul βS
  have h4 := (h3.mul h2).const_add u₀
  unfold lqAppetite
  convert h4 using 1
  simp only [Pi.div_apply]
  field_simp
  ring

/-- **`β_T*` does not depend on the Sender's patience, its state slope or its appetite floor**:
two benchmark economies with the same `δ`, `q`, `k`, `ℓ`, `c`, `v` have the same threshold,
whatever their `β_S`, `w`, `u₀` (and `β_T`).
Scope: linear–quadratic benchmark only. -/
theorem betaStar_indep (P₁ P₂ : LQData) (hδ : P₁.δ = P₂.δ) (hq : P₁.q = P₂.q) (hk : P₁.k = P₂.k)
    (hℓ : P₁.ℓ = P₂.ℓ) (hc : P₁.c = P₂.c) (hv : P₁.v = P₂.v) :
    P₁.E.betaStar = P₂.E.betaStar := by
  rw [betaStar_eq, betaStar_eq]
  unfold βstar D
  rw [hδ, hq, hk, hℓ, hc, hv]

end LQData

end

end Examples
end Sanctions
