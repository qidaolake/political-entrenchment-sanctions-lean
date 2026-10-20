/-
Sanctions/Examples/AffineWindowWhole.lean

**Equilibria with interior compliance fill the whole window at the affine-window member**
(step 2, target 2c, part E, 2026-10-10; referee M3 item (v)).

`AffineWindowInstance.lean` proves that at the affine-window member (`q = 3`, `u₀ = 1`,
`k = 3`, `r = 1/2`, `w = 1`, `ℓ = 1`, `c = 4`, `n = 0`, `v = 30`, `F = (x+s)/2`, `β_S = 1/2`)
zero sanctions exist exactly up to `β_R = 36/197` and full defiance exactly from
`β_D = (82 − 7√2)/394`; `AffineWindowContinuum.lean` gives a continuum of equilibria at the
single discount `β₁ = 25248/138097` inside the window. This file fills the window.

1. **A converse** (`AQCert`, `AQCert.equilibrium`, `AQCert.rule`). On the linear–quadratic
   benchmark (`F` affine, `n = 0`), affine-policy, quadratic-value data that solve the Sender's
   Bellman coefficient equations, the Target's value recursions and the Target's indifference
   on its compliance plateau, and that are feasible (policy in `[0,1]`, realised sanction
   nonnegative, vertex at zero compliance at most one), define a top-selector equilibrium.
2. **Two families at the member** (`awwCert`, `awwFamily`, `aww_family`). For every realised
   slope `e₁` with `|e₁| ≤ 3/17`, at the discount
   `β_T(e₁) = 12(4e₁² + 21)/(197(e₁² + 7))`, the policy `1/5 + a₁(e₁)·x`,
   `a₁(e₁) = 7(e₁² − 6e₁ + 1)/(6(e₁² + 7))`, with realised sanction
   `e₀(e₁) + e₁·x`, `e₀(e₁) = 11(e₁² + 7)/(105(3 − e₁))`, is an equilibrium with interior
   compliance and interior, positive sanctions. All coefficients are rational in `e₁`:
   `S₂ = 12e₁²/(e₁² + 7)`, the Target's value slope is `197/6`.
3. **The whole window** (`aw_exists_on_window`). For every `β_T ∈ (36/197, (82 − 7√2)/394)`
   the slope `e₁ = √((1379β_T − 252)/(48 − 197β_T)) ∈ (0, 3/17]` has `β_T(±e₁) = β_T`, so two
   distinct equilibria with interior compliance and positive sanctions exist, one in each
   family. The family's ends are `β_T(0) = 36/197` and `β_T(3 − 2√2) = (82 − 7√2)/394`
   (`awwb_zero`, `awwb_defiance`): its slope runs from relief to defiance.

**Rule 9.** Existence certificates at one member; the families are not shown to exhaust the
equilibria in the window. **Rule 1.** The Sender's response is its unique maximiser; the
Target's policy is a maximiser at every state (weakly: it is indifferent on its plateau).
**Rule 3.** No assumption is introduced. **Rule 22.** AFFINE: one member of the family.
-/
import Sanctions.Examples.AffineWindowInstance

namespace Sanctions
namespace Examples
namespace AWWhole

open Set BoundedContinuousFunction AbstractGame

noncomputable section

/-! ## 1. A converse: affine–quadratic certificates are equilibria -/

/-- **An affine–quadratic equilibrium certificate** on the linear–quadratic benchmark: an affine
policy `a₀ + a₁x`, a quadratic Sender value `S₂y² + S₁y + S₀`, a realised sanction `e₀ + e₁x` and
an affine Target value `P₁y + P₀`, with `Q = q − 2β_Sδ²S₂ > 0`, solving

* the vertex relations `Q·e₁ = r − k·a₁ + 2β_Sδ(1−δ)S₂` and `Q·e₀ = u₀ − k·a₀ + β_SδS₁`;
* the Sender's Bellman coefficient equations (`hS₂`, `hS₁`, `hS₀`);
* the Target's value recursions (`hP₁`, `hP₀`);
* the Target's indifference on its compliance plateau `ℓQ = k(c − β_TδP₁)`;
* feasibility: policy in `[0,1]`, realised sanction nonnegative, and the vertex at zero
  compliance at most one (`hcap`, written as `Q(e₀ + e₁x) + k(a₀ + a₁x) ≤ Q`).

Scope: linear–quadratic benchmark only (a certificate format; used at the example economy). -/
structure AQCert (p : Params) (q u₀ k r w ℓ c v : ℝ) where
  a₀ : ℝ
  a₁ : ℝ
  S₂ : ℝ
  S₁ : ℝ
  S₀ : ℝ
  e₀ : ℝ
  e₁ : ℝ
  P₁ : ℝ
  P₀ : ℝ
  hQ : 0 < q - 2 * p.β_S * p.δ ^ 2 * S₂
  he₁ : (q - 2 * p.β_S * p.δ ^ 2 * S₂) * e₁ = r - k * a₁ + 2 * p.β_S * p.δ * (1 - p.δ) * S₂
  he₀ : (q - 2 * p.β_S * p.δ ^ 2 * S₂) * e₀ = u₀ - k * a₀ + p.β_S * p.δ * S₁
  hS₂ : S₂ = p.β_S * S₂ * (1 - p.δ) ^ 2 + (q - 2 * p.β_S * p.δ ^ 2 * S₂) / 2 * e₁ ^ 2
  hS₁ : S₁ = w + p.β_S * S₁ * (1 - p.δ) + (q - 2 * p.β_S * p.δ ^ 2 * S₂) * e₀ * e₁
  hS₀ : S₀ = p.β_S * S₀ + (q - 2 * p.β_S * p.δ ^ 2 * S₂) / 2 * e₀ ^ 2
  hP₁ : P₁ * (1 - p.β_T * (1 - p.δ + p.δ * e₁)) = v - ℓ * a₁ - c * e₁
  hP₀ : P₀ * (1 - p.β_T) = -ℓ * a₀ - c * e₀ + p.β_T * P₁ * p.δ * e₀
  hind : ℓ * (q - 2 * p.β_S * p.δ ^ 2 * S₂) = k * (c - p.β_T * p.δ * P₁)
  hpol : ∀ x ∈ Sanctions.I, a₀ + a₁ * x ∈ Sanctions.I
  hsan : ∀ x ∈ Sanctions.I, 0 ≤ e₀ + e₁ * x
  hcap : ∀ x ∈ Sanctions.I,
    (q - 2 * p.β_S * p.δ ^ 2 * S₂) * (e₀ + e₁ * x) + k * (a₀ + a₁ * x)
      ≤ q - 2 * p.β_S * p.δ ^ 2 * S₂

namespace AQCert

variable {p : Params} {q u₀ k r w ℓ c v : ℝ} (C : AQCert p q u₀ k r w ℓ c v)

/-- The certificate's dynamic curvature `Q`.

Scope: linear–quadratic benchmark only (a definition). -/
def Qc : ℝ := q - 2 * p.β_S * p.δ ^ 2 * C.S₂

/-- The vertex of the Sender's objective at `(x, a)`.

Scope: linear–quadratic benchmark only (a definition). -/
def vert (x a : ℝ) : ℝ :=
  (u₀ - k * a + r * x + p.β_S * p.δ * (2 * C.S₂ * (1 - p.δ) * x + C.S₁)) / C.Qc

/-- The certificate's Sender value.

Scope: linear–quadratic benchmark only (a definition). -/
def VS : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ := quadBCF C.S₂ C.S₁ C.S₀

/-- The certificate's Target value.

Scope: linear–quadratic benchmark only (a definition). -/
def VT : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ := ChordEconomy.affBCF C.P₁ C.P₀

/-- The certificate's policy.

Scope: linear–quadratic benchmark only (a definition). -/
def pol (x : ℝ) : ℝ := C.a₀ + C.a₁ * x

/-- The policy is feasible.

Scope: linear–quadratic benchmark only. -/
theorem pol_mem {x : ℝ} (hx : x ∈ Sanctions.I) : C.pol x ∈ Sanctions.I := C.hpol x hx

/-- The affine transition maps the square into the state set.

Scope: linear–quadratic benchmark only. -/
theorem F_mem (hF : p.F = affineF p.δ) {x s : ℝ} (hx : x ∈ Sanctions.I)
    (hs : s ∈ Sanctions.I) : p.F x s ∈ (Sanctions.S : Set ℝ) := by
  rw [hF]; unfold affineF
  have h := p.δ_mem
  have h1 : 0 ≤ 1 - p.δ := by linarith [h.2]
  constructor
  · nlinarith [mul_nonneg h1 hx.1, mul_nonneg h.1.le hs.1]
  · nlinarith [mul_nonneg h1 (sub_nonneg.mpr hx.2), mul_nonneg h.1.le (sub_nonneg.mpr hs.2)]

/-- `Q` times the vertex.

Scope: linear–quadratic benchmark only. -/
theorem Qc_mul_vert (x a : ℝ) :
    C.Qc * C.vert x a = u₀ - k * a + r * x + p.β_S * p.δ * (2 * C.S₂ * (1 - p.δ) * x + C.S₁) := by
  have hQ0 : C.Qc ≠ 0 := C.hQ.ne'
  unfold vert; field_simp

/-- `Q` times the vertex, through the realised sanction: `Q(e₀ + e₁x) + k(a₀ + a₁x) − k·a`.

Scope: linear–quadratic benchmark only. -/
theorem Qc_mul_vert' (x a : ℝ) :
    C.Qc * C.vert x a = C.Qc * (C.e₀ + C.e₁ * x) + k * (C.a₀ + C.a₁ * x) - k * a := by
  rw [C.Qc_mul_vert]
  have h1 := C.he₁
  have h0 := C.he₀
  unfold Qc
  linear_combination -h0 - x * h1

/-- At the policy the vertex is the realised sanction `e₀ + e₁x`.

Scope: linear–quadratic benchmark only. -/
theorem vert_pol (x : ℝ) : C.vert x (C.pol x) = C.e₀ + C.e₁ * x := by
  have h := C.Qc_mul_vert' x (C.pol x)
  unfold pol at h ⊢
  have h' : C.Qc * C.vert x (C.a₀ + C.a₁ * x) = C.Qc * (C.e₀ + C.e₁ * x) := by
    rw [h]; ring
  exact mul_left_cancel₀ C.hQ.ne' h'

/-- The vertex is at most one at every nonnegative compliance level.

Scope: linear–quadratic benchmark only. -/
theorem vert_le_one (hk : 0 < k) {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : 0 ≤ a) :
    C.vert x a ≤ 1 := by
  have h := C.Qc_mul_vert' x a
  have hcap := C.hcap x hx
  have hQ : 0 < C.Qc := C.hQ
  have h1 : C.Qc * C.vert x a ≤ C.Qc * 1 := by
    rw [h, mul_one]; unfold Qc; nlinarith [mul_nonneg hk.le ha]
  exact le_of_mul_le_mul_left h1 hQ

/-- **The Sender's objective is a concave parabola around the vertex.**

Scope: linear–quadratic benchmark only. -/
theorem senderObj (hUS : p.U_S = symU_S q u₀ k r w) (hF : p.F = affineF p.δ)
    {x : ℝ} (hx : x ∈ Sanctions.I) (a : ℝ) {s : ℝ} (hs : s ∈ Sanctions.I) :
    p.U_S x a s + p.β_S * C.VS (Sanctions.clipS' (p.F x s))
      = (w * x + p.β_S * (C.S₂ * ((1 - p.δ) * x) ^ 2 + C.S₁ * ((1 - p.δ) * x) + C.S₀)
          + C.Qc / 2 * C.vert x a ^ 2)
        - C.Qc / 2 * (s - C.vert x a) ^ 2 := by
  have hQv := C.Qc_mul_vert x a
  unfold VS
  rw [quadBCF_apply, Sanctions.clipS'_val_eq_of_mem (F_mem hF hx hs), hUS, hF]
  unfold symU_S affineF
  unfold Qc at hQv ⊢
  linear_combination (-s) * hQv

/-- **The Sender's response is the positive part of the vertex** at every compliance level.

Scope: linear–quadratic benchmark only. -/
theorem σ_eq (hUS : p.U_S = symU_S q u₀ k r w) (hF : p.F = affineF p.δ) (hk : 0 < k)
    {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ} (ha : a ∈ Sanctions.I) :
    p.σ_dyn_top C.VS x a = max 0 (C.vert x a) := by
  rw [σ_dyn_top_eq_clip p C.VS (half_pos (show 0 < C.Qc from C.hQ))
      (fun _ hs => C.senderObj hUS hF hx a hs),
    min_eq_right (C.vert_le_one hk hx ha.1)]

/-- The Target's objective against the certificate's values.

Scope: linear–quadratic benchmark only. -/
theorem joint_eq (hUS : p.U_S = symU_S q u₀ k r w) (hUT : p.U_T = symU_T ℓ c 0 v)
    (hF : p.F = affineF p.δ) (hk : 0 < k) {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I) :
    p.joint_T_top_integrand C.VT C.VS x a
      = v * x + p.β_T * (C.P₁ * ((1 - p.δ) * x) + C.P₀) - ℓ * a
        - (c - p.β_T * p.δ * C.P₁) * max 0 (C.vert x a) := by
  simp only [Params.joint_T_top_integrand]
  rw [C.σ_eq hUS hF hk hx ha]
  have hρ : max 0 (C.vert x a) ∈ Sanctions.I :=
    ⟨le_max_left _ _, max_le zero_le_one (C.vert_le_one hk hx ha.1)⟩
  unfold VT
  rw [ChordEconomy.affBCF_apply, Sanctions.clipS'_val_eq_of_mem (F_mem hF hx hρ), hUT, hF]
  unfold symU_T affineF
  ring

/-- **The Target is indifferent on its plateau and loses beyond it**: the objective at any
compliance level is at most its value at the policy.

Scope: linear–quadratic benchmark only. -/
theorem joint_le (hUS : p.U_S = symU_S q u₀ k r w) (hUT : p.U_T = symU_T ℓ c 0 v)
    (hF : p.F = affineF p.δ) (hk : 0 < k) (hℓ : 0 ≤ ℓ) {x : ℝ} (hx : x ∈ Sanctions.I) {a : ℝ}
    (ha : a ∈ Sanctions.I) :
    p.joint_T_top_integrand C.VT C.VS x a ≤ p.joint_T_top_integrand C.VT C.VS x (C.pol x) := by
  rw [C.joint_eq hUS hUT hF hk hx ha, C.joint_eq hUS hUT hF hk hx (C.pol_mem hx), C.vert_pol,
    max_eq_right (C.hsan x hx)]
  have hind : k * (c - p.β_T * p.δ * C.P₁) = ℓ * C.Qc := C.hind.symm
  have hQv := C.Qc_mul_vert' x a
  have key : k * (ℓ * C.pol x + (c - p.β_T * p.δ * C.P₁) * (C.e₀ + C.e₁ * x))
      ≤ k * (ℓ * a + (c - p.β_T * p.δ * C.P₁) * max 0 (C.vert x a)) := by
    have e1 : k * (ℓ * C.pol x + (c - p.β_T * p.δ * C.P₁) * (C.e₀ + C.e₁ * x))
        = ℓ * (C.Qc * (C.e₀ + C.e₁ * x) + k * C.pol x) := by
      linear_combination (C.e₀ + C.e₁ * x) * hind
    have e2 : k * (ℓ * a + (c - p.β_T * p.δ * C.P₁) * max 0 (C.vert x a))
        = k * ℓ * a + ℓ * C.Qc * max 0 (C.vert x a) := by
      linear_combination (max 0 (C.vert x a)) * hind
    rw [e1, e2]
    unfold pol
    rcases le_total (C.vert x a) 0 with h | h
    · rw [max_eq_left h, mul_zero, add_zero]
      have hQ : 0 < C.Qc := C.hQ
      have : C.Qc * C.vert x a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hQ.le h
      nlinarith [mul_le_mul_of_nonneg_left (show C.Qc * (C.e₀ + C.e₁ * x)
        + k * (C.a₀ + C.a₁ * x) ≤ k * a by linarith) hℓ]
    · rw [max_eq_right h]
      have heq : ℓ * (C.Qc * (C.e₀ + C.e₁ * x) + k * (C.a₀ + C.a₁ * x))
          = k * ℓ * a + ℓ * C.Qc * C.vert x a := by
        linear_combination (-ℓ) * hQv
      exact heq.le
  have hk' := hk
  have := le_of_mul_le_mul_left key hk'
  linarith

/-- The Target's objective at the policy is the certificate's Target value.

Scope: linear–quadratic benchmark only. -/
theorem joint_pol (hUS : p.U_S = symU_S q u₀ k r w) (hUT : p.U_T = symU_T ℓ c 0 v)
    (hF : p.F = affineF p.δ) (hk : 0 < k) {x : ℝ} (hx : x ∈ Sanctions.I) :
    p.joint_T_top_integrand C.VT C.VS x (C.pol x) = C.P₁ * x + C.P₀ := by
  rw [C.joint_eq hUS hUT hF hk hx (C.pol_mem hx), C.vert_pol, max_eq_right (C.hsan x hx)]
  have h1 := C.hP₁
  have h0 := C.hP₀
  unfold pol
  linear_combination (-x) * h1 - h0

/-- **The certificate's equilibrium.**

Scope: linear–quadratic benchmark only (a construction; used at the example economy). -/
def equilibrium (hUS : p.U_S = symU_S q u₀ k r w) (hUT : p.U_T = symU_T ℓ c 0 v)
    (hF : p.F = affineF p.δ) (hk : 0 < k) (hℓ : 0 ≤ ℓ) : p.FeedbackStackelbergEquilibriumTop where
  V_T := C.VT
  V_S := C.VS
  α := C.pol
  hα := by unfold pol; fun_prop
  α_mem := fun x hx => C.hpol x hx
  V_S_fix := by
    ext y
    change C.VS y = sSup ((fun s => p.integrandS C.pol (fun z => C.VS z) (y.val, s))
      '' Sanctions.I)
    have hy := y.property
    have hval : ∀ s ∈ Sanctions.I, p.integrandS C.pol (fun z => C.VS z) (y.val, s)
        = (w * y.val + p.β_S * (C.S₂ * ((1 - p.δ) * y.val) ^ 2 + C.S₁ * ((1 - p.δ) * y.val)
            + C.S₀) + C.Qc / 2 * C.vert y.val (C.pol y.val) ^ 2)
          - C.Qc / 2 * (s - C.vert y.val (C.pol y.val)) ^ 2 := by
      intro s hs
      simp only [Params.integrandS]
      exact C.senderObj hUS hF hy (C.pol y.val) hs
    have hv0 : 0 ≤ C.vert y.val (C.pol y.val) := by rw [C.vert_pol]; exact C.hsan _ hy
    have hv1 : C.vert y.val (C.pol y.val) ≤ 1 := C.vert_le_one hk hy (C.pol_mem hy).1
    have hVy : C.VS y = (w * y.val + p.β_S * (C.S₂ * ((1 - p.δ) * y.val) ^ 2
        + C.S₁ * ((1 - p.δ) * y.val) + C.S₀) + C.Qc / 2 * C.vert y.val (C.pol y.val) ^ 2) := by
      rw [C.vert_pol]
      unfold VS
      rw [quadBCF_apply]
      have h2 := C.hS₂
      have h1 := C.hS₁
      have h0 := C.hS₀
      unfold Qc
      linear_combination y.val ^ 2 * h2 + y.val * h1 + h0
    have hgt : IsGreatest ((fun s => p.integrandS C.pol (fun z => C.VS z) (y.val, s))
        '' Sanctions.I) (C.VS y) := by
      refine ⟨⟨C.vert y.val (C.pol y.val), ⟨hv0, hv1⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [hval _ ⟨hv0, hv1⟩, sub_self, hVy]
        ring
      · rintro _ ⟨s, hs, rfl⟩
        dsimp only
        rw [hval s hs, hVy]
        have hQ : 0 < C.Qc := C.hQ
        nlinarith [mul_nonneg hQ.le (sq_nonneg (s - C.vert y.val (C.pol y.val)))]
    exact hgt.csSup_eq.symm
  V_T_fix_top := by
    intro y
    have hy := y.property
    have hv : C.VT y = C.P₁ * y.val + C.P₀ := by unfold VT; rw [ChordEconomy.affBCF_apply]
    have hgt : IsGreatest ((fun a => p.joint_T_top_integrand C.VT C.VS y.val a) '' Sanctions.I)
        (C.VT y) := by
      refine ⟨⟨C.pol y.val, C.pol_mem hy, ?_⟩, ?_⟩
      · dsimp only
        rw [C.joint_pol hUS hUT hF hk hy, hv]
      · rintro _ ⟨a, ha, rfl⟩
        dsimp only
        rw [hv, ← C.joint_pol hUS hUT hF hk hy]
        exact C.joint_le hUS hUT hF hk hℓ hy ha
    exact hgt.csSup_eq.symm
  α_opt_top := fun x hx => by
    intro a ha
    exact C.joint_le hUS hUT hF hk hℓ hx ha

/-- **The certificate's realised sanction is `e₀ + e₁x`.**

Scope: linear–quadratic benchmark only. -/
theorem rule (hUS : p.U_S = symU_S q u₀ k r w) (hUT : p.U_T = symU_T ℓ c 0 v)
    (hF : p.F = affineF p.δ) (hk : 0 < k) (hℓ : 0 ≤ ℓ) {x : ℝ} (hx : x ∈ Sanctions.I) :
    p.dynamicEquilibriumRule (C.equilibrium hUS hUT hF hk hℓ) x = C.e₀ + C.e₁ * x := by
  change p.σ_dyn_top C.VS x (C.pol x) = _
  rw [C.σ_eq hUS hF hk hx (C.pol_mem hx), C.vert_pol, max_eq_right (C.hsan x hx)]

end AQCert

/-! ## 2. Two families at the affine-window member

The data are rational in the realised slope `e₁` (written `e`); the intercept of the policy is
`1/5`. The denominators are `e² + 7`, `3 − e` and `149e² + 1127`, all positive for `|e| ≤ 3/17`. -/

/-- The discount along the families, `β_T(e) = 12(4e² + 21)/(197(e² + 7))`.

Scope: at the example economy only (not general). -/
def awwb (e : ℝ) : ℝ := 12 * (4 * e ^ 2 + 21) / (197 * (e ^ 2 + 7))

/-- The Sender value's curvature along the families, `S₂(e) = 12e²/(e² + 7)`.

Scope: at the example economy only (not general). -/
def awwS₂ (e : ℝ) : ℝ := 12 * e ^ 2 / (e ^ 2 + 7)

/-- The policy slope along the families, `a₁(e) = 7(e² − 6e + 1)/(6(e² + 7))`.

Scope: at the example economy only (not general). -/
def awwa₁ (e : ℝ) : ℝ := 7 * (e ^ 2 - 6 * e + 1) / (6 * (e ^ 2 + 7))

/-- The realised sanction's intercept along the families, `e₀(e) = 11(e² + 7)/(105(3 − e))`.

Scope: at the example economy only (not general). -/
def awwe₀ (e : ℝ) : ℝ := 11 * (e ^ 2 + 7) / (105 * (3 - e))

/-- The Sender value's slope along the families, `S₁(e) = (20 + 8e)/(5(3 − e))`.

Scope: at the example economy only (not general). -/
def awwS₁ (e : ℝ) : ℝ := (20 + 8 * e) / (5 * (3 - e))

/-- The Sender value's intercept along the families, `S₀(e) = 121(e² + 7)/(525(3 − e)²)`.

Scope: at the example economy only (not general). -/
def awwS₀ (e : ℝ) : ℝ := 121 * (e ^ 2 + 7) / (525 * (3 - e) ^ 2)

/-- The Target value's intercept along the families.

Scope: at the example economy only (not general). -/
def awwP₀ (e : ℝ) : ℝ :=
  -(197 * (e ^ 2 + 7) * (20 - 3 * e)) / (15 * (3 - e) * (149 * e ^ 2 + 1127))

/-- Scope: at the example economy only (not general). -/
theorem awwb_pos (e : ℝ) : 0 < awwb e := by unfold awwb; positivity

/-- Scope: at the example economy only (not general). -/
theorem awwb_lt_one (e : ℝ) : awwb e < 1 := by
  unfold awwb; rw [div_lt_one (by positivity)]; nlinarith [sq_nonneg e]

/-- The family's discount is even in the slope.

Scope: at the example economy only (not general). -/
theorem awwb_neg (e : ℝ) : awwb (-e) = awwb e := by unfold awwb; ring

/-- **The relief end**: `β_T(0) = 36/197 = β_R`.

Scope: at the example economy only (not general). -/
theorem awwb_zero : awwb 0 = 36 / 197 := by unfold awwb; norm_num

/-- **The defiance end**: `β_T(3 − 2√2) = (82 − 7√2)/394 = β_D`, and the policy slope vanishes
there.

Scope: at the example economy only (not general). -/
theorem awwb_defiance :
    awwb (3 - 2 * Real.sqrt 2) = (82 - 7 * Real.sqrt 2) / 394 ∧
      awwa₁ (3 - 2 * Real.sqrt 2) = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  constructor
  · unfold awwb
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    linear_combination 5516 * (Real.sqrt 2 - 1) * hs
  · unfold awwa₁
    rw [div_eq_zero_iff]
    left
    linear_combination 28 * hs

/-- The member's adjustment rate is `1/2`.

Scope: at the example economy only (not general). -/
theorem aww_δ {b : ℝ} {hb0 : 0 < b} {hb1 : b < 1} : (awParams b hb0 hb1).δ = 1 / 2 := rfl

section Member

variable {e : ℝ}

/-- `e² ≤ 9/289` on the slope range.

Scope: at the example economy only (not general). -/
theorem aww_sq_le (he : |e| ≤ 3 / 17) : e ^ 2 ≤ 9 / 289 := by
  have h := abs_le.mp he
  nlinarith [mul_nonneg (by linarith [h.1] : (0 : ℝ) ≤ e + 3 / 17)
    (by linarith [h.2] : (0 : ℝ) ≤ 3 / 17 - e)]

/-- `3 − e > 0` on the slope range.

Scope: at the example economy only (not general). -/
theorem aww_three_sub_pos (he : |e| ≤ 3 / 17) : 0 < 3 - e := by
  linarith [(abs_le.mp he).2]

/-- `Q(e) = 3 − S₂(e)/4 = 21/(e² + 7)`.

Scope: at the example economy only (not general). -/
theorem aww_Q_eq (e : ℝ) : 3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e = 21 / (e ^ 2 + 7) := by
  have hD : (e ^ 2 + 7 : ℝ) ≠ 0 := by positivity
  unfold awwS₂; field_simp; ring

/-- The certificate's curvature condition along the families.

Scope: at the example economy only (not general). -/
theorem aww_hQ (e : ℝ) : 0 < 3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e := by
  rw [aww_Q_eq]; positivity

/-- The vertex relation for the slope along the families.

Scope: at the example economy only (not general). -/
theorem aww_he₁ (e : ℝ) :
    (3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e) * e
      = 1 / 2 - 3 * awwa₁ e + 2 * (1 / 2) * (1 / 2) * (1 - 1 / 2) * awwS₂ e := by
  have hD : (e ^ 2 + 7 : ℝ) ≠ 0 := by positivity
  unfold awwS₂ awwa₁; field_simp; ring

/-- The vertex relation for the intercept along the families.

Scope: at the example economy only (not general). -/
theorem aww_he₀ (he : |e| ≤ 3 / 17) :
    (3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e) * awwe₀ e
      = 1 - 3 * (1 / 5) + 1 / 2 * (1 / 2) * awwS₁ e := by
  have hD : (e ^ 2 + 7 : ℝ) ≠ 0 := by positivity
  have hT := (aww_three_sub_pos he).ne'
  unfold awwS₂ awwe₀ awwS₁; field_simp; ring

/-- The Sender's quadratic Bellman coefficient along the families.

Scope: at the example economy only (not general). -/
theorem aww_hS₂ (e : ℝ) :
    awwS₂ e = 1 / 2 * awwS₂ e * (1 - 1 / 2) ^ 2
      + (3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e) / 2 * e ^ 2 := by
  have hD : (e ^ 2 + 7 : ℝ) ≠ 0 := by positivity
  unfold awwS₂; field_simp; ring

/-- The Sender's linear Bellman coefficient along the families.

Scope: at the example economy only (not general). -/
theorem aww_hS₁ (he : |e| ≤ 3 / 17) :
    awwS₁ e = 1 + 1 / 2 * awwS₁ e * (1 - 1 / 2)
      + (3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e) * awwe₀ e * e := by
  have hD : (e ^ 2 + 7 : ℝ) ≠ 0 := by positivity
  have hT := (aww_three_sub_pos he).ne'
  unfold awwS₂ awwe₀ awwS₁; field_simp; ring

/-- The Sender's constant Bellman coefficient along the families.

Scope: at the example economy only (not general). -/
theorem aww_hS₀ (he : |e| ≤ 3 / 17) :
    awwS₀ e = 1 / 2 * awwS₀ e
      + (3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e) / 2 * awwe₀ e ^ 2 := by
  have hD : (e ^ 2 + 7 : ℝ) ≠ 0 := by positivity
  have hT := (aww_three_sub_pos he).ne'
  unfold awwS₂ awwe₀ awwS₀; field_simp; ring

/-- The Target value's slope recursion along the families (slope `197/6`).

Scope: at the example economy only (not general). -/
theorem aww_hP₁ (e : ℝ) :
    197 / 6 * (1 - awwb e * (1 - 1 / 2 + 1 / 2 * e)) = 30 - 1 * awwa₁ e - 4 * e := by
  have hD : (e ^ 2 + 7 : ℝ) ≠ 0 := by positivity
  unfold awwb awwa₁; field_simp; ring

/-- The Target value's intercept recursion along the families.

Scope: at the example economy only (not general). -/
theorem aww_hP₀ (he : |e| ≤ 3 / 17) :
    awwP₀ e * (1 - awwb e)
      = -1 * (1 / 5) - 4 * awwe₀ e + awwb e * (197 / 6) * (1 / 2) * awwe₀ e := by
  have hD : (e ^ 2 + 7 : ℝ) ≠ 0 := by positivity
  have hT := (aww_three_sub_pos he).ne'
  have hU : (149 * e ^ 2 + 1127 : ℝ) ≠ 0 := by positivity
  unfold awwP₀ awwb awwe₀; field_simp; ring

/-- The Target's indifference on its plateau along the families.

Scope: at the example economy only (not general). -/
theorem aww_hind (e : ℝ) :
    1 * (3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e) = 3 * (4 - awwb e * (1 / 2) * (197 / 6)) := by
  have hD : (e ^ 2 + 7 : ℝ) ≠ 0 := by positivity
  unfold awwS₂ awwb; field_simp; ring

/-- Lower bound on the policy slope on the slope range.

Scope: at the example economy only (not general). -/
theorem aww_a₁_ge (he : |e| ≤ 3 / 17) : -1 / 10 ≤ awwa₁ e := by
  have h := abs_le.mp he
  unfold awwa₁
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg e]

/-- Upper bound on the policy slope on the slope range.

Scope: at the example economy only (not general). -/
theorem aww_a₁_le (he : |e| ≤ 3 / 17) : awwa₁ e ≤ 1 / 2 := by
  have h := abs_le.mp he
  have h2 := aww_sq_le he
  unfold awwa₁
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Lower bound on the sanction intercept on the slope range.

Scope: at the example economy only (not general). -/
theorem aww_e₀_ge (he : |e| ≤ 3 / 17) : 1 / 5 ≤ awwe₀ e := by
  have h := abs_le.mp he
  have hT := aww_three_sub_pos he
  unfold awwe₀
  rw [le_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg e]

/-- Upper bound on the sanction intercept on the slope range.

Scope: at the example economy only (not general). -/
theorem aww_e₀_le (he : |e| ≤ 3 / 17) : awwe₀ e ≤ 3 / 10 := by
  have h := abs_le.mp he
  have h2 := aww_sq_le he
  have hT := aww_three_sub_pos he
  unfold awwe₀
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The policy is feasible along the families.

Scope: at the example economy only (not general). -/
theorem aww_hpol (he : |e| ≤ 3 / 17) : ∀ x ∈ Sanctions.I, 1 / 5 + awwa₁ e * x ∈ Sanctions.I := by
  intro x hx
  have h1 := aww_a₁_ge he
  have h2 := aww_a₁_le he
  constructor
  · nlinarith [mul_nonneg hx.1 (by linarith : (0 : ℝ) ≤ awwa₁ e + 1 / 10), hx.1, hx.2]
  · nlinarith [mul_nonneg hx.1 (by linarith : (0 : ℝ) ≤ 1 / 2 - awwa₁ e), hx.1, hx.2]

/-- The realised sanction is nonnegative along the families.

Scope: at the example economy only (not general). -/
theorem aww_hsan (he : |e| ≤ 3 / 17) : ∀ x ∈ Sanctions.I, 0 ≤ awwe₀ e + e * x := by
  intro x hx
  have h := abs_le.mp he
  have h1 := aww_e₀_ge he
  nlinarith [mul_nonneg hx.1 (by linarith [h.1] : (0 : ℝ) ≤ e + 3 / 17), hx.1, hx.2]

/-- The vertex at zero compliance is at most one along the families.

Scope: at the example economy only (not general). -/
theorem aww_hcap (he : |e| ≤ 3 / 17) : ∀ x ∈ Sanctions.I,
    (3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e) * (awwe₀ e + e * x) + 3 * (1 / 5 + awwa₁ e * x)
      ≤ 3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e := by
  intro x hx
  have hD : (0 : ℝ) < e ^ 2 + 7 := by positivity
  have hid : (3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e) * (awwe₀ e + e * x)
      + 3 * (1 / 5 + awwa₁ e * x)
      = (3 - 2 * (1 / 2) * (1 / 2) ^ 2 * awwS₂ e)
        * (awwe₀ e + (e ^ 2 + 7) / 35 + x * (e ^ 2 + 1) / 6) := by
    rw [aww_Q_eq]; unfold awwa₁; field_simp; ring
  rw [hid]
  have hQ := aww_hQ e
  have h2 := aww_sq_le he
  have h3 := aww_e₀_le he
  have hB : awwe₀ e + (e ^ 2 + 7) / 35 + x * (e ^ 2 + 1) / 6 ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hx.2 (by positivity : (0 : ℝ) ≤ e ^ 2 + 1)]
  nlinarith [mul_le_mul_of_nonneg_left hB hQ.le]

end Member

/-- **The certificate of the family member with slope `e`** at any discount `b = β_T(e)`.

Scope: at the example economy only (not general). -/
def awwCert (e : ℝ) (he : |e| ≤ 3 / 17) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hb : b = awwb e) :
    AQCert (awParams b hb0 hb1) 3 1 3 (1 / 2) 1 1 4 30 where
  a₀ := 1 / 5
  a₁ := awwa₁ e
  S₂ := awwS₂ e
  S₁ := awwS₁ e
  S₀ := awwS₀ e
  e₀ := awwe₀ e
  e₁ := e
  P₁ := 197 / 6
  P₀ := awwP₀ e
  hQ := aww_hQ e
  he₁ := aww_he₁ e
  he₀ := aww_he₀ he
  hS₂ := aww_hS₂ e
  hS₁ := aww_hS₁ he
  hS₀ := aww_hS₀ he
  hP₁ := by subst hb; exact aww_hP₁ e
  hP₀ := by subst hb; exact aww_hP₀ he
  hind := by subst hb; exact aww_hind e
  hpol := aww_hpol he
  hsan := aww_hsan he
  hcap := aww_hcap he

/-- **The family member with slope `e`**: the certificate's equilibrium at `b = β_T(e)`.

Scope: at the example economy only (not general). -/
def awwFamily (e : ℝ) (he : |e| ≤ 3 / 17) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hb : b = awwb e) : (awParams b hb0 hb1).FeedbackStackelbergEquilibriumTop :=
  (awwCert e he hb0 hb1 hb).equilibrium aw_U_S aw_U_T aw_F (by norm_num) (by norm_num)

/-- **The families.** For every slope `|e| ≤ 3/17`, at the discount
`b = β_T(e) = 12(4e² + 21)/(197(e² + 7))`, the member `awwFamily e` is an equilibrium with policy
`1/5 + a₁(e)·x` and realised sanction `e₀(e) + e·x`; compliance and sanctions are interior at
every state.

Scope: at the example economy only (not general). -/
theorem aww_family (e : ℝ) (he : |e| ≤ 3 / 17) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hb : b = awwb e) :
    (∀ x ∈ Sanctions.I, (awwFamily e he hb0 hb1 hb).α x = 1 / 5 + awwa₁ e * x) ∧
      (∀ x ∈ Sanctions.I,
        (awParams b hb0 hb1).dynamicEquilibriumRule (awwFamily e he hb0 hb1 hb) x
          = awwe₀ e + e * x) ∧
      (∀ x ∈ Sanctions.I, 0 < (awwFamily e he hb0 hb1 hb).α x ∧
        (awwFamily e he hb0 hb1 hb).α x < 1) ∧
      (∀ x ∈ Sanctions.I,
        0 < (awParams b hb0 hb1).dynamicEquilibriumRule (awwFamily e he hb0 hb1 hb) x ∧
        (awParams b hb0 hb1).dynamicEquilibriumRule (awwFamily e he hb0 hb1 hb) x < 1) := by
  have hrule : ∀ x ∈ Sanctions.I,
      (awParams b hb0 hb1).dynamicEquilibriumRule (awwFamily e he hb0 hb1 hb) x
        = awwe₀ e + e * x := fun x hx =>
    (awwCert e he hb0 hb1 hb).rule aw_U_S aw_U_T aw_F (by norm_num) (by norm_num) hx
  have h := abs_le.mp he
  have ha₁ := aww_a₁_ge he
  have ha₁' := aww_a₁_le he
  have he₀ := aww_e₀_ge he
  have he₀' := aww_e₀_le he
  refine ⟨fun _ _ => rfl, hrule, fun x hx => ?_, fun x hx => ?_⟩
  · change 0 < 1 / 5 + awwa₁ e * x ∧ 1 / 5 + awwa₁ e * x < 1
    constructor
    · nlinarith [mul_nonneg hx.1 (by linarith : (0 : ℝ) ≤ awwa₁ e + 1 / 10), hx.2]
    · nlinarith [mul_nonneg hx.1 (by linarith : (0 : ℝ) ≤ 1 / 2 - awwa₁ e), hx.2]
  · rw [hrule x hx]
    constructor
    · nlinarith [mul_nonneg hx.1 (by linarith [h.1] : (0 : ℝ) ≤ e + 3 / 17), hx.2]
    · nlinarith [mul_nonneg hx.1 (by linarith [h.2] : (0 : ℝ) ≤ 3 / 17 - e), hx.2]

/-- The window binder of `aw_exists_on_window` gives `0 < b`. -/
theorem hb0_of_window {b : ℝ} (hb : b ∈ Ioo (36 / 197 : ℝ) ((82 - 7 * Real.sqrt 2) / 394)) :
    0 < b := lt_trans (by norm_num) hb.1

/-- The window binder of `aw_exists_on_window` gives `b < 1`. -/
theorem hb1_of_window {b : ℝ} (hb : b ∈ Ioo (36 / 197 : ℝ) ((82 - 7 * Real.sqrt 2) / 394)) :
    b < 1 := by
  have h := Real.sqrt_nonneg 2
  have h' : (82 - 7 * Real.sqrt 2) / 394 < 1 := by
    rw [div_lt_one (by norm_num)]; linarith
  exact lt_trans hb.2 h'

/-- The whole-window existence with the discount-range binders explicit (the proof; the public
`aw_exists_on_window` derives them from the window binder). -/
theorem aw_exists_on_window_core (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hb : b ∈ Ioo (36 / 197 : ℝ) ((82 - 7 * Real.sqrt 2) / 394)) :
    ∃ e₁ : ℝ, 0 < e₁ ∧ e₁ ≤ 3 / 17 ∧ b = 12 * (4 * e₁ ^ 2 + 21) / (197 * (e₁ ^ 2 + 7)) ∧
      awwa₁ e₁ < awwa₁ (-e₁) ∧
      (∃ Q : (awParams b hb0 hb1).FeedbackStackelbergEquilibriumTop,
        (∀ x ∈ Sanctions.I, Q.α x = 1 / 5 + awwa₁ e₁ * x) ∧
        (∀ x ∈ Sanctions.I,
          (awParams b hb0 hb1).dynamicEquilibriumRule Q x = awwe₀ e₁ + e₁ * x) ∧
        (∀ x ∈ Sanctions.I, 0 < Q.α x ∧ Q.α x < 1) ∧
        (∀ x ∈ Sanctions.I, 0 < (awParams b hb0 hb1).dynamicEquilibriumRule Q x ∧
          (awParams b hb0 hb1).dynamicEquilibriumRule Q x < 1)) ∧
      (∃ Q : (awParams b hb0 hb1).FeedbackStackelbergEquilibriumTop,
        (∀ x ∈ Sanctions.I, Q.α x = 1 / 5 + awwa₁ (-e₁) * x) ∧
        (∀ x ∈ Sanctions.I,
          (awParams b hb0 hb1).dynamicEquilibriumRule Q x = awwe₀ (-e₁) + -e₁ * x) ∧
        (∀ x ∈ Sanctions.I, 0 < Q.α x ∧ Q.α x < 1) ∧
        (∀ x ∈ Sanctions.I, 0 < (awParams b hb0 hb1).dynamicEquilibriumRule Q x ∧
          (awParams b hb0 hb1).dynamicEquilibriumRule Q x < 1)) := by
  obtain ⟨hbR, hbD⟩ := hb
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  have hs1 : 707 / 500 < Real.sqrt 2 := by nlinarith
  have hb48 : 197 * b < 48 := by
    have : (82 - 7 * Real.sqrt 2) / 394 < 48 / 197 := by
      rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    linarith
  have hbtop : b ≤ 73260 / 400304 := by
    have : (82 - 7 * Real.sqrt 2) / 394 ≤ 73260 / 400304 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    linarith
  set R := (1379 * b - 252) / (48 - 197 * b) with hRdef
  have hden : (0 : ℝ) < 48 - 197 * b := by linarith
  have hnum : (0 : ℝ) < 1379 * b - 252 := by
    have := mul_lt_mul_of_pos_left hbR (show (0 : ℝ) < 1379 by norm_num)
    linarith
  have hR0 : 0 < R := div_pos hnum hden
  have hRmul : R * (48 - 197 * b) = 1379 * b - 252 := div_mul_cancel₀ _ hden.ne'
  have hR9 : R ≤ 9 / 289 := by
    rw [hRdef, div_le_iff₀ hden]; nlinarith
  obtain ⟨e, he0, hele, hbe⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ 3 / 17 ∧ b = awwb e := by
    refine ⟨Real.sqrt R, Real.sqrt_pos.mpr hR0, ?_, ?_⟩
    · rw [show (3 / 17 : ℝ) = Real.sqrt ((3 / 17) ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num; linarith)
    · have he2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0.le
      unfold awwb
      rw [eq_div_iff (by positivity), he2]
      linear_combination -hRmul
  have he : |e| ≤ 3 / 17 := abs_le.mpr ⟨by linarith, hele⟩
  have he' : |-e| ≤ 3 / 17 := by rw [abs_neg]; exact he
  have hbe' : b = awwb (-e) := by rw [awwb_neg]; exact hbe
  have hlt : awwa₁ e < awwa₁ (-e) := by
    unfold awwa₁
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg e]
  obtain ⟨p1, p2, p3, p4⟩ := aww_family e he hb0 hb1 hbe
  obtain ⟨q1, q2, q3, q4⟩ := aww_family (-e) he' hb0 hb1 hbe'
  exact ⟨e, he0, hele, hbe, hlt, ⟨_, p1, p2, p3, p4⟩, ⟨_, q1, q2, q3, q4⟩⟩

/-- **Equilibria with interior compliance exist on the whole window.** At the affine-window
member, for every Target discount `b` strictly between `β_R = 36/197` and
`β_D = (82 − 7√2)/394`, the slope `e₁ ∈ (0, 3/17]` with `b = 12(4e₁² + 21)/(197(e₁² + 7))` gives
two equilibria, one in each family: policies `1/5 + a₁(±e₁)·x` (distinct, since
`a₁(e₁) < a₁(−e₁)`) and realised sanctions `e₀(±e₁) ± e₁·x`, with compliance and sanctions
interior at every state. So neither is relief nor full defiance.

Scope: at the example economy only (not general). -/
theorem aw_exists_on_window (b : ℝ)
    (hb : b ∈ Ioo (36 / 197 : ℝ) ((82 - 7 * Real.sqrt 2) / 394)) :
    ∃ e₁ : ℝ, 0 < e₁ ∧ e₁ ≤ 3 / 17 ∧ b = 12 * (4 * e₁ ^ 2 + 21) / (197 * (e₁ ^ 2 + 7)) ∧
      awwa₁ e₁ < awwa₁ (-e₁) ∧
      (∃ Q : (awParams b (hb0_of_window hb) (hb1_of_window hb)).FeedbackStackelbergEquilibriumTop,
        (∀ x ∈ Sanctions.I, Q.α x = 1 / 5 + awwa₁ e₁ * x) ∧
        (∀ x ∈ Sanctions.I,
          (awParams b (hb0_of_window hb) (hb1_of_window hb)).dynamicEquilibriumRule Q x
            = awwe₀ e₁ + e₁ * x) ∧
        (∀ x ∈ Sanctions.I, 0 < Q.α x ∧ Q.α x < 1) ∧
        (∀ x ∈ Sanctions.I,
          0 < (awParams b (hb0_of_window hb) (hb1_of_window hb)).dynamicEquilibriumRule Q x ∧
          (awParams b (hb0_of_window hb) (hb1_of_window hb)).dynamicEquilibriumRule Q x < 1)) ∧
      (∃ Q : (awParams b (hb0_of_window hb) (hb1_of_window hb)).FeedbackStackelbergEquilibriumTop,
        (∀ x ∈ Sanctions.I, Q.α x = 1 / 5 + awwa₁ (-e₁) * x) ∧
        (∀ x ∈ Sanctions.I,
          (awParams b (hb0_of_window hb) (hb1_of_window hb)).dynamicEquilibriumRule Q x
            = awwe₀ (-e₁) + -e₁ * x) ∧
        (∀ x ∈ Sanctions.I, 0 < Q.α x ∧ Q.α x < 1) ∧
        (∀ x ∈ Sanctions.I,
          0 < (awParams b (hb0_of_window hb) (hb1_of_window hb)).dynamicEquilibriumRule Q x ∧
          (awParams b (hb0_of_window hb) (hb1_of_window hb)).dynamicEquilibriumRule Q x < 1)) :=
  aw_exists_on_window_core b (hb0_of_window hb) (hb1_of_window hb) hb

end

end AWWhole
end Examples
end Sanctions
