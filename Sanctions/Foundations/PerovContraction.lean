/-
Sanctions/Foundations/PerovContraction.lean

**Perov's contraction principle (2×2 case) for joint Banach iteration.**

Following Toda 2021 ORL (*Operations Research Letters* **49**(5), 815-819).
Perov's contraction principle generalises the scalar Banach contraction
constant `β < 1` to a **spectral radius condition `ρ(B) < 1`** on a
non-negative matrix `B`, working over a vector-valued metric.

For the 2-coordinate case relevant to our joint Target-Sender Bellman pair,
this reduces to clean 2×2 linear algebra. The spectral radius of the
non-negative matrix

  `M = ((β_T, L_TS), (L_ST, β_{S,row}))`

is, by Perron-Frobenius for 2×2 non-negative matrices,

  `ρ(M) = (a + d + √((a−d)² + 4 b c)) / 2`

where `a = β_T, b = L_TS, c = L_ST, d = β_{S,row}`. Under
`β_T, β_{S,row} ∈ [0, 1)` (automatic from `Params` / Schur-margin construction),
the condition `ρ(M) < 1` is *equivalent* to the **Schur determinant
condition**

  `L_TS · L_ST < (1 − β_T) · (1 − β_{S,row})`.

The fixed-point engine below needs only the second diagonal bound
`β_{S,row} < 1` next to the Schur margin: with nonnegative cross entries the
first bound `β_T < 1` follows (`lt_one_of_schur_margin`, 2026-10-06 round BG1.1).

The Perov framing is **strictly weaker** than the legacy row-sum form
(`β_T + L_TS < 1` AND `β_S + L_ST < 1`), which only requires each row to
contract individually but is sufficient — not necessary — for spectral
contraction of the joint operator.

## Why it matters

The strictly-weaker route is realized in the tree: at the coupled
low-`δ` economy the exact rational row matrix has both cross constants
strictly positive, its Schur margin holds (`coupledSchur_margin_robust`,
`Examples/CoupledRoute/CoupledSchurWitness.lean`) while the Target row sum fails
(`coupled_rowSum_fails`, `β_T + L_TS = 61499/54110 > 1`) — so the Perov
framing admits a contraction matrix the row-sum framing provably
rejects. (The coupled *equilibrium* application remains conditional:
its leader strong-concavity premise is refuted at modulus 2.) The
row-sum ⇒ Schur direction (`schurDet_of_rowSums`) conversely lets every
legacy row-sum certificate reuse the Schur machinery
(`StandardComplianceLocalCoreCertificateSchur.ofRowSum`).

## Literature anchors

* **Toda 2021 ORL** — Perov's Contraction Principle and Dynamic Programming
  with Stochastic Discounting; arXiv:2103.14173.
* **Horn-Johnson 1985** — *Matrix Analysis*, Theorem 8.1.18
  (Perron-Frobenius for 2×2 non-negative matrices).

## Rule compliance

* **Rule 1** ✓ — no strategies; pure real-analysis content.
* **Rule 3** ✓ — no new `Params` fields; structure-level lemmas only.
* **Rule 5** ✓ — fully parametric over `(a, b, c, d)`.
* **Rule 8** ✓ — every introduced object explained in plain English in
  docstrings.
* **Rule 10** ✓ — verified axiom-clean post-build.
* **Rule 19** ✓ — generic real-analysis content with no project-specific
  economic dependencies; lives in `Foundations/`.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic

namespace Sanctions

/-! ## Generic 2×2 Schur metric lemmas

Moved from `Theory/Equilibrium/EpsilonIsolation.lean` §1–§3 in the
2026-07-24 Rule-19 sweep (user-approved): fully generic metric /
seminormed-group results with zero project content, declared at the
`Sanctions` root so every pre-existing fully-qualified name is
unchanged. `fixedPoint_unique_of_schur_rows` is now also the single
point of truth for the uniqueness half of `perov2_existsUnique_fixedPoint`
below (previously re-derived inline via the weighted metric). The
formerly unused hypothesis `_ha_lt : a < 1` was dropped from
`fixedPoint_unique_of_schur_rows` (Rule-13 disclosed; the proof
eliminates the first coordinate through the Schur chain, so only
`d < 1` is consumed). -/

/-- **Enlarged norm bound from ε-closeness** (triangle inequality):
if `‖V₀‖ ≤ M` and `dist V V₀ ≤ ε` then `‖V‖ ≤ M + ε`. -/
theorem norm_le_enlarged_of_dist_le {X : Type*} [SeminormedAddCommGroup X]
    {V V₀ : X} {M ε : ℝ} (h₀ : ‖V₀‖ ≤ M) (hd : dist V V₀ ≤ ε) :
    ‖V‖ ≤ M + ε := by
  have h := norm_sub_norm_le V V₀
  rw [← dist_eq_norm] at h
  linarith

/-- **Enlarged-carrier membership from norm ε-closeness plus a shape
pin.** If the carrier `C` contains every `V` with `‖V‖ ≤ M + ε` that
satisfies the shape pin `V ∈ P` (the carrier *decomposition*), then any
`V` that is ε-close to an anchor `V₀` of norm `≤ M` and carries the
shape pin is a member. The shape hypothesis `V ∈ P` is irreducible: the
sawtooth exhibit shows ε-closeness cannot control slopes (see
`Theory/Equilibrium/EpsilonIsolation.lean`). -/
theorem mem_enlarged_of_dist_le {X : Type*} [SeminormedAddCommGroup X]
    {C P : Set X} {M ε : ℝ}
    (h_decomp : ∀ V : X, ‖V‖ ≤ M + ε → V ∈ P → V ∈ C)
    {V₀ V : X} (h₀ : ‖V₀‖ ≤ M) (hd : dist V V₀ ≤ ε) (hP : V ∈ P) :
    V ∈ C :=
  h_decomp V (norm_le_enlarged_of_dist_le h₀ hd) hP

/-- **Uniqueness of the joint fixed point under the Schur margin.**
Any two fixed points of a 2×2 row-Lipschitz map with second diagonal
entry `< 1` and Schur margin `b·c < (1−a)(1−d)` coincide: the two
row estimates give `(1−a)·dX ≤ b·dY` and `(1−d)·dY ≤ c·dX`; chaining
forces `((1−a)(1−d) − b·c)·dX ≤ 0`, i.e. `dX = 0`, then `dY = 0`.
No completeness, nonemptiness, or `a < 1` is needed. -/
theorem fixedPoint_unique_of_schur_rows
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (T : X × Y → X × Y) {a b c d : ℝ}
    (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c)
    (hX : ∀ z z' : X × Y,
      dist (T z).1 (T z').1 ≤ a * dist z.1 z'.1 + b * dist z.2 z'.2)
    (hY : ∀ z z' : X × Y,
      dist (T z).2 (T z').2 ≤ c * dist z.1 z'.1 + d * dist z.2 z'.2)
    (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d))
    {z w : X × Y} (hz : T z = z) (hw : T w = w) :
    z = w := by
  have h1 : dist z.1 w.1 ≤ a * dist z.1 w.1 + b * dist z.2 w.2 := by
    have h := hX z w; rw [hz, hw] at h; exact h
  have h2 : dist z.2 w.2 ≤ c * dist z.1 w.1 + d * dist z.2 w.2 := by
    have h := hY z w; rw [hz, hw] at h; exact h
  have h3 : (1 - a) * dist z.1 w.1 ≤ b * dist z.2 w.2 := by nlinarith
  have h4 : (1 - d) * dist z.2 w.2 ≤ c * dist z.1 w.1 := by nlinarith
  have hdX : dist z.1 w.1 = 0 := by
    have hchain : (1 - a) * (1 - d) * dist z.1 w.1
        ≤ b * c * dist z.1 w.1 := by nlinarith
    have := dist_nonneg (x := z.1) (y := w.1)
    nlinarith
  have hdY : dist z.2 w.2 = 0 := by
    have := dist_nonneg (x := z.2) (y := w.2)
    nlinarith [h4, hdX]
  exact Prod.ext (dist_eq_zero.mp hdX) (dist_eq_zero.mp hdY)

/-- **Abstract ε-isolation under the Schur margin.** Let `T` be the
joint operator on the (enlarged-)carrier product `↥C_T × ↥C_S`,
row-Lipschitz with matrix `[[β_T, L_TS], [L_ST, β_S]]` obeying the Schur
margin, and let `z` be a fixed point of `T` whose value pair carries the
*exact* norm anchors `‖z.1‖ ≤ M_T`, `‖z.2‖ ≤ M_S`. Suppose the carriers
decompose as norm-ball-∩-shape at the enlarged radii `M_T + ε_T`,
`M_S + ε_S`. Then any value pair `(W_T, W_S)` that is ε-close to the
fixed point in sup-norm, carries the shape pins (irreducible: sawtooth
exhibit), and is Bellman-fixed as a member, IS the fixed point.
F-free: pure metric-space content, so it holds for every transition law.
(2026-10-06, round BG1.1: the never-consumed first diagonal bound
`β_T < 1` was dropped from the signature; only `β_S < 1` and the Schur
margin are used, through `fixedPoint_unique_of_schur_rows`.) -/
theorem epsIsolation_of_schur_rows
    {X : Type*} [NormedAddCommGroup X]
    {C_T C_S : Set X}
    (T : ↥C_T × ↥C_S → ↥C_T × ↥C_S)
    {β_T β_S L_TS L_ST : ℝ}
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ z z' : ↥C_T × ↥C_S,
      dist (T z).1 (T z').1 ≤ β_T * dist z.1 z'.1 + L_TS * dist z.2 z'.2)
    (hT_S : ∀ z z' : ↥C_T × ↥C_S,
      dist (T z).2 (T z').2 ≤ L_ST * dist z.1 z'.1 + β_S * dist z.2 z'.2)
    (hβ_S_lt : β_S < 1)
    (hSchur : L_TS * L_ST < (1 - β_T) * (1 - β_S))
    (z : ↥C_T × ↥C_S) (hz : T z = z)
    {M_T M_S ε_T ε_S : ℝ}
    (hz_T_norm : ‖z.1.val‖ ≤ M_T) (hz_S_norm : ‖z.2.val‖ ≤ M_S)
    {shape_T shape_S : Set X}
    (h_decomp_T : ∀ V : X, ‖V‖ ≤ M_T + ε_T → V ∈ shape_T → V ∈ C_T)
    (h_decomp_S : ∀ V : X, ‖V‖ ≤ M_S + ε_S → V ∈ shape_S → V ∈ C_S)
    {W_T W_S : X}
    (hd_T : dist W_T z.1.val ≤ ε_T) (hd_S : dist W_S z.2.val ≤ ε_S)
    (hsh_T : W_T ∈ shape_T) (hsh_S : W_S ∈ shape_S)
    (hWfix : ∀ (hWT : W_T ∈ C_T) (hWS : W_S ∈ C_S),
      T (⟨W_T, hWT⟩, ⟨W_S, hWS⟩) = (⟨W_T, hWT⟩, ⟨W_S, hWS⟩)) :
    W_T = z.1.val ∧ W_S = z.2.val := by
  have hWT : W_T ∈ C_T := mem_enlarged_of_dist_le h_decomp_T hz_T_norm hd_T hsh_T
  have hWS : W_S ∈ C_S := mem_enlarged_of_dist_le h_decomp_S hz_S_norm hd_S hsh_S
  have huniq := fixedPoint_unique_of_schur_rows T hL_TS_nn hL_ST_nn hT_T hT_S
    hβ_S_lt hSchur (hWfix hWT hWS) hz
  exact ⟨congrArg (fun w : ↥C_T × ↥C_S => w.1.val) huniq,
         congrArg (fun w : ↥C_T × ↥C_S => w.2.val) huniq⟩

namespace Foundations
namespace Perov

/-- **The first diagonal bound follows from the Schur margin (round BG1.1,
2026-10-06).** If both off-diagonal entries are nonnegative, the second
diagonal entry is below one, and the Schur margin `b·c < (1−a)(1−d)` holds,
then the first diagonal entry is below one as well. Reason: `0 ≤ b·c` makes
`(1−a)(1−d)` strictly positive, and `1 − d > 0` then forces `1 − a > 0`.

Plain language: in the joint Target–Sender contraction, once the Sender row's
own discount is below one and the cross-feedback product is smaller than the
product of the two own-discount slacks, the Target row's own discount cannot
reach one. So `a < 1` is a consequence, not an assumption, wherever the signs
`0 ≤ b`, `0 ≤ c` are kept. F-free: pure real arithmetic. -/
theorem lt_one_of_schur_margin
    {a b c d : ℝ}
    (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d)) :
    a < 1 := by
  nlinarith [mul_nonneg hb_nn hc_nn]

/-- **Unbundled Perron-weight extraction (scalar form, 2026-07-24
dedup).** From `0 ≤ b`, `0 ≤ c`, `d < 1` and the Schur margin
`b·c < (1−a)(1−d)`, the explicit weights `c₁ = (1−d)+b`,
`c₂ = (1−a)+c` are positive and strictly shrink both weighted rows.
Single point of truth for the 2×2 Perron-weight algebra: both
`NNMat2.perronWeightsFromSchurDet` (below) and
`AbstractGame.JointMPE.rowSumWeights_of_spectralRadius_lt_one`
(`Theory/Equilibrium/JointMPE.lean`) are one-line wrappers.

2026-10-06 (round BG1.1): the hypothesis `a < 1` was dropped. It is derived
from the signs, `d < 1` and the Schur margin by `lt_one_of_schur_margin`, so
the weights exist under strictly fewer stated assumptions. F-free: pure
2×2 matrix arithmetic. -/
theorem perronWeights_of_schur_scalars
    {a b c d : ℝ}
    (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c)
    (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d)) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      c₁ * a + c₂ * b < c₁ ∧
      c₁ * c + c₂ * d < c₂ := by
  have ha_lt : a < 1 := lt_one_of_schur_margin hb_nn hc_nn hd_lt hSchur
  refine ⟨(1 - d) + b, (1 - a) + c, by linarith, by linarith, ?_, ?_⟩
  · nlinarith [hSchur]
  · nlinarith [hSchur]

/-- A 2×2 non-negative real matrix `((a, b), (c, d))`. Used to encode the
row-Lipschitz constants of a joint Banach iteration on a 2-coordinate
value pair `(V_T, V_S)`. The diagonal entries `(a, d)` are the
own-discount row-contraction margins; the off-diagonal entries `(b, c)`
are the cross-row absorption coefficients. -/
structure NNMat2 where
  /-- Row-1 diagonal entry (e.g. `β_T`). -/
  a : ℝ
  /-- Row-1 off-diagonal entry (e.g. `L_TS`). -/
  b : ℝ
  /-- Row-2 off-diagonal entry (e.g. `L_ST`). -/
  c : ℝ
  /-- Row-2 diagonal entry (e.g. `β_{S,row}`). -/
  d : ℝ
  /-- Non-negativity of the diagonal entry. -/
  ha_nn : 0 ≤ a
  /-- Non-negativity of the upper off-diagonal. -/
  hb_nn : 0 ≤ b
  /-- Non-negativity of the lower off-diagonal. -/
  hc_nn : 0 ≤ c
  /-- Non-negativity of the second diagonal entry. -/
  hd_nn : 0 ≤ d

namespace NNMat2

/-- **Spectral radius of a 2×2 non-negative matrix** via Perron-Frobenius.
For `M = ((a, b), (c, d))` with `a, b, c, d ≥ 0`, the dominant eigenvalue
is the larger root of the characteristic polynomial `λ² − (a+d)λ + (ad − bc)`:

  `ρ(M) = (a + d + √((a−d)² + 4 b c)) / 2`.

Reference: Horn-Johnson 1985 Theorem 8.1.18. -/
noncomputable def specRadius (M : NNMat2) : ℝ :=
  (M.a + M.d + Real.sqrt ((M.a - M.d)^2 + 4 * M.b * M.c)) / 2

/-- **Schur determinant condition** on the matrix `I − M`:
`(1 − a)(1 − d) > b · c`. Equivalent to `det(I − M) > 0` when `a, d < 1`. -/
def schurDet (M : NNMat2) : Prop :=
  M.b * M.c < (1 - M.a) * (1 - M.d)

/-- The argument of the square root in `specRadius` is non-negative. -/
theorem sqrt_arg_nn (M : NNMat2) :
    0 ≤ (M.a - M.d)^2 + 4 * M.b * M.c := by
  have h1 : 0 ≤ (M.a - M.d)^2 := sq_nonneg _
  have h2 : 0 ≤ 4 * M.b * M.c := by
    have := mul_nonneg M.hb_nn M.hc_nn
    linarith
  linarith

/-- The spectral radius is non-negative. -/
theorem specRadius_nn (M : NNMat2) : 0 ≤ M.specRadius := by
  unfold specRadius
  have hsum : 0 ≤ M.a + M.d := by linarith [M.ha_nn, M.hd_nn]
  have hsqrt : 0 ≤ Real.sqrt ((M.a - M.d)^2 + 4 * M.b * M.c) :=
    Real.sqrt_nonneg _
  linarith

/-- **Round 2.0 — central equivalence.** Under non-negative entries with
diagonal entries strictly less than 1, the Perov spectral-radius condition
`ρ(M) < 1` is **equivalent** to the Schur determinant condition
`b · c < (1 − a)(1 − d)`.

This is the Perov characterisation in the 2×2 case; under the natural
Params constraint `β_T, β_{S,row} ∈ [0, 1)`, the spectral-radius and
Schur-determinant conditions are interchangeable. -/
theorem specRadius_lt_one_iff_schurDet (M : NNMat2)
    (ha_lt : M.a < 1) (hd_lt : M.d < 1) :
    M.specRadius < 1 ↔ M.schurDet := by
  unfold specRadius schurDet
  -- Set s := a + d, sq := (a-d)² + 4bc. Goal: (s + √sq)/2 < 1 ↔ bc < (1-a)(1-d).
  have hs_lt : M.a + M.d < 2 := by linarith
  have hsq_nn : 0 ≤ (M.a - M.d)^2 + 4 * M.b * M.c := M.sqrt_arg_nn
  have h_2ms_nn : 0 < 2 - (M.a + M.d) := by linarith
  -- (s + √sq) / 2 < 1 ↔ √sq < 2 - s
  constructor
  · intro hρ
    have h_sqrt_lt : Real.sqrt ((M.a - M.d)^2 + 4 * M.b * M.c) < 2 - (M.a + M.d) := by
      linarith
    -- Square both sides (positive): sq < (2-s)²
    have h_sq_lt : (M.a - M.d)^2 + 4 * M.b * M.c < (2 - (M.a + M.d))^2 := by
      have h1 : Real.sqrt ((M.a - M.d)^2 + 4 * M.b * M.c)
                  ^ 2 = (M.a - M.d)^2 + 4 * M.b * M.c :=
        Real.sq_sqrt hsq_nn
      nlinarith [h_sqrt_lt, Real.sqrt_nonneg ((M.a - M.d)^2 + 4 * M.b * M.c),
                 sq_nonneg (Real.sqrt ((M.a - M.d)^2 + 4 * M.b * M.c) - (2 - (M.a + M.d)))]
    -- Expand: a² - 2ad + d² + 4bc < 4 - 4(a+d) + (a+d)²
    -- Simplifies to bc < (1-a)(1-d)
    nlinarith [h_sq_lt]
  · intro hSchur
    -- bc < (1-a)(1-d) implies √sq < 2 - s
    have h_sq_lt : (M.a - M.d)^2 + 4 * M.b * M.c < (2 - (M.a + M.d))^2 := by
      nlinarith [hSchur]
    have h_2ms_sq_nn : 0 ≤ (2 - (M.a + M.d))^2 := sq_nonneg _
    have h_sqrt_lt : Real.sqrt ((M.a - M.d)^2 + 4 * M.b * M.c) < 2 - (M.a + M.d) := by
      rw [show (2 - (M.a + M.d))^2 = (2 - (M.a + M.d)) * (2 - (M.a + M.d)) by ring] at h_sq_lt
      have h1 : Real.sqrt ((M.a - M.d)^2 + 4 * M.b * M.c)
                  < Real.sqrt ((2 - (M.a + M.d)) * (2 - (M.a + M.d))) := by
        apply Real.sqrt_lt_sqrt hsq_nn
        linarith
      have h2 : Real.sqrt ((2 - (M.a + M.d)) * (2 - (M.a + M.d)))
                  = 2 - (M.a + M.d) := by
        rw [Real.sqrt_mul_self (le_of_lt h_2ms_nn)]
      linarith
    linarith

/-- **Sufficient condition (legacy row-sum form).** The classical row-sum
contraction conditions `a + b < 1` and `c + d < 1` together imply the
Schur determinant condition `b · c < (1 − a)(1 − d)`.

This shows the Perov framing is **weaker** than (or equivalent to) the
row-sum framing: anything that clears the row-sums automatically clears
the spectral-radius / Schur-determinant condition, but the converse can
fail (witness: `b` large, `c` small). -/
theorem schurDet_of_rowSums (M : NNMat2)
    (h_row1 : M.a + M.b < 1) (h_row2 : M.c + M.d < 1) :
    M.schurDet := by
  unfold schurDet
  have h1 : M.b < 1 - M.a := by linarith
  have h2 : M.c < 1 - M.d := by linarith
  have h1a : 0 < 1 - M.a := by linarith [M.hb_nn]
  have h1d : 0 < 1 - M.d := by linarith [M.hc_nn]
  -- 0 ≤ b < 1 - a and 0 ≤ c < 1 - d gives bc < (1-a)(1-d)
  calc M.b * M.c
      ≤ (1 - M.a) * M.c := by
        exact mul_le_mul_of_nonneg_right (le_of_lt h1) M.hc_nn
    _ < (1 - M.a) * (1 - M.d) := by
        exact mul_lt_mul_of_pos_left h2 h1a

/-- **Composite: row-sum implies spectral radius < 1.** Under the natural
constraints `a, d ∈ [0, 1)`, the legacy row-sum conditions imply the
Perov spectral-radius bound. -/
theorem specRadius_lt_one_of_rowSums (M : NNMat2)
    (h_row1 : M.a + M.b < 1) (h_row2 : M.c + M.d < 1) :
    M.specRadius < 1 := by
  have ha_lt : M.a < 1 := by linarith [M.hb_nn]
  have hd_lt : M.d < 1 := by linarith [M.hc_nn]
  rw [M.specRadius_lt_one_iff_schurDet ha_lt hd_lt]
  exact M.schurDet_of_rowSums h_row1 h_row2

/-- **Round 2.1 — Perron weight extraction from the Schur determinant
condition.** Given a 2×2 non-negative matrix `M = ((a, b), (c, d))` with
second diagonal entry `d < 1` and Schur determinant condition
`b · c < (1−a)(1−d)` (the first diagonal bound `a < 1` follows from these and
was dropped as a hypothesis on 2026-10-06, round BG1.1; see
`lt_one_of_schur_margin`),
this exhibits explicit positive weights `(c_1, c_2)` such that the
**weighted row sums** strictly contract:

  `c_1 · a + c_2 · b < c_1`   AND   `c_1 · c + c_2 · d < c_2`.

The closed-form weights are
  `c_1 := (1 − d) + b`,
  `c_2 := (1 − a) + c`.

Algebraic identity: substituting back,
  `c_1 · a + c_2 · b − c_1 = b · c − (1 − a)(1 − d) < 0`
  `c_1 · c + c_2 · d − c_2 = b · c − (1 − a)(1 − d) < 0`
both follow from the Schur determinant condition by direct expansion.

One-line wrapper of the unbundled scalar lemma
`perronWeights_of_schur_scalars` (the 2026-07-24 dedup single point of
truth; `AbstractGame.JointMPE.rowSumWeights_of_spectralRadius_lt_one`
is the other wrapper). F-free: pure 2×2 matrix arithmetic. -/
theorem perronWeightsFromSchurDet (M : NNMat2)
    (hd_lt : M.d < 1) (hSchur : M.schurDet) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      c₁ * M.a + c₂ * M.b < c₁ ∧
      c₁ * M.c + c₂ * M.d < c₂ :=
  perronWeights_of_schur_scalars M.hb_nn M.hc_nn hd_lt hSchur

end NNMat2

/-! ## Perov two-coordinate fixed point from the Schur margin (Round E1)

The weighted-sup-norm reduction: a pair of row-Lipschitz estimates
with nonnegative coefficient matrix `M = ((a,b),(c,d))` satisfying `d < 1` and
the Schur condition `b·c < (1−a)(1−d)` (which together give `a < 1`,
`lt_one_of_schur_margin`) admits **explicit positive
weights** (from `NNMat2.perronWeightsFromSchurDet`) under which the
map is a single-modulus contraction in the weighted max metric
`w(z,z') = max(ξ_X·dist z.1 z'.1, ξ_Y·dist z.2 z'.2)`. The fixed
point is produced by an elementary geometric Cauchy iteration in each
coordinate — no custom metric-space instance is needed.

This is the 2×2 case of the Perov contraction principle (Perov 1964;
Toda 2021/2023 §2) and the weighted-max-norm reduction of
Bertsekas-Tsitsiklis (NDP §2). It removes the need for the *row-sum*
conditions `a + b < 1`, `c + d < 1` in heterogeneous two-player
Banach steps: the spectral condition `ρ(M) < 1` (equivalently the
Schur margin, by `specRadius_lt_one_iff_schurDet`) suffices. -/

/-- **Perov 2×2 fixed point.** If `T : X × Y → X × Y` satisfies the
row-Lipschitz estimates with nonnegative matrix `((a,b),(c,d))`, `d < 1`, and
the Schur margin `b·c < (1−a)(1−d)`, then `T` has a unique fixed
point. Existence by weighted geometric iteration; uniqueness because
the weighted distance of two fixed points contracts into itself.

2026-10-06 (round BG1.1): the hypothesis `a < 1` was dropped. With the four
sign conditions kept, it follows from `d < 1` and the Schur margin
(`lt_one_of_schur_margin`), as the uniqueness half already used. Plain
language: the joint Target–Sender operator has exactly one fixed point as
soon as the Sender row contracts on its own and the cross feedback is smaller
than the two own-discount slacks; the Target row's own contraction is then
automatic. The signs are still needed: dropping them together with a diagonal
bound makes the step false. F-free: abstract metric-space content. -/
theorem perov2_existsUnique_fixedPoint
    {X Y : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    [MetricSpace Y] [CompleteSpace Y] [Nonempty Y]
    (T : X × Y → X × Y) {a b c d : ℝ}
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) (hd_nn : 0 ≤ d)
    (hX : ∀ z z' : X × Y,
      dist (T z).1 (T z').1 ≤ a * dist z.1 z'.1 + b * dist z.2 z'.2)
    (hY : ∀ z z' : X × Y,
      dist (T z).2 (T z').2 ≤ c * dist z.1 z'.1 + d * dist z.2 z'.2)
    (hd_lt : d < 1)
    (hSchur : b * c < (1 - a) * (1 - d)) :
    ∃! z : X × Y, T z = z := by
  -- Perron weights from the Schur margin.
  obtain ⟨c₁, c₂, hc₁, hc₂, hrow1, hrow2⟩ :=
    NNMat2.perronWeightsFromSchurDet ⟨a, b, c, d, ha_nn, hb_nn, hc_nn, hd_nn⟩
      hd_lt hSchur
  -- Weighted max metric and the contraction modulus.
  set w : X × Y → X × Y → ℝ :=
    fun z z' => max (c₂ * dist z.1 z'.1) (c₁ * dist z.2 z'.2) with hw_def
  set β : ℝ := max ((c₁ * a + c₂ * b) / c₁) ((c₁ * c + c₂ * d) / c₂)
    with hβ_def
  have hβ_nn : 0 ≤ β := le_trans (div_nonneg (by nlinarith) hc₁.le)
    (le_max_left _ _)
  have hβ_lt : β < 1 :=
    max_lt ((div_lt_one hc₁).mpr hrow1) ((div_lt_one hc₂).mpr hrow2)
  have hw_nn : ∀ z z', 0 ≤ w z z' := fun z z' =>
    le_trans (mul_nonneg hc₂.le dist_nonneg) (le_max_left _ _)
  -- One-step weighted contraction.
  have hcontr : ∀ z z', w (T z) (T z') ≤ β * w z z' := by
    intro z z'
    have hdX : c₂ * dist z.1 z'.1 ≤ w z z' := le_max_left _ _
    have hdY : c₁ * dist z.2 z'.2 ≤ w z z' := le_max_right _ _
    have hX' : c₂ * dist (T z).1 (T z').1 ≤
        ((c₁ * a + c₂ * b) / c₁) * w z z' := by
      have h1 : c₂ * dist (T z).1 (T z').1 ≤
          c₂ * (a * dist z.1 z'.1 + b * dist z.2 z'.2) :=
        mul_le_mul_of_nonneg_left (hX z z') hc₂.le
      have h2 : c₂ * (a * dist z.1 z'.1 + b * dist z.2 z'.2)
          = (a / c₁) * (c₂ * c₁ * dist z.1 z'.1)
            + (c₂ * b / c₁) * (c₁ * dist z.2 z'.2) := by
        field_simp
      have h3 : (a / c₁) * (c₂ * c₁ * dist z.1 z'.1)
          ≤ (a / c₁) * (c₁ * w z z') := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg ha_nn hc₁.le)
        calc c₂ * c₁ * dist z.1 z'.1
            = c₁ * (c₂ * dist z.1 z'.1) := by ring
          _ ≤ c₁ * w z z' := mul_le_mul_of_nonneg_left hdX hc₁.le
      have h4 : (c₂ * b / c₁) * (c₁ * dist z.2 z'.2)
          ≤ (c₂ * b / c₁) * (c₁ / c₁ * w z z') := by
        apply mul_le_mul_of_nonneg_left _
          (div_nonneg (mul_nonneg hc₂.le hb_nn) hc₁.le)
        rw [div_self (ne_of_gt hc₁), one_mul]
        exact hdY
      have h5 : (a / c₁) * (c₁ * w z z')
            + (c₂ * b / c₁) * (c₁ / c₁ * w z z')
          = ((c₁ * a + c₂ * b) / c₁) * w z z' := by
        field_simp
      linarith
    have hY' : c₁ * dist (T z).2 (T z').2 ≤
        ((c₁ * c + c₂ * d) / c₂) * w z z' := by
      have h1 : c₁ * dist (T z).2 (T z').2 ≤
          c₁ * (c * dist z.1 z'.1 + d * dist z.2 z'.2) :=
        mul_le_mul_of_nonneg_left (hY z z') hc₁.le
      have h2 : c₁ * (c * dist z.1 z'.1 + d * dist z.2 z'.2)
          = (c₁ * c / c₂) * (c₂ * dist z.1 z'.1)
            + (d / c₂) * (c₂ * c₁ * dist z.2 z'.2) := by
        field_simp
      have h3 : (c₁ * c / c₂) * (c₂ * dist z.1 z'.1)
          ≤ (c₁ * c / c₂) * w z z' := by
        apply mul_le_mul_of_nonneg_left hdX
          (div_nonneg (mul_nonneg hc₁.le hc_nn) hc₂.le)
      have h4 : (d / c₂) * (c₂ * c₁ * dist z.2 z'.2)
          ≤ (d / c₂) * (c₂ * w z z') := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hd_nn hc₂.le)
        calc c₂ * c₁ * dist z.2 z'.2
            = c₂ * (c₁ * dist z.2 z'.2) := by ring
          _ ≤ c₂ * w z z' := mul_le_mul_of_nonneg_left hdY hc₂.le
      have h5 : (c₁ * c / c₂) * w z z' + (d / c₂) * (c₂ * w z z')
          = ((c₁ * c + c₂ * d) / c₂) * w z z' := by
        field_simp
      linarith
    have hβX : ((c₁ * a + c₂ * b) / c₁) * w z z' ≤ β * w z z' :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (hw_nn z z')
    have hβY : ((c₁ * c + c₂ * d) / c₂) * w z z' ≤ β * w z z' :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (hw_nn z z')
    exact max_le (le_trans hX' hβX) (le_trans hY' hβY)
  -- Geometric iteration from an arbitrary seed.
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  set z : ℕ → X × Y := fun n => T^[n] (x₀, y₀) with hz_def
  have hz_succ : ∀ n, z (n + 1) = T (z n) := by
    intro n
    simp only [hz_def, Function.iterate_succ_apply']
  have hgeom : ∀ n, w (z n) (z (n + 1)) ≤ β ^ n * w (z 0) (z 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : w (z (n + 1)) (z (n + 2)) ≤ β * w (z n) (z (n + 1)) := by
        have h := hcontr (z n) (z (n + 1))
        rw [← hz_succ n, ← hz_succ (n + 1)] at h
        exact h
      calc w (z (n + 1)) (z (n + 2))
          ≤ β * w (z n) (z (n + 1)) := hstep
        _ ≤ β * (β ^ n * w (z 0) (z 1)) :=
            mul_le_mul_of_nonneg_left ih hβ_nn
        _ = β ^ (n + 1) * w (z 0) (z 1) := by ring
  -- Coordinatewise Cauchy sequences.
  have hcauchy1 : CauchySeq (fun n => (z n).1) := by
    apply cauchySeq_of_le_geometric β (w (z 0) (z 1) / c₂) hβ_lt
    intro n
    have hco : c₂ * dist (z n).1 (z (n + 1)).1 ≤ β ^ n * w (z 0) (z 1) :=
      le_trans (le_max_left _ _) (hgeom n)
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₂]
    have hcomm : dist (z n).1 (z (n + 1)).1 * c₂
        = c₂ * dist (z n).1 (z (n + 1)).1 := mul_comm _ _
    have hcomm' : w (z 0) (z 1) * β ^ n = β ^ n * w (z 0) (z 1) :=
      mul_comm _ _
    linarith
  have hcauchy2 : CauchySeq (fun n => (z n).2) := by
    apply cauchySeq_of_le_geometric β (w (z 0) (z 1) / c₁) hβ_lt
    intro n
    have hco : c₁ * dist (z n).2 (z (n + 1)).2 ≤ β ^ n * w (z 0) (z 1) :=
      le_trans (le_max_right _ _) (hgeom n)
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₁]
    have hcomm : dist (z n).2 (z (n + 1)).2 * c₁
        = c₁ * dist (z n).2 (z (n + 1)).2 := mul_comm _ _
    have hcomm' : w (z 0) (z 1) * β ^ n = β ^ n * w (z 0) (z 1) :=
      mul_comm _ _
    linarith
  obtain ⟨xs, hxs⟩ := cauchySeq_tendsto_of_complete hcauchy1
  obtain ⟨ys, hys⟩ := cauchySeq_tendsto_of_complete hcauchy2
  -- The limit is a fixed point: squeeze each coordinate distance to 0.
  have hd1 : ∀ n, dist (T (xs, ys)).1 xs ≤
      a * dist xs (z n).1 + b * dist ys (z n).2
        + dist (z (n + 1)).1 xs := by
    intro n
    calc dist (T (xs, ys)).1 xs
        ≤ dist (T (xs, ys)).1 (T (z n)).1 + dist (T (z n)).1 xs :=
          dist_triangle _ _ _
      _ ≤ (a * dist xs (z n).1 + b * dist ys (z n).2)
            + dist (T (z n)).1 xs := by
          have := hX (xs, ys) (z n)
          gcongr
      _ = a * dist xs (z n).1 + b * dist ys (z n).2
            + dist (z (n + 1)).1 xs := by rw [hz_succ]
  have hd2 : ∀ n, dist (T (xs, ys)).2 ys ≤
      c * dist xs (z n).1 + d * dist ys (z n).2
        + dist (z (n + 1)).2 ys := by
    intro n
    calc dist (T (xs, ys)).2 ys
        ≤ dist (T (xs, ys)).2 (T (z n)).2 + dist (T (z n)).2 ys :=
          dist_triangle _ _ _
      _ ≤ (c * dist xs (z n).1 + d * dist ys (z n).2)
            + dist (T (z n)).2 ys := by
          have := hY (xs, ys) (z n)
          gcongr
      _ = c * dist xs (z n).1 + d * dist ys (z n).2
            + dist (z (n + 1)).2 ys := by rw [hz_succ]
  have htend1 : Filter.Tendsto (fun n => dist xs (z n).1)
      Filter.atTop (nhds 0) := by
    have := (tendsto_iff_dist_tendsto_zero).mp hxs
    simpa [dist_comm] using this
  have htend2 : Filter.Tendsto (fun n => dist ys (z n).2)
      Filter.atTop (nhds 0) := by
    have := (tendsto_iff_dist_tendsto_zero).mp hys
    simpa [dist_comm] using this
  have htend1' : Filter.Tendsto (fun n => dist (z (n + 1)).1 xs)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_iff_dist_tendsto_zero).mp hxs
    exact (h.comp (Filter.tendsto_add_atTop_nat 1))
  have htend2' : Filter.Tendsto (fun n => dist (z (n + 1)).2 ys)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_iff_dist_tendsto_zero).mp hys
    exact (h.comp (Filter.tendsto_add_atTop_nat 1))
  have hfix1 : dist (T (xs, ys)).1 xs = 0 := by
    have hbound : Filter.Tendsto
        (fun n => a * dist xs (z n).1 + b * dist ys (z n).2
          + dist (z (n + 1)).1 xs) Filter.atTop (nhds 0) := by
      have := ((htend1.const_mul a).add (htend2.const_mul b)).add htend1'
      simpa using this
    have hle : dist (T (xs, ys)).1 xs ≤ 0 :=
      ge_of_tendsto hbound (Filter.Eventually.of_forall hd1)
    exact le_antisymm hle dist_nonneg
  have hfix2 : dist (T (xs, ys)).2 ys = 0 := by
    have hbound : Filter.Tendsto
        (fun n => c * dist xs (z n).1 + d * dist ys (z n).2
          + dist (z (n + 1)).2 ys) Filter.atTop (nhds 0) := by
      have := ((htend1.const_mul c).add (htend2.const_mul d)).add htend2'
      simpa using this
    have hle : dist (T (xs, ys)).2 ys ≤ 0 :=
      ge_of_tendsto hbound (Filter.Eventually.of_forall hd2)
    exact le_antisymm hle dist_nonneg
  refine ⟨(xs, ys), ?_, ?_⟩
  · have h1 : (T (xs, ys)).1 = xs := by
      rwa [dist_eq_zero] at hfix1
    have h2 : (T (xs, ys)).2 = ys := by
      rwa [dist_eq_zero] at hfix2
    exact Prod.ext h1 h2
  · -- Uniqueness: two Schur fixed points coincide (generic lemma —
    -- 2026-07-24 dedup; previously re-derived inline via the weighted
    -- metric).
    intro z' hz'
    have hfix : T (xs, ys) = (xs, ys) := by
      have h1 : (T (xs, ys)).1 = xs := by rwa [dist_eq_zero] at hfix1
      have h2 : (T (xs, ys)).2 = ys := by rwa [dist_eq_zero] at hfix2
      exact Prod.ext h1 h2
    exact fixedPoint_unique_of_schur_rows T hb_nn hc_nn hX hY hd_lt
      hSchur hz' hfix

end Perov
end Foundations
end Sanctions
