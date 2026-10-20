/-
Sanctions/Theory/Bellman/ValueClassC1.lean

**iter 17: C¹ value class structure with parametric Bellman operator.**

**PARTIALLY UNFROZEN (2026-07-12; supersedes the 2026-07-04 A6 freeze
for the witness layer only).** The *witness* layer now carries
paper-facing load: `Examples/C1WitnessEnvelope.lean` inhabits `C1Val`,
`ValueClass_C1`, `ValueClass_C1Complete` and `C1BellmanSystem` at the
two pinned exact Bellman fixed points (eeCert, fourGroup), and the
paper's shadow-price passage cites the resulting equilibrium slopes.
At those witnesses the completeness field is *proved*
(`eeC1Class_complete` / `fgcC1Class_complete` — a singleton carrier is
trivially complete) and `T = id`, so the `c1distPair`-fixed point is a
genuine fixed point: no assumed-completeness postulate and no
pseudo-metric artefact enters any shipped result. No headline row
fences the C¹ layer.

The *abstract* layer STAYS FROZEN: each general form (the
`SmoothSanctionClass` IFT Prop fields, an abstract
`ValueClass_C1Complete` derivation, general-`F` RZS-style statements)
would need new differentiability hypotheses (Rule 3). Both structural
deficiencies persist at abstract generality: `c1distPair` is a
pseudo-metric (`V'` stored on all of `ℝ`), and completeness
(`ValueClass_C1Complete`) is consumed per-certificate, not derived. Revival order if ever needed: (1) the within-set
uniform-limits-of-derivatives theorem (a mathlib gap, not an analytic
one — `Foundations/` candidate), (2) the `V'`-domain refactor,
(3) asymmetric duplication only once a consumer exists.

The C¹ analog of `Sanctions/Theory/Bellman/InvariantValueClass.lean`:
a closed nonempty carrier of `C1Val K_d × C1Val K_d` pairs together
with a parametric *joint* Bellman operator `T : carrier → carrier` and
a Lipschitz constant witnessing that `T` is a `q`-contraction in the
combined C¹ pair-distance.

## Architectural role

The BCF `ValueClass` (in `InvariantValueClass.lean`) packages:

* `carrier : Set Val` — closed nonempty subset of the BCF space.
* `sender_unique_on`, `target_unique_on` — uniqueness primitives.
* `IsInvariant` — Prop: joint Bellman operators preserve `carrier`.

For C¹, the parallel structure is:

* `carrier : Set (C1Val K_d × C1Val K_d)` — closed nonempty subset.
* `T : carrier → carrier` — parametric C¹ joint Bellman operator
  (envelope-theorem-style differentiation of the BCF Bellman; the
  construction is genuinely non-trivial at concrete payoff classes,
  so we take `T` as a structure field rather than building it from
  primitives — exactly the audit's "abstract heavy" track structure).
* `T_contracts` — witness that `T` is a `q`-contraction in the
  combined C¹ pair-distance `c1distPair`.

This structure is exactly the input to the Banach fixed-point
existence theorem (iter 18). The construction of `T` at concrete
payoff classes is the substantive economic content that lives at
the concrete-instantiation layer (out of scope for the abstract
formalization, but framed by this structure for direct downstream
consumption).

## Rule compliance

**Rule 1.** The fixed point produced by Banach iteration is the
unique limit of `T^n x₀` — equilibrium-derived, not hand-chosen.

**Rule 3.** `ValueClass_C1` is a structure (taken as a parametric
input to downstream theorems), not a `Params` field. The Banach
contraction primitive `T_contracts` is the canonical
fixed-point-existence input. No new BCF assumptions.

**Rule 5.** Fully parametric over `(K_d, q)` and the carrier.
-/

import Sanctions.Theory.Bellman.C1Val

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace C1Val

/-! ## Combined C¹ pair distance -/

/-- **Combined C¹ pair distance** on `C1Val K_d × C1Val K_d`. Sum of
the two component C¹ distances. -/
noncomputable def c1distPair {K_d : ℝ}
    (a b : C1Val K_d × C1Val K_d) : ℝ :=
  C1Val.c1dist a.1 b.1 + C1Val.c1dist a.2 b.2

/-- Combined distance is non-negative when `K_d ≥ 0`. -/
theorem c1distPair_nonneg {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    (a b : C1Val K_d × C1Val K_d) : 0 ≤ c1distPair a b :=
  add_nonneg (C1Val.c1dist_nonneg hK_d_nn a.1 b.1)
             (C1Val.c1dist_nonneg hK_d_nn a.2 b.2)

/-- Combined distance is symmetric. -/
theorem c1distPair_comm {K_d : ℝ} (a b : C1Val K_d × C1Val K_d) :
    c1distPair a b = c1distPair b a := by
  unfold c1distPair
  rw [C1Val.c1dist_comm a.1 b.1, C1Val.c1dist_comm a.2 b.2]

/-- Combined distance is zero at the diagonal. -/
theorem c1distPair_self {K_d : ℝ} (a : C1Val K_d × C1Val K_d) :
    c1distPair a a = 0 := by
  unfold c1distPair
  rw [C1Val.c1dist_self a.1, C1Val.c1dist_self a.2]; ring

/-- Combined-distance triangle inequality, from component triangles. -/
theorem c1distPair_triangle {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    (a b c : C1Val K_d × C1Val K_d) :
    c1distPair a c ≤ c1distPair a b + c1distPair b c := by
  unfold c1distPair
  have h1 := C1Val.c1dist_triangle hK_d_nn a.1 b.1 c.1
  have h2 := C1Val.c1dist_triangle hK_d_nn a.2 b.2 c.2
  linarith

end C1Val

/-! ## `ValueClass_C1` structure -/

namespace AbstractGame

/-- **C¹ value class.** Closed nonempty carrier of `C1Val K_d ×
C1Val K_d` pairs together with a parametric joint Bellman operator
`T : carrier → carrier` that is a `q`-contraction in the combined
C¹ pair-distance.

The construction of `T` at a concrete payoff class is the substantive
economic step (envelope-theorem-style differentiation of the BCF
Bellman through the smoothness of the value functions); the abstract
layer here packages the required interface for downstream theorems. -/
structure ValueClass_C1 (K_d : ℝ) where
  /-- The C¹ value-pair carrier. -/
  carrier : Set (C1Val K_d × C1Val K_d)
  /-- Carrier is nonempty (must contain at least one C¹ value pair). -/
  isNonempty : carrier.Nonempty
  /-- Parametric C¹ joint Bellman operator preserving the carrier. -/
  T : carrier → carrier
  /-- Contraction constant. -/
  q : ℝ
  /-- `q ∈ [0, 1)`: contraction modulus. -/
  q_nn : 0 ≤ q
  q_lt_one : q < 1
  /-- `T` is a `q`-contraction in the combined C¹ pair-distance
  `c1distPair` on the carrier subtype. -/
  T_contracts : ∀ a b : carrier,
    C1Val.c1distPair (T a).val (T b).val
      ≤ q * C1Val.c1distPair a.val b.val

namespace ValueClass_C1

/-- The carrier subtype (typeclass-friendly `↥`). -/
abbrev Carrier {K_d : ℝ} (D : ValueClass_C1 K_d) : Type :=
  D.carrier

end ValueClass_C1

/-! ## iter 18: Banach iteration on `ValueClass_C1` carrier is Cauchy

Mirrors iter 15 (`banachIter_isC1Cauchy`) for the *pair-carrier* of a
`ValueClass_C1`, using the contraction T : carrier → carrier provided
by the structure. The iteration produces a sequence in `D.Carrier`
that is Cauchy w.r.t. `c1distPair`.

This is the C¹-track Banach fixed-point input. At a concrete payoff
class, completing the proof to "limit ∈ carrier" requires
carrier-closedness in the c1distPair topology, which is handled at
the instantiation layer (not abstract). -/

/-- **C¹ Banach iteration on the pair carrier.** Applying T : carrier
→ carrier produces a sequence in the C¹ carrier. -/
noncomputable def ValueClass_C1.iter {K_d : ℝ} (D : ValueClass_C1 K_d)
    (x₀ : D.Carrier) : ℕ → D.Carrier
  | 0 => x₀
  | n + 1 => D.T (D.iter x₀ n)

@[simp] theorem ValueClass_C1.iter_zero {K_d : ℝ} (D : ValueClass_C1 K_d)
    (x₀ : D.Carrier) : D.iter x₀ 0 = x₀ := rfl

@[simp] theorem ValueClass_C1.iter_succ {K_d : ℝ} (D : ValueClass_C1 K_d)
    (x₀ : D.Carrier) (n : ℕ) : D.iter x₀ (n + 1) = D.T (D.iter x₀ n) := rfl

/-- **Geometric step bound** for the C¹ pair iteration. -/
theorem ValueClass_C1.iter_step_dist {K_d : ℝ} (D : ValueClass_C1 K_d)
    (x₀ : D.Carrier) (n : ℕ) :
    C1Val.c1distPair (D.iter x₀ n).val (D.iter x₀ (n + 1)).val
      ≤ D.q^n * C1Val.c1distPair x₀.val (D.T x₀).val := by
  induction n with
  | zero =>
    simp [ValueClass_C1.iter]
  | succ n ih =>
    have h_contract := D.T_contracts (D.iter x₀ n) (D.iter x₀ (n + 1))
    have h_pow_nn : 0 ≤ D.q^n := pow_nonneg D.q_nn n
    calc C1Val.c1distPair (D.iter x₀ (n + 1)).val (D.iter x₀ (n + 2)).val
        = C1Val.c1distPair (D.T (D.iter x₀ n)).val (D.T (D.iter x₀ (n + 1))).val := rfl
      _ ≤ D.q * C1Val.c1distPair (D.iter x₀ n).val (D.iter x₀ (n + 1)).val :=
          h_contract
      _ ≤ D.q * (D.q^n * C1Val.c1distPair x₀.val (D.T x₀).val) :=
          mul_le_mul_of_nonneg_left ih D.q_nn
      _ = D.q^(n + 1) * C1Val.c1distPair x₀.val (D.T x₀).val := by ring

/-- **Tight geometric series bound** (telescoping triangle through
intermediate iterates). Proof parallels `banachIter_dist_le_tight`. -/
theorem ValueClass_C1.iter_dist_le_tight {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    (D : ValueClass_C1 K_d) (x₀ : D.Carrier) :
    ∀ p k : ℕ,
      C1Val.c1distPair (D.iter x₀ p).val (D.iter x₀ (p + k)).val
        ≤ D.q^p * C1Val.c1distPair x₀.val (D.T x₀).val
            * (1 - D.q^k) / (1 - D.q) := by
  have hq_nn := D.q_nn
  have hq_lt := D.q_lt_one
  have h1mq_pos : 0 < 1 - D.q := by linarith
  intro p k
  induction k with
  | zero =>
    have h_self :
        C1Val.c1distPair (D.iter x₀ p).val (D.iter x₀ (p + 0)).val = 0 := by
      rw [Nat.add_zero, C1Val.c1distPair_self]
    rw [h_self]; simp
  | succ k ih =>
    have h_eq : p + (k + 1) = (p + k) + 1 := by ring
    have h_tri := C1Val.c1distPair_triangle hK_d_nn
      (D.iter x₀ p).val (D.iter x₀ (p + k)).val (D.iter x₀ (p + (k + 1))).val
    have h_step := D.iter_step_dist x₀ (p + k)
    have h_step_dist :
        C1Val.c1distPair (D.iter x₀ (p + k)).val (D.iter x₀ (p + (k + 1))).val
          ≤ D.q^(p + k) * C1Val.c1distPair x₀.val (D.T x₀).val := by
      rw [h_eq]; exact h_step
    have h_pow_split : D.q^(p + k) = D.q^p * D.q^k := by rw [pow_add]
    calc C1Val.c1distPair (D.iter x₀ p).val (D.iter x₀ (p + (k + 1))).val
        ≤ C1Val.c1distPair (D.iter x₀ p).val (D.iter x₀ (p + k)).val
          + C1Val.c1distPair (D.iter x₀ (p + k)).val
              (D.iter x₀ (p + (k + 1))).val := h_tri
      _ ≤ D.q^p * C1Val.c1distPair x₀.val (D.T x₀).val * (1 - D.q^k) / (1 - D.q)
          + D.q^(p + k) * C1Val.c1distPair x₀.val (D.T x₀).val :=
          add_le_add ih h_step_dist
      _ = D.q^p * C1Val.c1distPair x₀.val (D.T x₀).val
            * (1 - D.q^(k + 1)) / (1 - D.q) := by
          rw [h_pow_split, pow_succ]
          field_simp
          ring

/-- **Loose geometric series bound** (drop `(1 - q^k)`). -/
theorem ValueClass_C1.iter_dist_le {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    (D : ValueClass_C1 K_d) (x₀ : D.Carrier) (p k : ℕ) :
    C1Val.c1distPair (D.iter x₀ p).val (D.iter x₀ (p + k)).val
      ≤ D.q^p * C1Val.c1distPair x₀.val (D.T x₀).val / (1 - D.q) := by
  have hq_nn := D.q_nn
  have hq_lt := D.q_lt_one
  have h1mq_pos : 0 < 1 - D.q := by linarith
  have h1mq_nn : 0 ≤ 1 - D.q := le_of_lt h1mq_pos
  have hD_nn : 0 ≤ C1Val.c1distPair x₀.val (D.T x₀).val :=
    C1Val.c1distPair_nonneg hK_d_nn x₀.val (D.T x₀).val
  have h_pow_p_nn : 0 ≤ D.q^p := pow_nonneg hq_nn p
  have h_pow_k_nn : 0 ≤ D.q^k := pow_nonneg hq_nn k
  have h_tight := D.iter_dist_le_tight hK_d_nn x₀ p k
  have h_factor : (1 - D.q^k) ≤ 1 := by linarith
  have h_coef_nn : 0 ≤ D.q^p * C1Val.c1distPair x₀.val (D.T x₀).val :=
    mul_nonneg h_pow_p_nn hD_nn
  have h_prod_le :
      D.q^p * C1Val.c1distPair x₀.val (D.T x₀).val * (1 - D.q^k)
        ≤ D.q^p * C1Val.c1distPair x₀.val (D.T x₀).val := by
    have := mul_le_mul_of_nonneg_left h_factor h_coef_nn
    simpa using this
  have h_rhs_le :
      D.q^p * C1Val.c1distPair x₀.val (D.T x₀).val * (1 - D.q^k) / (1 - D.q)
        ≤ D.q^p * C1Val.c1distPair x₀.val (D.T x₀).val / (1 - D.q) :=
    div_le_div_of_nonneg_right h_prod_le h1mq_nn
  linarith [h_tight]

/-- **Symmetric form** covering both `m ≤ n` and `n ≤ m`. -/
theorem ValueClass_C1.iter_dist_le_symm {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    (D : ValueClass_C1 K_d) (x₀ : D.Carrier) (m n : ℕ) :
    C1Val.c1distPair (D.iter x₀ m).val (D.iter x₀ n).val
      ≤ D.q^(min m n) * C1Val.c1distPair x₀.val (D.T x₀).val / (1 - D.q) := by
  rcases le_total m n with h_mn | h_nm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h_mn
    have h_min : min m (m + k) = m := by omega
    rw [h_min]
    exact D.iter_dist_le hK_d_nn x₀ m k
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h_nm
    have h_min : min (n + k) n = n := by omega
    rw [h_min, C1Val.c1distPair_comm]
    exact D.iter_dist_le hK_d_nn x₀ n k

/-- **`IsC1Cauchy_pair`** predicate: the pair-level analog of
`IsC1Cauchy` using `c1distPair`. -/
def IsC1CauchyPair {K_d : ℝ} (s : ℕ → C1Val K_d × C1Val K_d) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    C1Val.c1distPair (s m) (s n) < ε

/-- **C¹ Banach iteration on `ValueClass_C1` is Cauchy.** Standard
argument: pick `N` so that `q^N · D / (1 - q) < ε`. -/
theorem ValueClass_C1.iter_isC1CauchyPair {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    (D : ValueClass_C1 K_d) (x₀ : D.Carrier) :
    IsC1CauchyPair (fun n => (D.iter x₀ n).val) := by
  intro ε hε
  have hq_nn := D.q_nn
  have hq_lt := D.q_lt_one
  have h1mq_pos : 0 < 1 - D.q := by linarith
  have h1mq_nn : 0 ≤ 1 - D.q := le_of_lt h1mq_pos
  set Dist : ℝ := C1Val.c1distPair x₀.val (D.T x₀).val with hDist_def
  have hDist_nn : 0 ≤ Dist :=
    C1Val.c1distPair_nonneg hK_d_nn x₀.val (D.T x₀).val
  set C : ℝ := Dist + 1 with hC_def
  have hC_pos : 0 < C := by linarith
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  set δ : ℝ := ε * (1 - D.q) / C with hδ_def
  have hδ_pos : 0 < δ := div_pos (mul_pos hε h1mq_pos) hC_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, D.q^N < δ := by
    by_cases hq_zero : D.q = 0
    · refine ⟨1, ?_⟩
      rw [hq_zero, pow_one]; exact hδ_pos
    exact exists_pow_lt_of_lt_one hδ_pos hq_lt
  refine ⟨N, fun m n hm hn => ?_⟩
  have h_bound := D.iter_dist_le_symm hK_d_nn x₀ m n
  have h_min_ge : N ≤ min m n := le_min hm hn
  have h_q_in : D.q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq_nn, le_of_lt hq_lt⟩
  have h_pow_min_le_pow_N : D.q^(min m n) ≤ D.q^N :=
    pow_le_pow_of_le_one h_q_in.1 h_q_in.2 h_min_ge
  have h_step_le :
      D.q^(min m n) * Dist / (1 - D.q) ≤ D.q^N * Dist / (1 - D.q) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right h_pow_min_le_pow_N hDist_nn) h1mq_nn
  have h_Dist_le_C : Dist ≤ C := by linarith
  have h_C_step :
      D.q^N * Dist / (1 - D.q) ≤ D.q^N * C / (1 - D.q) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left h_Dist_le_C (pow_nonneg hq_nn N)) h1mq_nn
  rw [hδ_def] at hN
  have h_cross : D.q^N * C < ε * (1 - D.q) := by
    have h_step : D.q^N * C < (ε * (1 - D.q) / C) * C :=
      (mul_lt_mul_iff_of_pos_right hC_pos).mpr hN
    rwa [div_mul_cancel₀ _ hC_ne] at h_step
  have h_final : D.q^N * C / (1 - D.q) < ε := by
    rw [div_lt_iff₀ h1mq_pos]; linarith
  calc C1Val.c1distPair (D.iter x₀ m).val (D.iter x₀ n).val
      ≤ D.q^(min m n) * Dist / (1 - D.q) := h_bound
    _ ≤ D.q^N * Dist / (1 - D.q) := h_step_le
    _ ≤ D.q^N * C / (1 - D.q) := h_C_step
    _ < ε := h_final

/-! ## iter 18 corollary: V_T and V_S components are each `IsC1Cauchy`

Project the pair-Cauchy result onto the V_T and V_S components: each
projects to a C¹-Cauchy sequence (since `c1dist a.1 b.1 ≤ c1distPair`).
The two component-Cauchy sequences then have BCF + uniform-on-S
derivative limits via the existing iter 7-12 machinery on each
component, producing the C¹ joint fixed-point candidate. -/

/-- **V_T-component is C¹-Cauchy.** -/
theorem ValueClass_C1.iter_V_T_isC1Cauchy {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    (D : ValueClass_C1 K_d) (x₀ : D.Carrier) :
    C1Val.IsC1Cauchy (fun n => (D.iter x₀ n).val.1) := by
  intro ε hε
  obtain ⟨N, hN⟩ := D.iter_isC1CauchyPair hK_d_nn x₀ ε hε
  refine ⟨N, fun m n hm hn => ?_⟩
  have h_pair := hN m n hm hn
  -- c1dist V_T.m V_T.n ≤ c1distPair < ε.
  unfold C1Val.c1distPair at h_pair
  have h_other_nn : 0 ≤ C1Val.c1dist (D.iter x₀ m).val.2 (D.iter x₀ n).val.2 :=
    C1Val.c1dist_nonneg hK_d_nn _ _
  linarith

/-- **V_S-component is C¹-Cauchy.** -/
theorem ValueClass_C1.iter_V_S_isC1Cauchy {K_d : ℝ} (hK_d_nn : 0 ≤ K_d)
    (D : ValueClass_C1 K_d) (x₀ : D.Carrier) :
    C1Val.IsC1Cauchy (fun n => (D.iter x₀ n).val.2) := by
  intro ε hε
  obtain ⟨N, hN⟩ := D.iter_isC1CauchyPair hK_d_nn x₀ ε hε
  refine ⟨N, fun m n hm hn => ?_⟩
  have h_pair := hN m n hm hn
  unfold C1Val.c1distPair at h_pair
  have h_other_nn : 0 ≤ C1Val.c1dist (D.iter x₀ m).val.1 (D.iter x₀ n).val.1 :=
    C1Val.c1dist_nonneg hK_d_nn _ _
  linarith

/-! ## iter 20 (audit-37 Step 3): C¹ fixed-point existence on `ValueClass_C1`

The audit-37 critique observes that `ValueClass_C1.iter_isC1CauchyPair`
proves the Banach iteration is Cauchy, but NOT that a fixed point
exists. This iter adds the missing piece.

Because C¹ values don't admit a clean `c1distPair = 0 ⇒ equality` lemma
on the current `C1Val K_d` structure (the derivative field
`V' : ℝ → ℝ` is not canonical outside `S`; an "iter-21" refactor storing
it as `↥S → ℝ` was once planned but NEVER happened — `V'` is still a
function on all of `ℝ`, so `c1distPair` remains a pseudo-metric and this
deficiency is an open fact), the "fixed point" we produce is a
**`c1distPair`-fixed point**: a `z ∈ D.Carrier` with
`C1Val.c1distPair (D.T z).val z.val = 0`.

This is the correct notion for C¹ Banach fixed-point existence on the
pseudo-metric `c1distPair`; downstream consumers can use the
`c1distPair = 0` conclusion together with any extensionality lemma
they prove at concrete payoff classes (e.g., uniqueness of the C¹
Bellman fixed point).

The completeness hypothesis is packaged as a `ValueClass_C1Complete D`
Prop: every `IsC1CauchyPair` sequence in `D.Carrier` has a
`c1distPair`-limit in `D.Carrier`. -/

/-- **Completeness Prop for a `ValueClass_C1` carrier.** Every Cauchy
sequence (in `c1distPair`) of carrier elements has a `c1distPair`-limit
in the carrier.

This is a theorem-parameter primitive at the abstract layer; at
concrete payoff classes it's discharged by showing the carrier is
closed under the C¹ topology and the C¹ space is complete (the latter
follows from `IsC1Cauchy.toC1ValLim` applied componentwise once the
boundary derivative hypotheses are met). -/
def ValueClass_C1Complete {K_d : ℝ} (D : ValueClass_C1 K_d) : Prop :=
  ∀ s : ℕ → D.Carrier, IsC1CauchyPair (fun n => (s n).val) →
    ∃ z : D.Carrier,
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
        C1Val.c1distPair (s n).val z.val < ε

/-- **Banach contraction principle on `ValueClass_C1`.** Under
completeness, the contracting operator `T` has a `c1distPair`-fixed
point: there exists `z ∈ D.Carrier` with
`C1Val.c1distPair (D.T z).val z.val = 0`.

Proof: take the Banach iteration `D.iter x₀` (Cauchy by iter 18);
use completeness to obtain a carrier limit `z`; apply the
contraction (T-continuity in `c1distPair`) plus the iteration
recursion `iter (n+1) = T (iter n)` to show `c1distPair (T z) z = 0`. -/
theorem ValueClass_C1.exists_c1distPair_fixedPoint {K_d : ℝ}
    (hK_d_nn : 0 ≤ K_d)
    (D : ValueClass_C1 K_d) (hComplete : ValueClass_C1Complete D) :
    ∃ z : D.Carrier, C1Val.c1distPair (D.T z).val z.val = 0 := by
  obtain ⟨x₀_val, hx₀_mem⟩ := D.isNonempty
  let x₀ : D.Carrier := ⟨x₀_val, hx₀_mem⟩
  have h_cauchy : IsC1CauchyPair (fun n => (D.iter x₀ n).val) :=
    D.iter_isC1CauchyPair hK_d_nn x₀
  obtain ⟨z, hz_lim⟩ := hComplete (D.iter x₀) h_cauchy
  refine ⟨z, ?_⟩
  -- Show c1distPair (T z) z = 0 by showing it's ≤ ε for every ε > 0.
  refine le_antisymm ?_ (C1Val.c1distPair_nonneg hK_d_nn _ _)
  -- Want: c1distPair (T z) z ≤ 0; suffices: c1distPair (T z) z < ε for all ε > 0.
  by_contra h_pos
  push Not at h_pos
  set ε : ℝ := C1Val.c1distPair (D.T z).val z.val with hε_def
  have hε_pos : 0 < ε := h_pos
  -- Take δ = ε/3 so 3δ < 2ε (giving us strict slack against q ≤ 1).
  set δ : ℝ := ε / 3 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  have h_3δ_eq : (3 : ℝ) * δ = ε := by rw [hδ_def]; ring
  -- Pick N s.t. for all n ≥ N, c1distPair (iter n) z < δ.
  obtain ⟨N, hN⟩ := hz_lim δ hδ_pos
  have h_iter_close : C1Val.c1distPair (D.iter x₀ (N + 1)).val z.val < δ :=
    hN (N + 1) (Nat.le_succ N)
  have h_iter_prev : C1Val.c1distPair (D.iter x₀ N).val z.val < δ :=
    hN N (le_refl N)
  -- Contraction: c1distPair (T (iter N)) (T z) ≤ q · c1distPair (iter N) z ≤ 1 · δ = δ.
  have h_T_step :
      C1Val.c1distPair (D.T (D.iter x₀ N)).val (D.T z).val
        ≤ D.q * C1Val.c1distPair (D.iter x₀ N).val z.val :=
    D.T_contracts (D.iter x₀ N) z
  have hq_le_one : D.q ≤ 1 := le_of_lt D.q_lt_one
  have h_T_le_δ :
      C1Val.c1distPair (D.T (D.iter x₀ N)).val (D.T z).val ≤ δ := by
    calc C1Val.c1distPair (D.T (D.iter x₀ N)).val (D.T z).val
        ≤ D.q * C1Val.c1distPair (D.iter x₀ N).val z.val := h_T_step
      _ ≤ 1 * C1Val.c1distPair (D.iter x₀ N).val z.val := by
          apply mul_le_mul_of_nonneg_right hq_le_one
          exact C1Val.c1distPair_nonneg hK_d_nn _ _
      _ = C1Val.c1distPair (D.iter x₀ N).val z.val := one_mul _
      _ ≤ δ := le_of_lt h_iter_prev
  -- iter (N+1) = T (iter N) by definition.
  have h_iter_eq : D.iter x₀ (N + 1) = D.T (D.iter x₀ N) := by
    simp [ValueClass_C1.iter]
  -- Triangle: c1distPair (T z) z ≤ c1distPair (T z) (iter (N+1))
  --                                 + c1distPair (iter (N+1)) z
  --                              ≤ δ + δ = 2δ < 3δ = ε.
  have h_tri := C1Val.c1distPair_triangle hK_d_nn
    (D.T z).val (D.iter x₀ (N + 1)).val z.val
  -- c1distPair (T z) (iter (N+1)) = c1distPair (iter (N+1)) (T z)
  --                              = c1distPair (T (iter N)) (T z) ≤ δ.
  have h_first :
      C1Val.c1distPair (D.T z).val (D.iter x₀ (N + 1)).val ≤ δ := by
    rw [C1Val.c1distPair_comm, h_iter_eq]
    exact h_T_le_δ
  have h_total : ε ≤ δ + δ := by
    calc ε = C1Val.c1distPair (D.T z).val z.val := hε_def
      _ ≤ C1Val.c1distPair (D.T z).val (D.iter x₀ (N + 1)).val
          + C1Val.c1distPair (D.iter x₀ (N + 1)).val z.val := h_tri
      _ ≤ δ + δ := add_le_add h_first (le_of_lt h_iter_close)
  -- δ + δ = 2δ < 3δ = ε. So ε < ε, contradiction.
  have h_2δ_lt_3δ : (2 : ℝ) * δ < 3 * δ := by
    have : 2 * δ + δ = 3 * δ := by ring
    linarith
  have : ε < ε := by
    calc ε ≤ δ + δ := h_total
      _ = 2 * δ := by ring
      _ < 3 * δ := h_2δ_lt_3δ
      _ = ε := h_3δ_eq
  exact lt_irrefl _ this

end AbstractGame

end -- noncomputable section

end Sanctions
