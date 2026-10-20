/-
Sanctions/Examples/MinLawSubmodularityWitness.lean

**An admissible transition law that satisfies Curtat's (A8) while depending on
both of its arguments** — the witness that refutes a universal this project had
been asserting about its own transition class.

## The universal that is refuted

Two places in this development claimed, in substance:

> the Curtat 1996 / Amir 2002 supermodular route is provably unavailable for the
> project's transition, **for every economy in the class**

(`PaperRefer/StochasticGames/DeterministicTransitionObstructions-collected-2026-08.md`,
and until 2026-08-31 the `Sanctions/Foundations.lean` aggregator comment). The
reasoning was that `F_mono_x`, `F_mono_s` and `F_diag` force the transition to
grow strictly in both arguments, so that the threshold kernel is never
submodular.

**The reasoning does not go through, and the universal is false.** The law
`minLaw x s = min x s` satisfies every transition field of `Params` —

* `minLaw_mem` — it maps the unit square into the unit interval (`F_mem`);
* `minLaw_continuous` — it is jointly continuous (`F_continuous`);
* `minLaw_mono_x`, `minLaw_mono_s` — it is nondecreasing in each argument
  separately (`F_mono_x`, `F_mono_s`);
* `minLaw_diag` — `min x x = x`, so a sanction equal to the inherited state
  leaves the state unchanged (`F_diag`)

— it depends genuinely on **both** arguments (`minLaw_nonconstant_fst`,
`minLaw_nonconstant_snd`, at explicit endpoints), and **every** threshold CDF it
induces is submodular (`minLaw_submodular`). So (A8) holds at an admissible
transition, and the obstruction is not a property of the class.

## Why it works, and what the exact condition is

Submodularity of a threshold indicator fails at an ordered rectangle exactly when
the lower corner is *strictly* below both cross corners — that is the content of
`not_submodularAt_cdf_of_strict` in `Foundations/DiracSubmodularity.lean`. For
`min` that never happens, because of the **rectangle-min identity**
`minLaw_rectangle`:

    min x₁ a₁ = min (min x₁ a₂) (min x₂ a₁)   whenever x₁ ≤ x₂ and a₁ ≤ a₂,

so the lower corner always *equals* one of the two cross corners rather than
sitting strictly below both.

Read against Amir (2002, §2.2), whose criterion is that `F` fails submodularity
"unless the zero-one discontinuity of `F` is contained along a vertical or a
horizontal line": `min`'s level set `{min x s ≤ y}` is the complement of an upper
square, so its boundary is **L-shaped** — a vertical segment *plus* a horizontal
one. That is neither a single vertical line nor a single horizontal line, so
Amir's graphical criterion predicts failure, and yet submodularity holds. The
criterion is *sufficient for the cases it covers and not necessary*; it is not a
classification, and it should not be cited as one.

## What this does NOT show (Rule 9)

This is an existence certificate for the transition class and nothing more.

* It does **not** reopen the Curtat route for *this* model. The transitions this
  project actually uses — `affineF δ` with `δ ∈ (0,1)`, and the non-affine
  `ratchetF` / `quadBumpF` / `wobbleF` witnesses — do grow strictly in both
  arguments, so `not_submodularAt_cdf_of_strict` still applies to them and (A8)
  still fails for them. The verdict for the model is unchanged.
* It does **not** exhibit a full `Params` instance. What is verified here is that
  the five *transition* fields are jointly satisfiable together with (A8); the
  remaining payoff, discount and selector fields are untouched. A reader may not
  infer "there is an economy in this project satisfying Curtat's hypotheses" —
  (A8) is one of nine, and (A1)–(A7) and (A9) are not addressed.
* It carries **no** claim of typicality. `min x s` is an unusual sanctions
  technology: the state falls to whichever of inherited entrenchment and the
  applied sanction is lower, so a weak sanction is fully effective and a harsh
  one has no extra bite.
-/

import Sanctions.Foundations.DiracSubmodularity

namespace Sanctions.Examples.MinLaw

open Set Sanctions.DiracKernel

/-- **The transition that takes the smaller of state and sanction.** -/
noncomputable def minLaw (x s : ℝ) : ℝ := min x s

/-! ## 1. It is an admissible transition: the five `Params` transition fields -/

/-- `F_mem`: the unit square is mapped into the unit interval. -/
theorem minLaw_mem {x s : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    minLaw x s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min hx.1 hs.1, (min_le_left _ _).trans hx.2⟩

/-- `F_continuous`: jointly continuous. -/
theorem minLaw_continuous : Continuous (fun p : ℝ × ℝ => minLaw p.1 p.2) :=
  continuous_fst.min continuous_snd

/-- `F_mono_x`: a higher inherited state never lowers the successor state. -/
theorem minLaw_mono_x (s : ℝ) : Monotone (fun x => minLaw x s) :=
  fun _ _ h => min_le_min h le_rfl

/-- `F_mono_s`: a harsher sanction never lowers the successor state. -/
theorem minLaw_mono_s (x : ℝ) : Monotone (fun s => minLaw x s) :=
  fun _ _ h => min_le_min le_rfl h

/-- `F_diag`: a sanction equal to the inherited state leaves the state fixed. -/
theorem minLaw_diag (x : ℝ) : minLaw x x = x := min_self x

/-! ## 2. It depends on both arguments -/

/-- Moving the *state* alone changes the law. -/
theorem minLaw_nonconstant_fst : minLaw 0 1 ≠ minLaw 1 1 := by
  unfold minLaw; norm_num

/-- Moving the *sanction* alone changes the law. -/
theorem minLaw_nonconstant_snd : minLaw 1 0 ≠ minLaw 1 1 := by
  unfold minLaw; norm_num

/-! ## 3. Yet every threshold kernel is submodular -/

/-- **The rectangle-min identity.** At every ordered rectangle the lower corner
equals the smaller of the two cross corners — never strictly below both, which
is what a violation of submodularity would require. -/
theorem minLaw_rectangle {x₁ x₂ a₁ a₂ : ℝ} (hx : x₁ ≤ x₂) (ha : a₁ ≤ a₂) :
    minLaw x₁ a₁ = min (minLaw x₁ a₂) (minLaw x₂ a₁) := by
  unfold minLaw
  refine le_antisymm (le_min (min_le_min le_rfl ha) (min_le_min hx le_rfl)) ?_
  refine le_min ?_ ?_
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem minLaw_submodularAt (y : ℝ) {x₁ x₂ a₁ a₂ : ℝ} (hx : x₁ ≤ x₂) (ha : a₁ ≤ a₂) :
    SubmodularAt (cdf minLaw y) x₁ x₂ a₁ a₂ := by
  have hkey := minLaw_rectangle hx ha
  have h12 : minLaw x₁ a₁ ≤ minLaw x₁ a₂ := minLaw_mono_s x₁ ha
  have h21 : minLaw x₁ a₁ ≤ minLaw x₂ a₁ := minLaw_mono_x a₁ hx
  have h22 : minLaw x₁ a₂ ≤ minLaw x₂ a₂ := minLaw_mono_x a₂ hx
  have h22' : minLaw x₂ a₁ ≤ minLaw x₂ a₂ := minLaw_mono_s x₂ ha
  simp only [SubmodularAt, cdf]
  split_ifs <;> norm_num <;>
    first
      | linarith
      | (rw [hkey] at *; simp only [min_le_iff] at *; tauto)

/-- **(A8) holds at `minLaw`.** Every threshold CDF the law induces is
submodular in the (state, sanction) pair. -/
theorem minLaw_submodular (y : ℝ) : Submodular (cdf minLaw y) :=
  fun _ _ _ _ hx ha => minLaw_submodularAt y hx ha

/-- **The refutation, packaged.** There is a law that is nondecreasing in each
argument, fixes the diagonal, depends on both arguments, and satisfies every
threshold-submodularity inequality. So "the deterministic threshold kernel is
submodular only if the law ignores one argument" is false. -/
theorem exists_nondegenerate_submodular_law :
    ∃ f : ℝ → ℝ → ℝ,
      (∀ s, Monotone (fun x => f x s)) ∧
      (∀ x, Monotone (fun s => f x s)) ∧
      (∀ x, f x x = x) ∧
      f 0 1 ≠ f 1 1 ∧
      f 1 0 ≠ f 1 1 ∧
      (∀ y, Submodular (cdf f y)) :=
  ⟨minLaw, minLaw_mono_x, minLaw_mono_s, minLaw_diag,
    minLaw_nonconstant_fst, minLaw_nonconstant_snd, minLaw_submodular⟩

end Sanctions.Examples.MinLaw
