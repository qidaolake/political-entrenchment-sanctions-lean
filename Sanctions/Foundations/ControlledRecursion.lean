/-
Sanctions/Foundations/ControlledRecursion.lean

**Comparison for a monotone controlled recursion** (doc 59 §5).

A scalar recursion `y_{n+1} = G(y_n, u_n)` driven by an input sequence `u`,
beside its held-input comparison `z_{n+1} = G(z_n, h)`. With `G` nondecreasing
in each argument:

1. **Domination.** If `z₀ ≤ y₀` and `u_n ≥ h` at every date before `T`, then
   `z_n ≤ y_n` at every date `n ≤ T`. Nothing is assumed about the shape of
   `u`: the driven path may fall while staying above the held one.
2. **The held path.** If `G` fixes its diagonal, the held path from a start in
   `[0, h]` stays in `[0, h]` and is nondecreasing.
3. **Linear growth.** If `G(z, h) − z ≥ η` on `[0, b]`, the held path from `0`
   has gained at least `n·η` after `n` steps, as long as its earlier iterates
   stayed at or below `b`.
4. **Entry.** With `η > 0`, the held path from `0` is at or above `b` at every
   date `n ≥ ⌈b/η⌉`, and so is the driven path at every such date up to `T`.
5. **Retention.** Once the driven path is at or above `b`, inputs at or above
   `b` keep it there.

Nothing here names a game: `G` is any function of two real arguments. The
sanctions wiring — `G` the political transition, the input a sanction
schedule — is `Theory/LockIn/FiniteEpisodePersistence.lean`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Sanctions
namespace ControlledRecursion

open Set

variable (G : ℝ → ℝ → ℝ)

/-- The path driven by the input sequence `u` from `y₀`. -/
def controlledPath (u : ℕ → ℝ) (y₀ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | n + 1 => G (controlledPath u y₀ n) (u n)

/-- The path under the input held at `h`, from `z₀`. -/
def heldPath (h : ℝ) (z₀ : ℝ) (n : ℕ) : ℝ := (fun z => G z h)^[n] z₀

@[simp] theorem controlledPath_zero (u : ℕ → ℝ) (y₀ : ℝ) :
    controlledPath G u y₀ 0 = y₀ := rfl

@[simp] theorem controlledPath_succ (u : ℕ → ℝ) (y₀ : ℝ) (n : ℕ) :
    controlledPath G u y₀ (n + 1) = G (controlledPath G u y₀ n) (u n) := rfl

@[simp] theorem heldPath_zero (h z₀ : ℝ) : heldPath G h z₀ 0 = z₀ := rfl

@[simp] theorem heldPath_succ (h z₀ : ℝ) (n : ℕ) :
    heldPath G h z₀ (n + 1) = G (heldPath G h z₀ n) h :=
  Function.iterate_succ_apply' _ _ _

variable {G}

/-! ## 1. Feasibility and domination -/

/-- A driven path with feasible inputs from a feasible start stays feasible. -/
theorem controlledPath_mem_Icc
    (hmem : ∀ x s, x ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → G x s ∈ Icc (0 : ℝ) 1)
    {u : ℕ → ℝ} (hu : ∀ n, u n ∈ Icc (0 : ℝ) 1) {y₀ : ℝ} (hy₀ : y₀ ∈ Icc (0 : ℝ) 1) :
    ∀ n, controlledPath G u y₀ n ∈ Icc (0 : ℝ) 1 := by
  intro n
  induction n with
  | zero => simpa using hy₀
  | succ n ih => exact hmem _ _ ih (hu n)

/-- **Domination.** Inputs at or above `h` before `T` keep the driven path at
or above the held path through date `T`. -/
theorem heldPath_le_controlledPath
    (hmx : ∀ s, Monotone (fun x => G x s)) (hms : ∀ x, Monotone (fun s => G x s))
    {u : ℕ → ℝ} {h : ℝ} {T : ℕ} (hu : ∀ n < T, h ≤ u n) {y₀ z₀ : ℝ} (hz : z₀ ≤ y₀) :
    ∀ n ≤ T, heldPath G h z₀ n ≤ controlledPath G u y₀ n := by
  intro n
  induction n with
  | zero => intro _; simpa using hz
  | succ n ih =>
    intro hn
    rw [heldPath_succ, controlledPath_succ]
    calc G (heldPath G h z₀ n) h ≤ G (controlledPath G u y₀ n) h :=
          hmx h (ih (Nat.le_of_succ_le hn))
      _ ≤ G (controlledPath G u y₀ n) (u n) := hms _ (hu n (Nat.lt_of_succ_le hn))

/-! ## 2. The held path -/

/-- The held path from `[0, h]` stays in `[0, h]`. -/
theorem heldPath_mem_Icc
    (hmx : ∀ s, Monotone (fun x => G x s)) (hms : ∀ x, Monotone (fun s => G x s))
    (hdiag : ∀ x, G x x = x) {h : ℝ} (hh0 : 0 ≤ h) {z₀ : ℝ} (hz₀ : z₀ ∈ Icc 0 h) :
    ∀ n, heldPath G h z₀ n ∈ Icc 0 h := by
  intro n
  induction n with
  | zero => simpa using hz₀
  | succ n ih =>
    rw [heldPath_succ]
    constructor
    · calc (0 : ℝ) = G 0 0 := (hdiag 0).symm
        _ ≤ G (heldPath G h z₀ n) 0 := hmx 0 ih.1
        _ ≤ G (heldPath G h z₀ n) h := hms _ hh0
    · calc G (heldPath G h z₀ n) h ≤ G h h := hmx h ih.2
        _ = h := hdiag h

/-- The held path from `[0, h]` is nondecreasing. -/
theorem heldPath_monotone
    (hmx : ∀ s, Monotone (fun x => G x s)) (hms : ∀ x, Monotone (fun s => G x s))
    (hdiag : ∀ x, G x x = x) {h : ℝ} (hh0 : 0 ≤ h) {z₀ : ℝ} (hz₀ : z₀ ∈ Icc 0 h) :
    Monotone (heldPath G h z₀) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [heldPath_succ]
  have hmem := heldPath_mem_Icc hmx hms hdiag hh0 hz₀ n
  calc heldPath G h z₀ n = G (heldPath G h z₀ n) (heldPath G h z₀ n) := (hdiag _).symm
    _ ≤ G (heldPath G h z₀ n) h := hms _ hmem.2

/-- **Linear growth below the threshold.** With drift at least `η` on
`[0, b]`, the held path from `0` has gained `n·η` after `n` steps while its
earlier iterates stayed at or below `b`. -/
theorem heldPath_linear_lower_bound
    (hmx : ∀ s, Monotone (fun x => G x s)) (hms : ∀ x, Monotone (fun s => G x s))
    (hdiag : ∀ x, G x x = x) {h b η : ℝ} (hh0 : 0 ≤ h)
    (hη : ∀ z ∈ Icc (0 : ℝ) b, η ≤ G z h - z) :
    ∀ n : ℕ, (∀ k < n, heldPath G h 0 k ≤ b) → (n : ℝ) * η ≤ heldPath G h 0 n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hstay
    have hmem0 : heldPath G h 0 n ∈ Icc 0 h :=
      heldPath_mem_Icc hmx hms hdiag hh0 ⟨le_rfl, hh0⟩ n
    have hdrift := hη _ ⟨hmem0.1, hstay n (Nat.lt_succ_self n)⟩
    have hih := ih (fun k hk => hstay k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    rw [heldPath_succ]
    push_cast
    linarith

/-- **Entry.** With a positive drift floor `η` on `[0, b]`, the held path from
`0` is at or above `b` at every date `n ≥ ⌈b/η⌉`. -/
theorem heldPath_natCeil_entry
    (hmx : ∀ s, Monotone (fun x => G x s)) (hms : ∀ x, Monotone (fun s => G x s))
    (hdiag : ∀ x, G x x = x) {h b η : ℝ} (hh0 : 0 ≤ h) (hη_pos : 0 < η)
    (hη : ∀ z ∈ Icc (0 : ℝ) b, η ≤ G z h - z) :
    ∀ n ≥ Nat.ceil (b / η), b ≤ heldPath G h 0 n := by
  have hmono := heldPath_monotone hmx hms hdiag hh0 (⟨le_rfl, hh0⟩ : (0 : ℝ) ∈ Icc 0 h)
  have hN : b ≤ heldPath G h 0 (Nat.ceil (b / η)) := by
    let N := Nat.ceil (b / η)
    by_contra hnot
    have hlt : heldPath G h 0 N < b := lt_of_not_ge hnot
    have hstay : ∀ k < N, heldPath G h 0 k ≤ b :=
      fun k hk => le_trans (hmono (Nat.le_of_lt hk)) hlt.le
    have hlower := heldPath_linear_lower_bound hmx hms hdiag hh0 hη N hstay
    have hceil : b ≤ (N : ℝ) * η := by
      have hratio : b / η ≤ (N : ℝ) := by
        simpa [N] using (Nat.le_ceil (b / η))
      calc
        b = (b / η) * η := by field_simp
        _ ≤ (N : ℝ) * η := mul_le_mul_of_nonneg_right hratio hη_pos.le
    linarith
  intro n hn
  exact le_trans hN (hmono hn)

/-- **Entry of the driven path.** Inputs at or above `h` before `T`, a
positive drift floor `η` below `b` under the held input, and `T ≥ ⌈b/η⌉` put
the driven path from a nonnegative start at or above `b` at every date from
`⌈b/η⌉` through `T`. -/
theorem controlledPath_ge_of_high_inputs
    (hmx : ∀ s, Monotone (fun x => G x s)) (hms : ∀ x, Monotone (fun s => G x s))
    (hdiag : ∀ x, G x x = x) {u : ℕ → ℝ} {h b η : ℝ} {T : ℕ} (hh0 : 0 ≤ h)
    (hη_pos : 0 < η) (hη : ∀ z ∈ Icc (0 : ℝ) b, η ≤ G z h - z)
    (hu : ∀ n < T, h ≤ u n) {y₀ : ℝ} (hy₀ : 0 ≤ y₀) :
    ∀ n, Nat.ceil (b / η) ≤ n → n ≤ T → b ≤ controlledPath G u y₀ n :=
  fun n hN hnT =>
    le_trans (heldPath_natCeil_entry hmx hms hdiag hh0 hη_pos hη n hN)
      (heldPath_le_controlledPath hmx hms hu hy₀ n hnT)

/-! ## 3. Retention -/

/-- **Retention.** Once the driven path is at or above `b` at date `m`, inputs
at or above `b` from `m` on keep it at or above `b`. -/
theorem controlledPath_ge_of_inputs_ge
    (hmx : ∀ s, Monotone (fun x => G x s)) (hms : ∀ x, Monotone (fun s => G x s))
    (hdiag : ∀ x, G x x = x) {u : ℕ → ℝ} {b y₀ : ℝ} {m : ℕ}
    (hm : b ≤ controlledPath G u y₀ m) (hu : ∀ n, m ≤ n → b ≤ u n) :
    ∀ n, m ≤ n → b ≤ controlledPath G u y₀ n := by
  intro n hn
  induction n with
  | zero =>
    have h0 : m = 0 := Nat.le_zero.mp hn
    subst h0
    exact hm
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hn with heq | hlt
    · subst heq
      exact hm
    · have ih' := ih (Nat.le_of_lt_succ hlt)
      rw [controlledPath_succ]
      calc b = G b b := (hdiag b).symm
        _ ≤ G (controlledPath G u y₀ n) b := hmx b ih'
        _ ≤ G (controlledPath G u y₀ n) (u n) := hms _ (hu n (Nat.le_of_lt_succ hlt))

end ControlledRecursion
end Sanctions
