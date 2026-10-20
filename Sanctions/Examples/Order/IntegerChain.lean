/-
Sanctions/Examples/Order/IntegerChain.lean

**ROLE: GENERALITY WITNESS (Rule 9B).**

`Foundations/BinaryComparativeStatics.lean` and
`Foundations/CrossOrderComparison.lean` state the single-crossing and
cross-order relations over arbitrary ordered types rather than over `ℝ`. A class
that generalizes a named special case has to exhibit a member outside that case,
or its generality is asserted and not shown --- so this file instantiates the
relations on the integer chain `[0,3] ⊆ ℤ`, with integer values, where no
subtraction-based discharger and no real analysis is available.

The instance is chosen so the hypothesis genuinely filters: at `f n = -(n-1)^2`
and `g n = -(n-2)^2`, the single-crossing premise `f aL ≤ f aH` holds only for
the pairs `(0,1)` and `(0,2)`, and the relation has to be checked exactly there.
A witness in which the premise were vacuous would show nothing.

Rule 9: this shows the generalization is inhabited outside `ℝ`. It does not show
that anything in the sanctions development needs a non-real chain --- nothing
does, today.
-/

import Sanctions.Foundations.BinaryComparativeStatics
import Sanctions.Foundations.CrossOrderComparison

namespace Sanctions.Examples.Order

open Set Sanctions.BinaryComparativeStatics

/-- The chain: four integers. -/
def Z4 : Set ℤ := Icc 0 3

/-- Peaked at `1`. -/
def fZ (n : ℤ) : ℤ := -(n - 1) ^ 2

/-- Peaked at `2`. -/
def gZ (n : ℤ) : ℤ := -(n - 2) ^ 2

/-- **The ordinal relation holds on an integer chain, with integer values.**
Neither the domain nor the codomain is `ℝ`, and the premise is not vacuous. -/
theorem strictSCLowerOn_int : StrictSCLowerOn fZ gZ Z4 := by
  intro aL aH haL haH hlt hf
  obtain ⟨hL0, hL3⟩ := haL
  obtain ⟨hH0, hH3⟩ := haH
  simp only [fZ, gZ] at hf ⊢
  interval_cases aL <;> interval_cases aH <;> omega

/-- `1` maximizes `fZ` on the chain. -/
theorem isMaxOn_fZ : IsMaxOn fZ Z4 1 := by
  intro n hn
  obtain ⟨h0, h3⟩ := hn
  simp only [fZ, mem_setOf_eq]
  interval_cases n <;> omega

/-- `2` maximizes `gZ` on the chain. -/
theorem isMaxOn_gZ : IsMaxOn gZ Z4 2 := by
  intro n hn
  obtain ⟨h0, h3⟩ := hn
  simp only [gZ, mem_setOf_eq]
  interval_cases n <;> omega

/-- **The argmax theorem fires off `ℝ`.** The general result, instantiated at
the integer chain, orders the two maximizers. -/
theorem argmax_order_int : (1 : ℤ) ≤ 2 :=
  argmax_le_of_strictSCLowerOn strictSCLowerOn_int
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    isMaxOn_fZ isMaxOn_gZ

/-- **Cross-order too, and not by the easy route.**

On `B = {2}` against `A = [2,3]`, cross-order holds: `fZ 2 = -1` sits below both
`gZ 2 = 0` and `gZ 3 = -1`. But `gZ` *falls* from `2` to `3`, so it is not
monotone on `A` and `crossOrderOn_of_le_of_monotoneOn` cannot deliver this ---
the majorant pattern is sufficient and not necessary, and here is a chain on
which the gap is visible. -/
theorem crossOrderOn_int :
    Sanctions.CrossOrder.CrossOrderOn fZ gZ (Icc (2 : ℤ) 2) (Icc (2 : ℤ) 3) := by
  intro x hx y hy _
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy3⟩ := hy
  simp only [fZ, gZ]
  interval_cases x <;> interval_cases y <;> norm_num

/-- And `gZ` really is not monotone there, so the previous theorem is not the
majorant pattern in disguise. -/
theorem gZ_not_monotoneOn : ¬ MonotoneOn gZ (Icc (2 : ℤ) 3) := by
  intro h
  have := h (by constructor <;> norm_num : (2 : ℤ) ∈ Icc (2 : ℤ) 3)
    (by constructor <;> norm_num : (3 : ℤ) ∈ Icc (2 : ℤ) 3) (by norm_num)
  simp only [gZ] at this
  norm_num at this

end Sanctions.Examples.Order
