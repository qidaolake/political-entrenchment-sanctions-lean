-- scripts/structural_fingerprint_fixture.lean -- the fixture behind
-- scripts/Test-StructuralFingerprint.ps1 (round O, doc 82 P5). The script
-- splices scripts/contract_probe.lean.template above this file and checks the
-- digest invariants listed beside each pair. Keep the pairs and the
-- expectations table in the script in step.

-- alpha twins: the same digest
theorem fxA (x : Nat) (h : 0 < x) : 0 < x + 1 := by omega
theorem fxB (y : Nat) (hy : 0 < y) : 0 < y + 1 := by omega
-- a changed hypothesis: a different digest
theorem fxC (x : Nat) (h : 0 ≤ x) : 0 < x + 1 := by omega
-- a changed binder info: a different digest (binder infos are kept)
theorem fxD {x : Nat} (h : 0 < x) : 0 < x + 1 := by omega
-- proof terms inside a statement: the same digest (proofs print as ⋯)
theorem fxE : (⟨1, by decide⟩ : {n : Nat // 0 < n}).val = 1 := rfl
theorem fxF : (⟨1, Nat.one_pos⟩ : {n : Nat // 0 < n}).val = 1 := rfl
-- universe parameters renamed: the same digest (parameters by position)
theorem fxG.{u} (α : Type u) (a : α) : a = a := rfl
theorem fxH.{v} (β : Type v) (b : β) : b = b := rfl
-- a lambda under a binder, all names changed: the same digest
theorem fxI (f : Nat → Nat) (hf : ∀ n, f n = n) : (fun n => f n) 2 = 2 := by simp [hf]
theorem fxJ (g : Nat → Nat) (hg : ∀ m, g m = m) : (fun k => g k) 2 = 2 := by simp [hg]
#structuralRoots fxA fxB fxC fxD fxE fxF fxG fxH fxI fxJ
