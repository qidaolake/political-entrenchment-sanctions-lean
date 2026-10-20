/-
Sanctions/Foundations/Basic.lean

Shared entry point for the foundations layer of

  "Entrenchment and the Persistence of Sanctions"
  (Xiaofeng Gong; begun 2025-11-15 as "Why Do Sanctions Persist? A Dynamic
  Political-Economy Model", retitled 2026-09-21 and again 2026-10-11)

This file used to do two unrelated jobs: carry the shared Mathlib import block,
and define the state space `I` / `S`. The second moved to
`Sanctions/Domain/UnitInterval.lean` on 2026-08-27, so that the modelling choice
is declared in one place rather than inside the build prelude.

The import below is deliberate: it re-exports the domain, so the twenty-eight
modules that import this file for `I` and `S` continue to work unchanged, and
the move is invisible to every fully-qualified name.

Add further shared Mathlib imports to `Domain/UnitInterval.lean`, which is where
the targeted-import block now lives (it keeps the Lean server cold start near
30 s rather than the 5-10 min a bare `import Mathlib` costs).
-/

import Sanctions.Domain.UnitInterval

noncomputable section
open Set Function
open scoped Topology

namespace Sanctions

/-- If a rule is strictly below one at the top state, then it cannot
satisfy a sanction floor of the form `max x sbar ≤ r x` on any nonempty
upper interval ending at one. Evaluating the proposed floor at `x = 1`
already gives the contradiction. -/
theorem no_upper_basin_floor_of_top_lt_one
    (r : ℝ → ℝ) (h_top : r 1 < 1) {xbar sbar : ℝ} (hxbar : xbar ≤ 1) :
    ¬ ∀ x ∈ Set.Icc xbar 1, max x sbar ≤ r x := by
  intro h_floor
  have h_at_top := h_floor 1 ⟨hxbar, le_rfl⟩
  exact (not_le_of_gt h_top) (le_trans (le_max_left 1 sbar) h_at_top)

end Sanctions

end
