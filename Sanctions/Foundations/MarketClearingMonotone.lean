/-
Sanctions/Foundations/MarketClearingMonotone.lean

**Generic market-clearing (implicit-root) monotonicity.**

A one-dimensional monotone comparative-static, derivative-free: if a net
"excess demand"/pressure function `g(x, s)` is **strictly decreasing in `x`**
(so for each parameter `s` it has at most one root, the market-clearing level
`x*(s)`) and is **monotone in the parameter `s`**, then the clearing level
`x*(s)` inherits the parameter monotonicity:

* `g` non-decreasing in `s` ⟹ `x*` non-decreasing  (`clearing_mono_of_pressureDiff_mono`);
* `g` non-increasing in `s` ⟹ `x*` non-increasing  (`clearing_anti_of_pressureDiff_anti`).

This is the engine behind the Kaempfer-Lowenberg (1988, AER, §II) political-market
microfoundation in `Theory/Microfoundations/KaempferLowenbergPolity.lean`: there `g = P_J − P_K`
is the net pro-entrenchment pressure between the regime-supporting group `J` and the
opposition group `K`, `x*(s)` is the equilibrium objectionable-policy / hardliner-
entrenchment level, and the sign of `g`'s response to the sanction `s` is exactly the
(K-L-indeterminate) net of the rally, income-incidence, and opposition-empowerment
channels. No derivatives, no compactness — only strict antitonicity in `x` (for
root inversion) and monotonicity in `s`.
-/

import Sanctions.Foundations.Basic

namespace Sanctions
namespace MarketClearing

variable {g : ℝ → ℝ → ℝ} {xstar : ℝ → ℝ}

/-- **Clearing level rises with the parameter.** If the net pressure `g(·, s)` is
strictly decreasing in `x` at every `s` (unique root `x*(s)`) and non-decreasing in
`s` at every `x`, then the clearing level `x*` is non-decreasing. -/
theorem clearing_mono_of_pressureDiff_mono
    (hroot : ∀ s, g (xstar s) s = 0)
    (hx : ∀ s, StrictAnti (fun x => g x s))
    (hs : ∀ x, Monotone (fun s => g x s)) :
    Monotone xstar := by
  intro s s' hss'
  by_contra hcon
  -- `x*(s') < x*(s)` ⟹ (strict antitone in x) `g(x*(s), s') < g(x*(s'), s') = 0`
  have h : xstar s' < xstar s := not_le.mp hcon
  have hlt : g (xstar s) s' < g (xstar s') s' := (hx s') h
  -- but (monotone in s) `0 = g(x*(s), s) ≤ g(x*(s), s')`
  have hge : g (xstar s) s ≤ g (xstar s) s' := hs (xstar s) hss'
  rw [hroot s] at hge
  rw [hroot s'] at hlt
  linarith

/-- **Clearing level falls with the parameter.** Dual of the above: `g` non-increasing
in `s` ⟹ `x*` non-increasing. -/
theorem clearing_anti_of_pressureDiff_anti
    (hroot : ∀ s, g (xstar s) s = 0)
    (hx : ∀ s, StrictAnti (fun x => g x s))
    (hs : ∀ x, Antitone (fun s => g x s)) :
    Antitone xstar := by
  intro s s' hss'
  by_contra hcon
  have h : xstar s < xstar s' := not_le.mp hcon
  have hlt : g (xstar s') s < g (xstar s) s := (hx s) h
  have hge : g (xstar s') s' ≤ g (xstar s') s := hs (xstar s') hss'
  rw [hroot s'] at hge
  rw [hroot s] at hlt
  linarith

end MarketClearing
end Sanctions
