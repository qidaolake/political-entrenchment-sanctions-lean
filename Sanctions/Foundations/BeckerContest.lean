/-
Sanctions/Foundations/BeckerContest.lean

**Becker (1983, QJE 98(3), "A Theory of Competition Among Pressure Groups for
Political Influence") — two-player additive-influence pressure contest with
quadratic lobbying costs, solved in closed form.**

Two groups exert political pressure `p, q ≥ 0`.  Influence is *additive* in the
pressure difference (the zero-sum property of Becker's influence function,
eqs. 6–9), so with stake `S` (the group's marginal benefit of influence) and a
quadratic pressure-production cost (Becker's eq. 11 cost-of-pressure function
specialized to the quadratic), the contest payoffs are

  `v₁(p; q) = S₁·(p − q) − c₁·p²`,   `v₂(q; p) = S₂·(q − p) − c₂·q²`.

The rival's pressure enters only through an additive constant, so each group's
best response is a **dominant strategy** — the clipped first-order-condition
vertex `p* = max 0 (S/(2c))` (Becker's FOCs, eqs. 15–16).  The Nash
equilibrium therefore exists, is unique, and is closed-form: no fixed-point
machinery.  The argmax is certified by the exact completed-square identity
`v(p*) − v(p) = c·(p − p*)²` (a polynomial identity, kernel-checked).

Contents (all generic over abstract stakes `S` and costs `c` — Rule 19: no
game-specific content):

* `pStar`                     — the dominant-strategy equilibrium pressure;
* `completedSquare_certificate` — the exact argmax certificate;
* `pStar_isMaxOn` / `pStar_isMaxOn_contest` — the pressure is a *derived*
  argmax on `p ≥ 0` (isolated payoff / full contest payoff);
* `contest_nash` / `contest_nash_unique` — existence and uniqueness of the
  Nash pair (dominant strategies ⟹ unique);
* `pStar_mono_stake`          — the stake comparative static read off Becker's
  equations 15–16 (his Proposition 1 concerns efficiency at producing pressure,
  not this; re-anchored round AI, 2026-09-22): equilibrium pressure is
  monotone in the group's stake;
* `pStar_sub_pStar_eq`        — on the interior region the net influence
  `p₁* − p₂*` is affine in the stakes;
* `pStar_continuous`          — continuity in the stake.
-/

import Sanctions.Foundations.Basic

namespace Sanctions
namespace BeckerContest

/-! ### The dominant-strategy equilibrium pressure -/

/-- **Equilibrium pressure** (Becker 1983, FOCs eqs. 15–16 specialized to
quadratic cost): the best-response pressure `max 0 (S/(2c))` of a group with
stake `S` and quadratic cost coefficient `c` — the FOC vertex `S/(2c)`,
clipped at zero (pressure cannot be negative). -/
noncomputable def pStar (S c : ℝ) : ℝ := max 0 (S / (2 * c))

/-- Equilibrium pressure is nonnegative. -/
theorem pStar_nonneg (S c : ℝ) : 0 ≤ pStar S c := le_max_left _ _

/-- **Interior form**: with a nonnegative stake the clip is inactive and
`p* = S/(2c)` exactly. -/
theorem pStar_eq_of_nonneg {S c : ℝ} (hc : 0 < c) (hS : 0 ≤ S) :
    pStar S c = S / (2 * c) :=
  max_eq_right (div_nonneg hS (by positivity))

/-- **Corner form**: with a nonpositive stake the optimal pressure is zero
(exerting costly pressure for a worthless prize is dominated). -/
theorem pStar_eq_zero_of_nonpos {S c : ℝ} (hc : 0 < c) (hS : S ≤ 0) :
    pStar S c = 0 :=
  max_eq_left (div_nonpos_of_nonpos_of_nonneg hS (by positivity))

/-! ### The completed-square argmax certificate -/

/-- **Completed-square argmax certificate** (Becker eq. 11 payoff, FOCs
eqs. 15–16): at the interior optimum `p* = S/(2c)`, the payoff loss from any
deviation `p` is exactly the square `v(p*; q) − v(p; q) = c·(p − p*)²` — an
exact polynomial identity, independent of the rival's pressure `q`. -/
theorem completedSquare_certificate {c : ℝ} (hc : c ≠ 0) (S q p : ℝ) :
    (S * (S / (2 * c) - q) - c * (S / (2 * c)) ^ 2)
      - (S * (p - q) - c * p ^ 2) = c * (p - S / (2 * c)) ^ 2 := by
  field_simp
  ring

/-! ### The pressure is a derived argmax (Rule-1 certificate) -/

/-- **The clipped vertex maximizes the isolated payoff `S·p − c·p²` on
`p ≥ 0`.**  Interior case by the completed square, corner case (`S ≤ 0`)
because both payoff terms are then nonpositive. -/
theorem pStar_isMaxOn {c : ℝ} (hc : 0 < c) (S : ℝ) :
    IsMaxOn (fun p => S * p - c * p ^ 2) (Set.Ici 0) (pStar S c) := by
  rw [isMaxOn_iff]
  intro p hp
  rw [Set.mem_Ici] at hp
  rcases le_or_gt S 0 with hS | hS
  · rw [pStar_eq_zero_of_nonpos hc hS]
    have h1 : S * p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hS hp
    have h2 : 0 ≤ c * p ^ 2 := mul_nonneg hc.le (sq_nonneg p)
    nlinarith
  · rw [pStar_eq_of_nonneg hc hS.le]
    have hcert := completedSquare_certificate hc.ne' S 0 p
    have hsq : 0 ≤ c * (p - S / (2 * c)) ^ 2 := mul_nonneg hc.le (sq_nonneg _)
    nlinarith

/-- **Dominant strategy** (Becker's additive influence, eqs. 6–9): the rival's
pressure `q` enters the contest payoff `S·(p − q) − c·p²` only through the
additive constant `−S·q`, so the same `pStar` is the best response to *every*
rival pressure. -/
theorem pStar_isMaxOn_contest {c : ℝ} (hc : 0 < c) (S q : ℝ) :
    IsMaxOn (fun p => S * (p - q) - c * p ^ 2) (Set.Ici 0) (pStar S c) := by
  have h := pStar_isMaxOn hc S
  rw [isMaxOn_iff] at h ⊢
  intro p hp
  have hpq := h p hp
  simp only at hpq ⊢
  nlinarith

/-- Being a best response to a rival pressure `q` is the same as maximizing
the isolated payoff: the rival term is an additive constant. -/
theorem isMaxOn_contest_iff (S c q p : ℝ) :
    IsMaxOn (fun p' => S * (p' - q) - c * p' ^ 2) (Set.Ici 0) p ↔
      IsMaxOn (fun p' => S * p' - c * p' ^ 2) (Set.Ici 0) p := by
  simp only [isMaxOn_iff]
  constructor
  · intro h x hx
    have := h x hx
    simp only at this ⊢
    nlinarith
  · intro h x hx
    have := h x hx
    simp only at this ⊢
    nlinarith

/-! ### Nash equilibrium: existence and uniqueness -/

/-- **Nash equilibrium of the two-group pressure contest, in closed form**
(Becker 1983, eqs. 6–9, 11, 15–16): both groups playing their clipped FOC
vertices is a Nash equilibrium — each `pStar` is a best response (indeed a
dominant strategy) to the other's equilibrium pressure.  Existence with no
fixed-point machinery. -/
theorem contest_nash {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (S₁ S₂ : ℝ) :
    IsMaxOn (fun p => S₁ * (p - pStar S₂ c₂) - c₁ * p ^ 2) (Set.Ici 0)
        (pStar S₁ c₁) ∧
      IsMaxOn (fun q => S₂ * (q - pStar S₁ c₁) - c₂ * q ^ 2) (Set.Ici 0)
        (pStar S₂ c₂) :=
  ⟨pStar_isMaxOn_contest hc₁ S₁ _, pStar_isMaxOn_contest hc₂ S₂ _⟩

/-- **Uniqueness of the best response** (strict concavity): any maximizer of
the isolated payoff `S·p − c·p²` on `p ≥ 0` *equals* the clipped vertex. -/
theorem pStar_unique {c : ℝ} (hc : 0 < c) {S p : ℝ} (hp : p ∈ Set.Ici 0)
    (h : IsMaxOn (fun q => S * q - c * q ^ 2) (Set.Ici 0) p) :
    p = pStar S c := by
  rw [Set.mem_Ici] at hp
  have h1 := (isMaxOn_iff.mp h) (pStar S c) (pStar_nonneg S c)
  simp only at h1
  rcases le_or_gt S 0 with hS | hS
  · -- corner: `p* = 0`; optimality of `p` forces `0 ≤ S·p − c·p²`, but both
    -- terms are `≤ 0`, so `p² = 0`.
    rw [pStar_eq_zero_of_nonpos hc hS] at h1 ⊢
    have hSp : S * p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hS hp
    have hsq : p ^ 2 ≤ 0 := by nlinarith
    have : p ^ 2 = 0 := le_antisymm hsq (sq_nonneg p)
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  · -- interior: the completed square forces `(p − p*)² ≤ 0`.
    rw [pStar_eq_of_nonneg hc hS.le] at h1 ⊢
    set t := S / (2 * c) with ht
    have hSt : S = 2 * c * t := by rw [ht]; field_simp
    rw [hSt] at h1
    have hsq : (p - t) ^ 2 ≤ 0 := by nlinarith
    have : (p - t) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
    have := pow_eq_zero_iff two_ne_zero |>.mp this
    linarith

/-- **Uniqueness of the Nash pair** (dominant strategies ⟹ unique): any pair
of mutual best responses in the contest equals the closed form
`(pStar S₁ c₁, pStar S₂ c₂)`. -/
theorem contest_nash_unique {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    {S₁ S₂ p q : ℝ} (hp : p ∈ Set.Ici 0) (hq : q ∈ Set.Ici 0)
    (hbrP : IsMaxOn (fun p' => S₁ * (p' - q) - c₁ * p' ^ 2) (Set.Ici 0) p)
    (hbrQ : IsMaxOn (fun q' => S₂ * (q' - p) - c₂ * q' ^ 2) (Set.Ici 0) q) :
    p = pStar S₁ c₁ ∧ q = pStar S₂ c₂ :=
  ⟨pStar_unique hc₁ hp ((isMaxOn_contest_iff S₁ c₁ q p).mp hbrP),
   pStar_unique hc₂ hq ((isMaxOn_contest_iff S₂ c₂ p q).mp hbrQ)⟩

/-! ### Comparative statics (the stake, Becker eqs. 15–16) and continuity -/

/-- **The stake comparative static** (Becker 1983, eqs. 15–16; not his Proposition 1,
which is about efficiency at producing pressure): the
equilibrium pressure is monotone non-decreasing in the group's stake — a
group with more at risk exerts weakly more pressure. -/
theorem pStar_mono_stake {c : ℝ} (hc : 0 < c) : Monotone fun S => pStar S c := by
  intro S S' hSS'
  have h2c : (0 : ℝ) < 2 * c := by positivity
  exact max_le_max le_rfl (by gcongr)

/-- **Net influence is affine in the stakes** on the interior region: with
both stakes nonnegative the clips are inactive and the equilibrium pressure
difference is the affine expression `S₁/(2c₁) − S₂/(2c₂)`. -/
theorem pStar_sub_pStar_eq {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    {S₁ S₂ : ℝ} (h₁ : 0 ≤ S₁) (h₂ : 0 ≤ S₂) :
    pStar S₁ c₁ - pStar S₂ c₂ = S₁ / (2 * c₁) - S₂ / (2 * c₂) := by
  rw [pStar_eq_of_nonneg hc₁ h₁, pStar_eq_of_nonneg hc₂ h₂]

/-- Continuity of the equilibrium pressure in the stake. -/
theorem pStar_continuous (c : ℝ) : Continuous fun S => pStar S c := by
  unfold pStar
  fun_prop

end BeckerContest
end Sanctions
