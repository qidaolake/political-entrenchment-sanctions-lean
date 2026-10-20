/-
Sanctions/Theory/Basin/SenderPersistenceLocalisedShock.lean

**Shock hysteresis without the Target-preference condition, with full-sanction
ascent needed only below the basin** (round BB, 2026-09-28; doc 110 item R7(b),
the sibling of headline row 27).

Headline row 27, `equilibriumTop_senderPersistenceF_temporary_shock_permanent_high`
(`SenderPersistence.lean`), says: along an actual feedback Stackelberg
equilibrium, if the Sender-side persistence basin holds on `[x̄, 1]`, then a
finite exogenous full-sanction episode moves any feasible initial state into
the basin, after which the state stays there, the realised sanction stays at
or above `x̄` and never falls, and the Target plays its Bellman-optimal action
at every date. It takes, besides the basin package and the equilibrium,

* `hF_top` — full sanction strictly raises every state in `[0, 1)`;
* `hxbar_lt_one` — the basin threshold is below one;
* `hsbar_pos` — the sanction floor `s̄` is positive;
* `hx₀_nn`, `hx₀_le` — the initial state is feasible.

The proof reads `hsbar_pos` only for a positivity conjunct that the anchored
statement then discards (the unused-binder census lists it), reads `hF_top`
only through finite basin entry, and `hxbar_lt_one` is derivable. The sibling
here keeps the conclusion verbatim and takes only

* `hF_top_pre` — full sanction strictly raises every state in `[0, x̄]`
  (pre-basin ascent);
* `hx₀ : x₀ ∈ [0, 1]`.

`x̄ < 1` follows from `hF_top_pre` and the basin's `0 ≤ x̄`
(`lt_one_of_preBasinAscent`); the sanction floor `s̄` is unconstrained.

Direction (Rule 13): strictly weaker in hypotheses. Row 27's hypotheses
imply the sibling's (`preBasinAscent_of_hF_top`), as the recovery `example`
at the end of the file checks; the pinned row is untouched. The transition
hypothesis is properly weaker (`Examples/PreBasinAscentStrictness.lean`,
`exists_preBasinAscent_not_strictAdjustment`); no Sender-side basin package
is exhibited at such an economy, so that the sibling reaches an economy row
27 misses is unwitnessed at the level of the full theorem.

Scope (Rule 9): a universal statement over every economy, every equilibrium
`E` and every threshold for which the Sender-side basin package holds; it is
about the constructed-or-given equilibrium `E` it is handed, not about all
equilibria of the economy. The shock phase is the Rule-1 exogenous-phase
exception; the post-shock path is driven by `E.α` (feasible and
Bellman-optimal) and the Sender's upper dynamic argmax.

Rule 22: general in `F`. Rule 3: no new assumption — every hypothesis is an
existing one or implied by one.
-/

import Sanctions.Theory.Basin.SenderPersistence
import Sanctions.Theory.LockIn.LocalisedShockEntry

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-- **Quantitative shock hysteresis along an equilibrium, from the Sender-side
basin and pre-basin ascent.** There is an attained minimum full-sanction drift
`η > 0` on `[0, x̄]` such that, for every feasible initial state, an imposed
full-sanction episode of `⌈x̄ / η⌉₊` periods lands the state in the basin
`[x̄, 1]`; from there the equilibrium path stays in the basin, the realised
sanction is at least `x̄` and non-decreasing, and the Target's action is
Bellman-optimal at every date.

Hypotheses: an equilibrium `E`, the Sender-side basin package on `[x̄, 1]`
(no hypothesis on the Target's ranking over sanctions), and ascent at full
sanction on `[0, x̄]`. General in `F`. -/
theorem equilibriumTop_senderPersistenceF_min_drift_shock_of_preBasinAscent
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar sbar : ℝ}
    (hB : p.SenderPersistenceBasinTop E.V_S E.α xbar sbar)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1) :
    ∃ η : ℝ, 0 < η ∧
      (∃ xmin ∈ Set.Icc (0 : ℝ) xbar, η = p.fullShockDrift xmin) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) xbar, η ≤ p.fullShockDrift x) ∧
      ∀ x₀ ∈ Sanctions.I,
        p.shockPathF x₀ (Nat.ceil (xbar / η)) ∈ Set.Icc xbar 1 ∧
        (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                (p.shockPathF x₀ (Nat.ceil (xbar / η))) n ∈ Set.Icc xbar 1) ∧
        (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                        (p.shockPathF x₀ (Nat.ceil (xbar / η))) n) ∧
        Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α
                    (p.shockPathF x₀ (Nat.ceil (xbar / η)))) ∧
        (∀ n, IsMaxOn
          (fun a => p.joint_T_top_integrand E.V_T E.V_S
                      (p.dynamicTopLockInPathF E.V_S E.α
                        (p.shockPathF x₀ (Nat.ceil (xbar / η))) n) a)
          Sanctions.I
          (E.α (p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀ (Nat.ceil (xbar / η))) n))) := by
  obtain ⟨η, hη_pos, hη_attains, hη_floor, hentry⟩ :=
    p.shockPathF_exists_min_drift_uniform_natCeil_bound_of_preBasinAscent
      hB.xbar_nonneg hF_top_pre
  refine ⟨η, hη_pos, hη_attains, hη_floor, ?_⟩
  intro x₀ hx₀
  have hN := hentry x₀ hx₀ (Nat.ceil (xbar / η)) le_rfl
  obtain ⟨h1, _, h3, h4, h5⟩ :=
    p.equilibriumTop_senderPersistenceF_long_run_nonDecreasing E hB hN
  exact ⟨hN, h1, h3, h4, h5⟩

/-- **Anchored finite shock entry, localised (sibling of headline row 27).**
The conclusion of `equilibriumTop_senderPersistenceF_temporary_shock_permanent_high`
verbatim: some finite full-sanction episode moves the feasible initial state
`x₀` into the basin `[x̄, 1]`, after which the equilibrium path stays in the
basin, the realised sanction is at least `x̄` and never falls, and the
Target's action is Bellman-optimal at every date.

Premises: the Sender-side basin package `hB` on `[x̄, 1]` at the equilibrium
`E` (the forward-looking Sender has a maximiser at or above `max(x, s̄)` at
every basin state, and its greatest maximiser rises with the state), ascent
at full sanction on `[0, x̄]` only, and `x₀ ∈ [0, 1]`. Against row 27 this
drops the positive sanction floor `hsbar_pos` (read there only for a conjunct
the anchored statement discards), the threshold bound `hxbar_lt_one`
(derivable: `lt_one_of_preBasinAscent`), and replaces global ascent on
`[0, 1)` by ascent on `[0, x̄]`. Strictly weaker in hypotheses (Rule 13).
General in `F`. -/
theorem equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent
    (E : p.FeedbackStackelbergEquilibriumTop) {xbar sbar x₀ : ℝ}
    (hB : p.SenderPersistenceBasinTop E.V_S E.α xbar sbar)
    (hF_top_pre : ∀ x ∈ Set.Icc (0 : ℝ) xbar, x < p.F x 1)
    (hx₀ : x₀ ∈ Sanctions.I) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α (p.shockPathF x₀ N) n
              ∈ Set.Icc xbar 1) ∧
      (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                      (p.shockPathF x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α
                  (p.shockPathF x₀ N)) ∧
      (∀ n, IsMaxOn
        (fun a => p.joint_T_top_integrand E.V_T E.V_S
                    (p.dynamicTopLockInPathF E.V_S E.α
                      (p.shockPathF x₀ N) n) a)
        Sanctions.I
        (E.α (p.dynamicTopLockInPathF E.V_S E.α
                (p.shockPathF x₀ N) n))) := by
  obtain ⟨η, -, -, -, h⟩ :=
    p.equilibriumTop_senderPersistenceF_min_drift_shock_of_preBasinAscent
      E hB hF_top_pre
  obtain ⟨-, h1, h2, h3, h4⟩ := h x₀ hx₀
  exact ⟨Nat.ceil (xbar / η), h1, h2, h3, h4⟩

/-- Rule-13 recovery check: headline row 27's statement, with its full
premise list, follows from the localised sibling. -/
example (E : p.FeedbackStackelbergEquilibriumTop) {xbar sbar x₀ : ℝ}
    (hB : p.SenderPersistenceBasinTop E.V_S E.α xbar sbar)
    (hF_top : ∀ x ∈ Set.Ico (0 : ℝ) 1, x < p.F x 1)
    (hxbar_lt_one : xbar < 1)
    (_hsbar_pos : 0 < sbar)
    (hx₀_nn : 0 ≤ x₀) (hx₀_le : x₀ ≤ 1) :
    ∃ N : ℕ,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α (p.shockPathF x₀ N) n
              ∈ Set.Icc xbar 1) ∧
      (∀ n, xbar ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                      (p.shockPathF x₀ N) n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α
                  (p.shockPathF x₀ N)) ∧
      (∀ n, IsMaxOn
        (fun a => p.joint_T_top_integrand E.V_T E.V_S
                    (p.dynamicTopLockInPathF E.V_S E.α
                      (p.shockPathF x₀ N) n) a)
        Sanctions.I
        (E.α (p.dynamicTopLockInPathF E.V_S E.α
                (p.shockPathF x₀ N) n))) :=
  p.equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent
    E hB (p.preBasinAscent_of_hF_top hF_top hxbar_lt_one) ⟨hx₀_nn, hx₀_le⟩

end Params
end AbstractGame

end

-- The axiom report below names declarations in full; several names pass the
-- 100-character line limit, which is accepted for these report lines only.
set_option linter.style.longLine false

#print axioms Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceF_min_drift_shock_of_preBasinAscent
#print axioms Sanctions.AbstractGame.Params.equilibriumTop_senderPersistenceF_temporary_shock_permanent_high_of_preBasinAscent

end Sanctions
