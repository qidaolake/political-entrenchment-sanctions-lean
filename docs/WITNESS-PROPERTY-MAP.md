# What each mechanism witness proves — and what it does not

Written 2026-08-29. This file exists because the properties a stronger mechanism
paper needs are currently **distributed across different economies**, and each
one is often cited for something a neighbouring one actually establishes. Rule
9A is the standing constraint: a witness licenses existence and refutation, and
nothing else — not genericity, not mechanism, not causal attribution.

The audit below was checked against each file's own source. Where a file already
says the limiting thing about itself, that is quoted rather than paraphrased.

---

## The four properties a mechanism claim needs

1. **Adversarial interests** — sanctions actually hurt the Target.
2. **Active continuation channels** — the forward-looking terms are load-bearing,
   not decorative.
3. **Off-corner behaviour** — the equilibrium sanction is interior and varies
   with the political state.
4. **Interaction** — the two continuation motives amplify each other.

No economy in the tree has all four. Nothing has (4) at all.

---

## `Examples/ContinuationDrivenEscalation.lean` — `ceParams`

**Proves.** That the Sender's continuation term is load-bearing, exactly and not
numerically. Both equilibrium value functions are strictly increasing
(`ce_V_S_strictMono`), the equilibrium sanction exceeds the Sender's stage
optimum by exactly `1/8` (`ce_wedge`), and deleting the continuation term returns
the stage rule (`ce_zero_rule_eq_stage`), which on `(1/2, 3/4)` lies below the
diagonal — so the state *decays* on the very interval where the equilibrium path
*escalates* (`ce_zero_path_strictAnti` against `ce_strict_escalation`). The
equilibrium is constructed, not consumed.

**Does not prove** an adversarial sanctions mechanism. The file says so itself:
the header calls it an economy *"whose Target likes being sanctioned"*, records
`∂U_T/∂s = +1` identically, notes the two players' realised stage payoffs are
*"the same real number at every date"*, and concludes *"the players' interests
are aligned, not opposed."*

**Also.** The channel-off exercise holds the Target's policy fixed. It is a
counterfactual on one term inside an objective, not a re-solved equilibrium.

**Its closed loop rests at an interior fixed point** (`3/4`), not at the top —
so it witnesses `MonotoneAttraction.tendsto_fixedPoint_of_crossing`, not the
top-convergence theorem.

---

## `Examples/MechanismWitness.lean` — P3

**Proves.** The economic signs a genuine sanctions conflict should have: interior
Target action, interior dynamic Sender response, strict compliance placation,
positive sanction–state complementarities.

**Does not prove** a constructed equilibrium. The file records a *"true
order-reversal cycle, numerically confirmed; no constructed deterministic"*
fixed point — deterministic value, policy and Newton iteration limit-cycle, and
the coupled equilibrium is reached only through purification. Its two-force
activity is a *"numerical exhibit at the purified equilibrium."*

**Consequence.** P3 is diagnostic evidence about desired signs. It cannot carry a
mechanism theorem. Its cycling says that the reported iterations did not converge
*from the tested starts*; it is **not** evidence that no fixed point exists, nor
that no attracting basin exists elsewhere (Rule 9D.1: non-convergence is never
evidence of non-existence — `G(x) = 1 − x` cycles with period two and has the
fixed point `1/2`; `T(x) = min(1, x²(15/2 − 7x))` on `[0,1]` has the two-cycle
`{1/2, 1}` and the attracting fixed point `0`, with `T(x) ≤ (3/4)x` on
`[0, 1/10]`). Whether a deterministic equilibrium exists there is open.
(Corrected 2026-09-06, doc 68 L8, and 2026-09-08, doc 70 E8; the earlier
wordings inferred non-existence, then non-attraction, from the cycle.)

---

## `Examples/NonAffineInteriorWitness.lean` — `niParams`

**Proves.** The off-corner rule geometry, outside the affine class: `quadBumpF`
is genuinely non-affine, the realised rule is `R x = (x+1)/2`, so `x < R x < 1`
below the top and `R 1 = 1` at it. This is the Rule 9B **generality** witness for
the off-corner conditions, and `Examples/OffCornerNonVacuity.lean` discharges
them here.

**Does not prove** that forward looking *causes* the off-corner response. Both
equilibrium values are identically zero (`niV0 = 0`), so the continuation channel
contributes nothing; the interiority comes entirely from the curvature of the
stage payoff around its ideal sanction. It exhibits the theorem, not the
mechanism.

---

## `Examples/OffCornerNonVacuity.lean`

**Proves.** That the two off-corner conditions are jointly satisfiable at a
constructed equilibrium of a non-affine economy.

**Does not prove** that the region is economically interesting. The conditions
are *incompatible* with the corner route (`σ_dyn_top_V_S_zero_eq_one_of_monotone`
needs the stage payoff maximised at the top sanction, which leaves nothing
interior to beat it), so they describe a disjoint region — but inhabitation is
all that is claimed.

---

## The `FF` versus `MM` comparison layer

**Proves.** Selection-robust comparisons of the fully forward-looking regime
against the fully myopic one, at their own policies, under direct ordinal
dominance or the net-channel route.

**Does not identify the two channels separately.** `00` versus `11` is one
comparison; it cannot say which government caused which part. That is what
`Theory/Mechanism/ContinuationProfile.lean` is for.

**A caution about "same-α" theorems.** Comparisons such as
`equilibriumTop_dynamicTopSanctions_ge_myopify_same_alpha_...` hold the Target's
policy *fixed* while toggling the Sender's continuation. That is a partial
exercise, not a regime comparison: with a different Sender response, a myopic
Target's own optimum moves too. Do not cite a same-α theorem as a `01` versus
`00` result.

---

## Summary table

| | adversarial | continuation active | off-corner rule | interaction |
|---|---|---|---|---|
| `ceParams` | **no** — Target gains from sanctions | **yes**, exactly | interior, rests at `3/4` | no |
| P3 | yes | numerically | yes | no |
| `niParams` | — | **no** — both values zero | **yes**, non-affine | no |
| `OffCornerNonVacuity` | — | no | yes | no |

The gap the mechanism program is aimed at is one economy with the first three
columns simultaneously, plus the fourth. See
`suggestions/abstract-two-sided-forward-looking/34_...` for the specification
and `docs/REVISION-PLAN-2026-08-28.md` for how it sequences.

---

## A numerical finding about the four-regime program (2026-08-29)

Script archived at `docs/archive/workflow-scratch/interaction-sweep-2026-08-29.py`.
Rule 9C: it searched, and it justifies nothing.

The plan was to read the sign of the two-channel interaction
`I_R = R¹¹ − R¹⁰ − R⁰¹ + R⁰⁰` numerically before committing to a Rule 3
sign-off on the complementarity class. **No reading was obtained**, and the
reason is itself the finding.

On a freshly designed genuine-conflict economy — sanctions strictly harm the
Target, convex compliance cost, bilinear-rally Sender, affine transition — the
two regimes in which the **Sender** is forward-looking (`01` and `11`) do not
converge under deterministic best-response iteration. The regimes with a myopic
Sender (`00`, `10`) converge cleanly, in 2 and 109 iterations.

The diagnostics distinguish the three outcomes Rule 9D asks to be kept apart:

* **It cycles; it does not diverge.** Over the last 100 iterates the residual
  stays inside `[0.226, 0.619]` — bouncing, not growing.
* **Damping does not fix it.** Damping from `0` to `0.9` shrinks the value step
  (residual `0.44 → 0.019`) while the *policy* oscillation stays at `0.66`–`1.00`
  — at `damp = 0.5` the policy swings the full action range between iterates.
  Damping the values does not stop the argmax flipping, which is the signature
  of a policy cycle rather than an unstable value recursion.
* **Impatience does not fix it.** At `β = 0.30` it still cycles (oscillation
  `0.562`). So it is not a contraction-modulus problem.
* **The oscillation is not a grid artifact.** A swing of `0.94` is across nearly
  the whole action interval, not between adjacent grid points.
* **The rally term drives it.** Scanning the sanction–state complementarity
  coefficient `r`: at `r = 0` the residual falls to `3.9 × 10⁻³` and the
  oscillation to `0.087`; every `r > 0` cycles hard. With heavy damping at
  `r = 0`, three of the four regimes converge to `10⁻⁸` and `01` still holds at
  `6 × 10⁻⁴`.

**What this is not.** It is not evidence that no such economy exists — Rule 9D,
clause 1, and only a Lean refutation could settle that. It is evidence about the
*game*: at these configurations the deterministic four-regime system appears to
have no pure fixed point, which is the same wall P3 hit
(`MechanismWitness.lean`: *"true order-reversal cycle, numerically confirmed"*).
That it reappears in an independently designed economy makes it look structural
rather than particular to P3.

**What it means for the program.** Doc 34's requirement that *"all four regimes
are actual equilibria"* is harder than it reads, and the difficulty is
concentrated in exactly the regimes the mechanism paper needs. Worse for the
narrative: the coefficient whose positivity breaks convergence, `r`, is the
sanction–state complementarity — the very feature that gives the Sender a
reason to invest in entrenchment. On this evidence the mechanism's interest and
its tractability move in opposite directions.

That does not close the route. It says the route runs through purification, or
through a subclass where the complementarity is weak enough to keep a pure fixed
point — and doc 34 restricts purified constructions sharply. Either way the
question should be settled before a Rule 3 sign-off, not after.

---

## The standing rule

None of these economies licenses a universal, a genericity claim, or a causal
attribution. Where the paper wants to say the mechanism operates, the honest
forms are *"there exists an economy in which …"* or *"our witnesses have …"* —
scoped in the manuscript's own prose, not only in a Lean docstring.
