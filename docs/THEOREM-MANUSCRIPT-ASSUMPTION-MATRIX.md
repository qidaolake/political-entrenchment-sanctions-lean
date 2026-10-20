# Theorem–manuscript assumption matrix

**Purpose.** For each long-run claim, what the Lean assumes against what the
manuscript states. The matrix exists because "no new assumption" can be true in
Lean and misleading in the paper at the same time: a predicate that is already in
the project widens nothing in `Params`, and still widens the paper-facing surface
of whatever claim now depends on it.

**Created 2026-08-15**, after review found exactly that: the order-selection
theorems assume `DynamicArgmaxUnique`, which is a long-standing project predicate
but is neither a field of `SenderPersistencePackage` nor an assumption of the
manuscript's current long-run proposition.

---

## Legend

| Symbol | Meaning |
|---|---|
| ● | assumed |
| ○ | not assumed |
| ▲ | derived inside the theorem from another listed assumption |

`R` is the realized equilibrium sanction rule `x ↦ σ_dyn_top V_S x (α x)`;
`G(x) = F(x, R x)` is the closed loop.

---

## The long-run claims

| | `prop:longrun` (baseline) | C1 tier 1 | C1 tier 2 | C1 tier 3 | endpoint attraction | threshold pair |
|---|---|---|---|---|---|---|
| **Lean backing** | `dynamicTopLockInPathF_tendsto_steadyState` | `..._of_continuousOn` | `..._and_rule_limit` | `equilibriumTop_tendsto_order_selected_fixedPoint` | `equilibriumTop_tendsto_right_endpoint` | `equilibriumTop_threshold_separates_basins` |
| Continuity of the Target policy `α` | ● (`hα_cont`) | ● (via `E.hα`) | ● | ● | ● | ● |
| Basin level condition (sanction floor) | ● | ○ | ○ | ○ | ○ | ○ |
| Monotonicity of `R` on the basin | ○ | ● | ● | ● | ● | ● |
| Continuity of `R` on the basin | ○ | ● | ▲ | ▲ | ● | ▲ |
| `DynamicArgmaxUnique E.V_S` | ○ | ○ | ● | ● | ○ | ● |
| Interval inside the physical state space (`0 ≤ a`, `b ≤ 1`) | ● | ○ | ● | ● | ● | ● |
| Invariance of the basin under `G` | ▲ (from the floor) | ● | ● | ● | ● | ▲ (from the sign conditions) |
| `StrictAdjustment` (F5) | ○ | ○ | ○ | ● | ● | ● |
| Strict sign condition on `R − id` | ○ | ○ | ○ | ○ | ● | ● |
| Endpoints fixed by `R` | ○ | ○ | ○ | ○ | ▲ | ● |
| **Limit named?** | no | no | no | no | yes | yes |
| **Sanction limit** | subsequential, optimal at the state limit | `R(x*)` | `R(x*)` | `x*` | endpoint | — |
| **Common limit for the whole basin?** | no | no | no | no | **yes** | **yes, each side** |

---

## What the matrix is for

**1. The baseline is not dominated.** `prop:longrun` assumes strictly less about
the realized rule — no monotonicity, no continuity, no argmax uniqueness — and
concludes strictly less. The order-selection tiers are a sharper conclusion under
more regularity, not a strengthening of the same statement. Any manuscript text
presenting one as a corollary of the other is wrong, in either direction.

**2. `DynamicArgmaxUnique` is a paper-facing addition even though it is not a Lean
addition — and the Rule-3 position depends on what you are doing with it.**

* *Adding the theorems to the tree*: no Rule-3 stop. `DynamicArgmaxUnique` is an
  existing predicate carried by the standard compliance certificates, so `Params`
  is untouched and no headline hypothesis changed.
* *Promoting tier 1 to the headline set*: **Rule 3 and Rule 18 both apply.** The
  headline declaration set is itself load-bearing, and the promotion puts
  continuity of the realized rule on the paper-facing surface.
* *Promoting the refinement into the manuscript*: **Rule 3 and Rule 21 both
  apply**, for the same reason.

Both promotions were put to the author and approved on 2026-08-15, with the
packet recorded in §"Approved Rule-3 additions" below. Tier 1 exists so the paper
can separate the mathematical requirement — continuity of `R` — from the economic
condition that happens to supply it.

**2a. Tier 2's trade is not one-for-one.** It drops the continuity hypothesis and
picks up `DynamicArgmaxUnique` *together with* `0 ≤ a` and `b ≤ 1`, because argmax
uniqueness is stated at physical states and the interval must lie among them.
Hence the separate row above.

**3. Where "attractor" is licensed.** Only the last two columns. A common limit
for a whole basin is *equivalent* to uniqueness of the rest point in that basin
(`MonotoneAttraction.attraction_iff_unique_fixedPoint`), and equivalent again to
the strict sign condition
(`MonotoneAttraction.unique_fixedPoint_iff_strictly_signed`). So the word may be
used exactly where one of those has been established, and nowhere else. Local
isolation of the candidate limit does not qualify
(`isolated_fixedPoint_insufficient_for_attraction`) — and note the scope of that
witness: it attracts most of its interval, just not all of the interval claimed.

**3a. The equivalence is stated over the closed-loop state map `G`, not over the
sanction rule `R`.** Its sign condition is on `G x − x`. Transferring the sign to
`R x − x` is one-directional on the maintained fields — `R x ≥ x ⟹ G x ≥ x` from
`F_diag` and `F_mono_s` — and the converse needs `StrictAdjustment`
(`diagonal_and_sanction_monotone_insufficient_for_strict_step` refutes it
without). Any manuscript sentence phrasing the equivalence in sanction language
must carry that bridge.

**3b. The equivalence aims the search; it does not end it.** "Any sufficient
condition must imply basin uniqueness" leaves open the work of *deriving*
uniqueness from primitives rather than assuming it or assuming the full sign
pattern. That is the S6 target.

**4. `F` is never restricted in functional form.** Four of the six columns assume
`StrictAdjustment`, which is a structural sign condition on the transition and is
not supplied by any persistence package. The manuscript's wording should be: *no
functional form or numerical calibration is imposed on `F`, beyond the maintained
feasibility, continuity, monotonicity and diagonal conditions* — and, where it
applies, strict directional adjustment.

---

## The derived-interval claims (added 2026-08-15)

A second family, added after the order-selection round. These end the interval at
the **least** steady state above the pivot rather than at a state chosen in
advance, which is what lets them deliver a *common* limit rather than order
selection.

| | **derived-interval attraction (invariance form)** | derived-interval attraction (level-condition form) | derived-interval attraction (argmax form) | positive length | non-vacuity witness |
|---|---|---|---|---|---|
| **Lean backing** | `equilibriumTop_attraction_on_derived_interval_of_invariant` | `..._of_continuousOn` | `equilibriumTop_attraction_on_derived_interval` | `fixedPoint_gt_pivot_of_stepF_ne` | `dualParams_derived_interval_nonEmpty` |
| Continuity of the Target policy `α` | ● (via `E.hα`) | ● | ● | ○ | ● |
| Basin level condition (sanction floor) | **○** | ● | ● | ○ | ● |
| Monotonicity of `R` on the basin | ● | ● | ● | ○ | ● |
| Continuity of `R` on the basin | ● | ● | ▲ | ○ | ▲ |
| `DynamicArgmaxUnique E.V_S` | ○ | ○ | ● | ○ | ● |
| Interval inside the physical state space | ● (`0 ≤ x̄` only, for the sanction half) | ● | ● | ○ | ● |
| Invariance of the basin | **● assumed directly** | ▲ (from the level condition) | ▲ | ○ | ▲ |
| `StrictAdjustment` (F5) | ● (sanction half only) | ● | ● | ○ | ● |
| Uniqueness on the derived interval | ▲ **by construction** (leastness) | ▲ | ▲ | – | ▲ |
| Closed loop does not fix the pivot | ○ | ○ | ○ | ● | ▲ (from a floor above the pivot) |
| **Common limit for the whole interval?** | **yes** | **yes** | **yes** | – | **yes** |
| **Interval has positive length?** | not claimed | not claimed | not claimed | yes | yes |
| **Steady state interior (`x_s < 1`)?** | **not claimed** | not claimed | not claimed | – | **no — it is the corner** |

### Three cautions this family needs

**1. Attraction and positive length are priced separately.** The attraction rows
assume nothing the paper does not already hold. Positive length is an *extra*
condition, and the obvious economic route to it — a sanction floor strictly above
the pivot — is **unavailable on the persistence package's own basin**, because
`SenderPersistencePackage.toSenderPersistenceBasinTop` sets pivot and floor both
to `max xT xS`. There, positive length reduces to strict persistence at the
pivot, which is open. It is available at the dual-basin economy, whose
corner-pinned rule gives a floor of `1` against a pivot of `19/20`.

**2. Nothing here licenses the word *interior*.** No theorem establishes
`x_s < 1`, and at the one economy where positive length is witnessed, `x_s` **is**
the corner. The manuscript should say *attraction on a derived interval*.

**3. What the impossibility result actually refutes.** Monotonicity of the
realized rule and the weak level condition do not exclude a second steady state in
an interval specified in advance
(`persistence_consequences_insufficient_for_basin_uniqueness`). Whether the full
persistence package yields further restrictions is **open** — no complete `Params`
economy satisfying every field with two rest points in a claimed interval has been
constructed.

### Promoted 2026-08-15

**N36 is in the manuscript** as `prop:derived-interval` in `\Cref{sec:results}`,
on the author's Rule-21 approval, together with the Rule-3 disclosure it carries —
continuity of the realized rule on a second paper-facing claim.

Its backing is the **invariance form**, matching the proposition's stated
hypotheses exactly. The level-condition form previously recorded here was
stronger than the proposition, which was a Lean–paper mismatch; it is now a
corollary.

### Promoted 2026-08-15 (later) — N37, the derived dividing line

**N37 is in the manuscript** as `prop:derived-dividing-line` in
`\Cref{sec:mechanism:bistability}`, on the author's Rule-21 decision, together
with **headline row 36** for its Lean backing — the paper claim and the
drift-fenced theorem promoted in the same act. The general form is
`prop:derived-crossings` in `\Cref{app:derived-dividing-line}`.

It replaced the manuscript sentence *"the theorem does not identify the dynamics
between the two basins"*, which the result makes false. That was a Rule-2
fix-in-place, not a promotion.

| | derived dividing line |
|---|---|
| **Lean backing** | `equilibriumTop_derived_dual_basins` (headline row 36) |
| **Backing for the displayed `inf`/`sup` formulas** | `leastWeakAbove_spec`, `greatestWeakBelow_spec` — see note below |
| **Manuscript** | `prop:derived-dividing-line`; general form `prop:derived-crossings` |
| Continuity of the realised rule on the interval | ● |
| Monotonicity of the realised rule | **○ — not required anywhere** |
| Sign of the closed-loop gap in the middle region | **○ — not required** |
| Two endpoint readings (erodes at `x̄_L`, builds at `x̄_H`) | ● |
| Both named long-run states fixed by the closed loop | ● |
| Feasibility bounds on the closed loop (from `F_mem`, derived since round BC) | ● |
| `StrictAdjustment` (F5) | **○ — not required** |
| Level condition / sanction floor / persistence package | ○ |
| **Common limit below the lower crossing?** | **yes** |
| **Common limit above the upper crossing?** | **yes** |
| **Crossings proved to coincide?** | **no — reported as a gap, and the manuscript says so** |
| **Middle region fully classified?** | **no** |

The last two rows are the ones a reader will assume the wrong way round, which is
why the proposition's first qualification states the gap explicitly.
`derivedThresholds_can_differ` shows the gap is a genuine feature of continuous
maps, not slack in the proof.

**The backing is in two parts, and the split matters.**
`equilibriumTop_derived_dual_basins` is stated **existentially** — *there exist*
steady states `t ≤ t'` with these properties. It does not itself say that `t` is
the infimum of the non-eroding set. The manuscript displays those formulas, and
what licenses them is `leastWeakAbove_spec` / `greatestWeakBelow_spec`, which are
stated about the **named** objects `leastWeakAbove` and `greatestWeakBelow` rather
than existentially, and which are exactly what `prop:derived-crossings` in the
appendix reproduces. The manuscript route is therefore: general proposition (named
objects) → substitute `G = G_E`. The appendix says so in those terms.

A reader auditing row 36 alone would find the limits and the ordering but not the
identification. That is not a defect in the row — it is why the appendix
proposition is stated at the abstract level rather than folded into the
equilibrium statement.

**Nothing is held and nothing is staged.** N38 — announcing the result in the
introduction and abstract — was promoted on 2026-08-16 on a separate decision.
Both front-matter clauses say the derived steady states *bracket* the dividing
line, matching the "crossings proved to coincide? **no**" row above; neither
asserts a single crossing.

---

## Maintenance

Regenerate this matrix whenever a long-run claim is added, promoted, or has its
hypotheses changed. A row that appears in the Lean and not in the manuscript is
the failure mode this file exists to catch.

---

## Submission gate

Before the final language pass, all of the following must hold. Ticked boxes were
verified on the date shown.

**This block has recorded a stale headline count twice** — it read `33/33` while
the set held 34, and `34 rows` while the set held 35. Both were documentation lag
behind an approved addition, not a missing approval; but the count is exactly what
this file exists to keep honest, so it is now stated with the verifying run's own
figure rather than retyped.

- [x] Lean clean rebuild from an emptied `.lake/build`, six gates green
      *(2026-08-15, 35 rows)*.
- [x] `#print axioms` clean on every headline theorem: `propext`,
      `Classical.choice`, `Quot.sound` only *(2026-08-15, **35/35** replayed
      in-build)*.
- [x] Rule-18 headline declaration set approved by the author. The current 35-row
      set is covered by a chain of three acts, recorded separately because they
      are not the same act:
      1. sign-off on the **34 rows as a whole** *(2026-08-15)*;
      2. row 34 (`equilibriumTop_attraction_on_derived_interval_of_invariant`)
         approved as an addition *(2026-08-15)*;
      3. row 35 (`equilibriumTop_derived_dual_basins`) approved as an addition
         *(2026-08-15)*, promoted in the same act as the manuscript claim it
         backs.

      The chain is authoritative for the live set because the snapshot diff for
      act 3 was **one row added, none removed, and no existing elaborated-type
      hash changed** — so the 34 rows signed off in act 1 are provably the same 34
      rows today.

      **Not taken, and not required by Rule 18:** a fresh whole-set review of all
      35 rows as a single act. If the author wants one before submission it is a
      separate decision; the gate does not block on it.
- [x] This matrix regenerated, with a row for every long-run claim the
      manuscript makes *(2026-08-16)*.
- [x] *(2026-08-15)* No use of *attractor*, *globally stable*, or *bistable* anywhere a
      corresponding uniqueness result has not been established. By
      `attraction_iff_unique_fixedPoint` this is checkable: the word requires a
      proved unique rest point in the claimed basin.
- [x] *(2026-08-15)* No occurrence of *completely general* `F`. The correct wording is: **no
      functional form or numerical calibration is imposed on `F`, beyond the
      maintained feasibility, continuity, monotonicity and diagonal conditions**
      — plus strict directional adjustment wherever a result assumes it.
- [x] *(2026-08-15)* No novelty claim for extremal fixed-point selection;
      Amann (1976) cited.
- [x] *(2026-08-16)* Split and combined paper builds, zero undefined references
      and citations. Manuscript 29 pp, appendix 46 pp, formal supplement 27 pp,
      notes 16 pp; combined 72 pp. *(The figures recorded here on the morning of
      2026-08-16 — 28/45/72/17, omitting the supplement — predated that day's
      writing pass and no longer matched the verifying run. Restated from the
      run itself, as the block above requires of the row count.)*

Only then the language pass.
