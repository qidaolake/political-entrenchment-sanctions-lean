# How to misread this development

Every entry below is a mistake a careful reader would make from the names
alone. They are collected here because the names are, in each case, either
historical, abbreviated, or stronger than what they label. None of them is a
defect in the mathematics; all of them are defects in what the mathematics
*looks like* at a glance.

Ordered by how much damage the misreading does.

---

## 1. A missing `F` means the result is affine-only — and nothing in the signature says so

`dynamicTopLockInStep`, `dynamicTopLockInPath`, `dynamicTopLockInSanctions`,
`ruleStep`, `rulePath`, `ruleSanctions`, `lockInStep`, `shockStep`, `shockPath`
all hard-code the affine law `(1−δ)·x + δ·rule` **in their bodies** and never
call `p.F`.

So a theorem stated over them is restricted to an affine transition **even
though it carries no `hF : p.F = affineF p.δ` hypothesis**. Grepping for `hF`
to find the affine surface returns a clean bill of health that is wrong. The
project's scope note asserted exactly that false version for many rounds; it is
now Rule 22, axis 2.

**The general-transition siblings end in `F`:** `dynamicTopLockInStepF`,
`dynamicTopLockInPathF`, `dynamicTopLockInSanctionsF`, `shockPathF`.

Conversely, `_generalF` in a *theorem* name means it uses the general-transition
machinery — **not** that the economy it is applied to has a non-affine
transition. Only three economies in the headline set are genuinely non-affine:
`qbParams`, `lbParams`, and the `SymbolicEconomyF` family.

## 2. Every witness theorem is existential, and stays existential

Every headline theorem whose name contains `three_goals`, `persistence`,
`witness`, or a witness prefix (`eeCert`, `qbCert`, `lbLow`, `b2`, `sfCert`,
`fourGroupCert`, `dualParams`, `mechanismWitness`) concludes

> **there exists** an equilibrium `E` such that …

Not "for every equilibrium". A witness licenses *"there is an economy in
which…"* and refutation of a universal — nothing else. Not "generically", not
"typically", not "the mechanism causes this". This is the project's Rule 9 and
it is the one place this project has historically over-claimed.

## 3. `σ` is not the equilibrium Sender response

`Params.σ` is the **myopic, static** stage rule: the sanction a Sender that
ignored the future would choose. It exists to be the *comparator*.

The equilibrium Sender response is `σ_dyn_top`, built downstream from the
Sender's continuation value `V_S`. Confusing the two collapses the paper's
central dynamic-versus-myopic comparison into a tautology. The source warns
about this three separate times in one file, which is a fair measure of how
easy the slip is.

## 4. `theorem2_dynamic_dominates_myopic_at_same_alpha` does not compare two equilibria

Its actual statement is

```lean
(V_S) (h_V_S_mono : Monotone V_S) (α : ℝ → ℝ) (x : ℝ) :
    p.σ x (α x) ≤ p.σ_dyn_top V_S x (α x)
```

`α` is an **arbitrary function** `ℝ → ℝ`. It is not required to be optimal for
anyone. The theorem compares the Sender's *stage* argmax with the Sender's
*forward-looking* argmax **at a common Target action**, holding everything else
fixed.

That is a clean statement of the wedge, and it is genuinely general in `x`. It
is not "the forward-looking equilibrium sanctions more than the myopic
equilibrium", and quoting it that way overstates it.

## 5. "Top" means *greatest selector*, never *top of the state space*

In `σ_dyn_top`, `dynamicTopRealizedRule`, `JointPreferenceBasinTop`,
`FeedbackStackelbergEquilibriumTop`, "Top" always means **the greatest element
of the argmax set** — the selection rule used when the best response is not
unique. It never refers to the state `x = 1`.

## 6. `IsMaxOn f A a` does not say `a ∈ A`

It says only that nothing in `A` beats `a`. Feasibility is always a separate
conjunct. This is why `Params` carries `σ_mem` beside `σ_isMaxOn_U_S`, and why
`dynamicArgmaxSet` conjoins membership with the maximality claim. A reader who
assumes membership is implied will misjudge which fields are load-bearing.

## 7. The certificates' `β_T` and `β_S` are not discount factors

In `StandardComplianceLocalCoreCertificate` and its `_MS` sibling, the fields
`β_T` and `β_S` are **row-Lipschitz moduli of the joint Bellman operators**.
The discount factors are `p.β_T` and `p.β_S`.

Both appear inside the same structure — `hS_margin` uses `p.β_S`, `hsuff_S`
uses the field `β_S` — and nothing forces them equal.

## 8. `Sanctions.S` is the state space

Not "sanctions". `abbrev S : Set ℝ := I`: it is literally the same set as
`Sanctions.I`, namely `[0,1]`. Three spellings (`Set.Icc 0 1`, `Sanctions.I`,
`Sanctions.S`) all appear in the source for one object.

## 9. "MS" in the certificate name is historical

`StandardComplianceLocalCoreCertificate_MS` carries `hIDO_on`, the
Quah–Strulovici **interval-dominance** condition, which is strictly *weaker*
than Milgrom–Shannon single crossing. The "MS" is a leftover.

Relatedly: the certificate has a field documented as "A1 MS-form" for the
Sender's *stage* margin, while the manuscript's Assumption A1 is the
interval-dominance *direction* condition. That docstring label conflates level
with direction; the newer `PersistenceCertificate.lean` labels the two fields
LEVEL and DIRECTION and flags the inherited name as not to be propagated.

## 10. At most witness economies the ratchet is satisfied by a constant

At `eeCert`, `qbCert`, `lbLow`, `sfCert`, `fourGroupCert` and the
`SymbolicEconomyF` family, the certified equilibrium has the Target defying
fully and the Sender at the corner, so the realised sanction is identically 1
(or identically 0 in the low-basin case). `Monotone` is then satisfied by a
**constant sequence**.

This is stated outright by `persistence_generalF_corner`, which pins `σ = 1`.
It is persistence, not escalation. Only a couple of headline witnesses have a
strictly interior realised sanction.

## 11. Goal 2 is statewise, not pathwise

The dominance conclusion compares the myopic *rule* against the dynamic *rule*
at each basin state. The pathwise version — "the myopic sanction path is
dominated at every date" — additionally needs `hMyoBasin`, that the myopic rule
preserves the basin, and that is **false at this project's bistable witnesses**;
there is an explicit counterexample.

## 12. Some negative-sounding names are the positive results

`jointPreferenceBasinTop_tail_no_relief` and its siblings are the *persistence*
theorems: "no relief cutoff is ever reached after basin entry" is the lock-in
claim itself, stated as an infinite first-passage time.

And `dynamic_stake_refutation_target_is_empty` does not mean a refutation was
found — it means the space where such a refutation could live is empty.

## 13. Route refutations are not proposition refutations

Much of the `Coupled*` and `LowDelta*` material refutes *a specific route* to a
proposition, not the proposition. `not_coupledTargetQuadraticGrowth`,
`not_coupledLeaderObj_*` and their neighbours refute properties **of the
current carriers**, and the files say so. They are evidence that the coupled
existence result is honestly stated as conditional — not evidence that coupled
equilibria fail to exist.

## 14. "Local" means carrier-local

In `StandardComplianceLocal`, "local" means the fields are quantified over the
value **carrier** (`∀ V_T : D.CarrierT, ∀ V_S : D.CarrierS`). It does not mean
local in the state, and it does not mean per-equilibrium. The file notes this
is not a pure weakening of the older per-equilibrium form — the two quantify
over different families.

## 15. `δ` is a free scalar under a general transition

`Params.δ` is documented as the weight in `x' = (1−δ)x + δs`, but **no field of
`Params` connects `δ` to `F`.** None of `F_continuous`, `F_mono_x`,
`F_mono_s`, `F_diag` mentions it (nor the theorem `F_mem`, a field until round BC). The documented formula is true only when a
theorem separately supplies `hF : p.F = affineF p.δ`.

So `δ` is a mandatory field of every economy including the non-affine
witnesses, where it has no transition interpretation. The legacy margin
`hS_margin : β_S·K_S·δ < m_S` prices it even under a general `F`; the general-`F`
route drops it and uses the transition-adjusted chord
`β_S·K_S·|F(x,s₂) − F(x,s₁)| < ΔU_S` instead.

Measured 2026-08-11: the four general-`F` headline theorems read `δ` **zero**
times. It is retained rather than removed because three things genuinely use
it — the closed-form shock horizon, the comparative statics in the adjustment
rate, and the legacy affine routes — and because deleting the field would
relocate the assumption into 195 declarations across 68 files rather than
eliminate it. The field docstring now says all of this at the definition site.

## 16. The parametric layer of `SenderPersistence.lean` is not an economic claim

Its theorems quantify over an **arbitrary** Target policy `α`, so the
trajectory they describe need not be an equilibrium path. The docstrings say
so: *"Kinematic layer — internal. Not an economic statement… Do not cite it for
an economic claim."*

Only the `equilibriumTop_*` siblings, which take an actual
`FeedbackStackelbergEquilibriumTop`, are economic statements. Every consumer in
the repository routes through those.

## 17. The equilibrium concept is weaker than "Stackelberg" suggests

`FeedbackStackelbergEquilibriumTop` is a Markov-feedback fixed point: the
leader's action is optimal **pointwise in the state, over actions, against
frozen continuation values**. A leader deviation is never met by a Sender
re-solve. No theorem in the tree establishes optimality over alternative
stationary leader policies. The docstring and the paper's scope paragraph say
this; the name does not.

---

## The two that cost the most

If you remember only two, make them **#1** (a missing `F` is an invisible
affine restriction) and **#2** (witness theorems are existential). Those are
the two that turn a correct theorem into an incorrect sentence, and both have
caught this project before.
