# Enough Lean to read this development

For a reader who knows economics and no Lean. This is not a Lean tutorial —
it covers only the constructs this repository actually uses, and stops there.
Roughly fifteen minutes.

The one thing to hold onto: **a Lean theorem is a sentence, and the machine has
checked it is true.** Everything below is about reading the sentence.

---

## 1. Structures: a model is a record

```lean
structure Params where
  δ : ℝ
  δ_mem : δ ∈ Set.Ioo (0 : ℝ) 1
  F : ℝ → ℝ → ℝ
  F_diag : ∀ x, F x x = x
```

Read this as: *an economy consists of a number `δ`, a proof that `δ` lies
strictly between 0 and 1, a transition function `F`, and a proof that `F x x =
x`.*

A structure mixes two things an economist keeps apart: **objects** (`δ`, `F`)
and **assumptions about them** (`δ_mem`, `F_diag`). In Lean an assumption is
just another field, whose value is a proof. So `Params` *is* the model and its
maintained assumptions, together.

If `p : Params` — "let `p` be an economy" — then `p.F` is its transition and
`p.F_diag` is its proof that a matching sanction reproduces the state.

`ℝ → ℝ → ℝ` is a function of two real arguments. `U_S : ℝ → ℝ → ℝ → ℝ` takes
three: state, compliance, sanction.

## 2. Sets and intervals

| Lean | Means |
|---|---|
| `Set.Icc 0 1` | the closed interval `[0,1]` |
| `Set.Ico 0 1` | `[0,1)` — right endpoint **excluded** |
| `Set.Ioo 0 1` | `(0,1)` — both excluded |
| `Sanctions.I` | `[0,1]`, used for actions |
| `Sanctions.S` | `[0,1]`, used for the state |

`Sanctions.S` is defined as `abbrev S : Set ℝ := I` — it is **literally the
same set** as `I`. The two names track intended use, not different objects.
And `S` is the **state** space; it does not mean "sanctions".

Which endpoint is excluded is often substantive. `β_T ∈ Set.Ico 0 1` excludes
`β_T = 1` because the Bellman operator would stop being a contraction and the
value function would not exist.

## 3. Quantifiers

```lean
∀ x ∈ Set.Icc xbar 1, max x sbar ≤ p.dynamicTopRealizedRule V_S α x
```

*For every state `x` in `[x̄, 1]`, the realised sanction rule at `x` is at least
`max(x, s̄)`.*

`∃ E, P E` is "there exists an `E` such that `P E`". When you see `∃`, the claim
is existential and stays existential — see [READING-TRAPS.md](READING-TRAPS.md),
which opens with this.

`⟨a, b⟩` is anonymous-constructor notation: it packages the pieces of an `∃` or
an `∧`. `⟨h1, h2, h3⟩` supplies three components at once. You can skip past
these when reading a statement; they appear in proofs.

## 4. `fun` is λ

`fun s => p.U_S x a s` is "the function sending `s` to `U_S(x,a,s)`". It is how
you say "hold `x` and `a` fixed and vary the sanction".

## 5. `IsMaxOn` — how "argmax" is spelled

```lean
IsMaxOn (fun s => U_S x a s) (Set.Icc (0:ℝ) 1) (σ x a)
```

*`σ(x,a)` maximises `U_S(x,a,·)` over `s ∈ [0,1]`.*

The order is `IsMaxOn f A a` = "over the set `A`, `f` is maximised at `a`".

**`IsMaxOn f A a` does not assert `a ∈ A`.** It says only that no point of `A`
beats `a`. Feasibility is always a separate claim — which is exactly why
`Params` carries `σ_mem` (`σ x a ∈ [0,1]`) *next to* `σ_isMaxOn_U_S`. Two
fields, two jobs.

## 6. `→ᵇ` — why value functions live in a funny type

```lean
V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ
```

*`V_S` is a bounded continuous real-valued function on the state space `[0,1]`.*

`↥` just says "the set `[0,1]` viewed as a type"; ignore it. The `→ᵇ` matters
economically: bounded continuous functions on a compact set form a **complete
metric space**, which is what lets the Bellman operator be a contraction and
have a unique fixed point by Banach. The value function is not assumed to
exist here — it is *constructed*, and this type is where the construction
lives.

## 7. Monotonicity

| Lean | Means |
|---|---|
| `Monotone f` | `f` is weakly increasing, everywhere |
| `MonotoneOn f A` | weakly increasing on the set `A` |
| `StrictMonoOn f A` | strictly increasing on `A` |
| `Antitone f` | weakly decreasing |

`Monotone` never means "monotone in some direction" — it means non-decreasing.
Applied to a date-indexed sequence, `Monotone (dynamicTopLockInSanctionsF …)`
**is** the ratchet claim: sanctions never fall.

## 8. Theorem signatures

```lean
theorem foo (p : Params) (h : P p) : Q p := by ...
```

Everything before the final `:` is a hypothesis; the thing after it is the
conclusion. `(h : P p)` is "assume `P p`". Named hypotheses conventionally
start with `h`.

Curly braces `{p : Params}` mean the argument is inferred rather than written
out. Economically there is no difference. Double braces `⦃x : ℝ⦄` are the same
story; read them as ordinary `∀`.

## 9. Namespaces, and one genuine ambiguity

Declarations live in namespaces. Inside a file that has opened
`Sanctions.AbstractGame.Params`, the theorem written `foo` is really
`Sanctions.AbstractGame.Params.foo`. The snapshot in `HEADLINE-SNAPSHOT.md`
records the long form.

This creates the one notational trap worth learning: **`p.something` is
ambiguous by eye.** It is either

- a *field* of the structure — `p.F`, `p.δ`, `p.U_S`, `p.β_T_mem`; or
- a *theorem in the `Params` namespace applied to `p`* — `p.dynamicTopLockInPathF`.

Only the `structure Params` field list tells you which. If it is not in that
list, it is derived.

## 10. Two words with no mathematical content

`noncomputable` means "not intended to be run as a program". It says nothing
about the mathematics. `clipS'`, wrapping arguments as `V_S (clipS' (p.F x s))`,
is a type-level certificate that the argument lies in the domain — the theorem
`F_mem` (a field until round BC, 2026-09-29; now derived from monotonicity and
the fixed diagonal) already guarantees it economically. Neither is an assumption.

## 11. `sorry`

`sorry` is Lean's "assume this without proof". A file containing one still
builds, which is why it is dangerous.

**There are none here.** No `sorry`, no `admit`, no project `axiom` across
more than 5,000 declarations — gate 3 of `scripts/Audit-Round.ps1` greps for
those three on every audit round. (`native_decide` is also absent, but that is
a fact rather than something gate 3 currently checks — see
`docs/LEAN-STRUCTURE-PLAN.md`.) The three literal occurrences of the string "sorry" in the source are
inside prose comments.

---

## 12. A full theorem, dissolved

Here is a headline theorem, row 30 of the snapshot, from
`Sanctions/Examples/SymbolicCertifiedFamilyGeneralFPersistence.lean`:

```lean
theorem persistence_generalF :
    ∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop,
      Eq.V_T ∈ E.carrierT
      ∧ Eq.V_S ∈ E.carrierS
      ∧ ∀ x₀ ∈ Set.Icc E.xb 1,
          (∀ n, E.toParams.dynamicTopLockInPathF Eq.V_S Eq.α x₀ n
                  ∈ Set.Icc E.xb 1) ∧
          (∀ n, E.xb ≤ E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀ n) ∧
          Monotone (E.toParams.dynamicTopLockInSanctionsF Eq.V_S Eq.α x₀)
```

Line by line:

| Lean | English |
|---|---|
| `theorem persistence_generalF :` | The claim is named `persistence_generalF`. It takes **no hypotheses** — everything before the `:` is empty, so it holds for any `E` in the family. |
| `∃ Eq : …FeedbackStackelbergEquilibriumTop,` | There **exists** an equilibrium `Eq` — a Target policy and two value functions satisfying their Bellman equations, with the Target's action optimal at every state. |
| `Eq.V_T ∈ E.carrierT ∧ Eq.V_S ∈ E.carrierS` | Both of its value functions lie in the regularity classes the economy's own coefficients define. |
| `∀ x₀ ∈ Set.Icc E.xb 1,` | For **every** starting state in the high basin `[x̄, 1]` — one equilibrium serves all of them. |
| `∀ n, …dynamicTopLockInPathF … x₀ n ∈ Set.Icc E.xb 1` | At every date `n`, the political state is still in the basin. *Basin invariance.* |
| `∀ n, E.xb ≤ …dynamicTopLockInSanctionsF … x₀ n` | At every date, the realised sanction is at least the basin pivot. *The floor.* |
| `Monotone (…dynamicTopLockInSanctionsF … x₀)` | The realised sanction sequence never falls. *The ratchet.* |

In one sentence: *for every admissible member of this family there is an
equilibrium, built from the economy's own coefficients, whose political state
never leaves the high basin and whose sanction never falls.*

The `F` at the end of `dynamicTopLockInPathF` is load-bearing and is the
subject of the first entry in [READING-TRAPS.md](READING-TRAPS.md). Read that
next.
