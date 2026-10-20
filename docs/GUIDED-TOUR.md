# A guided tour of the formalization

For a reader who has read the paper and wants to know what the machine actually
checked. It assumes economics and no Lean.

Read [LEAN-PRIMER.md](LEAN-PRIMER.md) first if you have never seen Lean — it is
about fifteen minutes and covers only what appears here. Read
[READING-TRAPS.md](READING-TRAPS.md) before quoting anything.

The development is 119,000 lines across 249 modules. **You need about ten of
them.** This document says which, and why.

---

## 1. The claim in one paragraph

Sanctions entrench the political faction that benefits from them. If that
feedback is strong enough, a high-sanction regime sustains itself: the Sender
keeps sanctioning because the political state makes it worthwhile, and the
Target keeps defying because compliance no longer pays. The formalization
checks that this is a genuine equilibrium phenomenon and not an artifact of
assuming what you want to conclude — every strategy is derived as an
optimisation result, and the machine verifies each theorem down to the kernel.

## 2. What the model assumes: 499 lines

This is the number to start with. The entire primitive environment is
`Sanctions/Postulates/`, two files, 499 lines — **0.4% of the source**.
Everything else is derived from it plus mathlib.

`AbstractGame.Params` has exactly **20 fields**. A state `x ∈ [0,1]` measures
entrenchment of the hardline faction; the Target picks compliance `a ∈ [0,1]`;
the Sender picks a sanction `s ∈ [0,1]`; the state evolves as `x' = F(x,s)`.

**Objects (7).** `δ`, `β_T`, `β_S`, the two stage payoffs `U_T` and `U_S`, the
Sender's static stage rule `σ`, and the transition `F`. The payoffs are
abstract function fields — no closed form is imposed anywhere in the theory
layer.

**Ranges and feasibility (5).** `δ ∈ (0,1)`, `β_T, β_S ∈ [0,1)`, `σ` lands in
`[0,1]`, and `F` maps `[0,1]²` into `[0,1]`. The half-open discount intervals
are what make the Bellman operators contractions; `β = 1` is excluded because
the value function would not exist.

**Continuity (4).** `U_T`, `U_S`, `σ`, `F` are jointly continuous. This is not
only technical: boundedness of the payoffs is **derived** from continuity on
the compact cube rather than assumed. Two earlier boundedness fields were
deleted once that was noticed.

**Genuine economic content (4).** These are the ones a referee should argue
with:

| Field | What it says |
|---|---|
| `F_mono_s` | Heavier sanctions today weakly raise tomorrow's entrenchment. *This is the mechanism.* |
| `F_mono_x` | Power persists: more entrenchment today, weakly more tomorrow. |
| `F_diag` | `F x x = x` — a sanction equal to the state reproduces it. |
| `σ_isMaxOn_U_S` | The static rule is the Sender's stage argmax, not an assumed function. |

`F_diag` looks like a normalisation and is not. With the two monotonicity
conditions it yields no-overshooting: the next state always lies weakly between
today's state and today's sanction. **Persistence then reduces to showing the
equilibrium sanction does not fall below the state** — a materially easier
target, and the reason the basin argument works.

`σ_isMaxOn_U_S` is where the project's optimal-strategies-only discipline is
anchored on the Sender side: the stage rule is *derived*, so the myopic
comparator is a real optimiser rather than a strawman.

### What the primitives deliberately do not say

Three absences matter more than most of the fields.

**Compliance never enters the transition.** `F : ℝ → ℝ → ℝ` takes the state and
the sanction only. The Target cannot affect its own political future directly —
only by moving the Sender's sanction. That is a substantive modelling
commitment, and it is invisible unless you count the arrows in the type.

**There is no sign restriction on either payoff.** Nothing in `Params` says
sanctions hurt the Target or that the Sender dislikes defiance. Preference
structure enters downstream, as per-theorem hypotheses and certificate fields.
So "the assumption surface is 499 lines" is true and *understates* the
assumption load behind the headline results — the certificates carry more.

**`δ` is not tied to `F`.** No field connects them; see trap #15.

## 3. The spine: ten files

The flagship theorem is proved by ten modules, about 9,700 lines — under 5% of
the theory layer. In dependency order:

| # | Module | What it adds |
|---|---|---|
| 0 | `Postulates/AbstractGame.lean` | The 20 primitives above. |
| 1–2 | `Theory/Bellman/BellmanT.lean`, `BellmanS.lean` | Each player's Bellman operator is a contraction on bounded continuous functions, so **each value function exists and is unique** — constructed by Banach, not assumed. |
| 3 | `Theory/Equilibrium/JointMPE.lean` | The Sender's *forward-looking* response `σ_dyn`: the argmax of stage payoff plus discounted continuation. This is the object the paper's comparison is about. |
| 4 | `Theory/Bellman/InvariantValueClass2.lean` | The **carrier** — see below — and the joint fixed point inside it. |
| 5 | `Theory/Basin/JointPreferenceBasin.lean` | **The keystone.** |
| 6–7 | `Theory/LockIn/DynamicTopLockIn.lean`, `LockIn.lean` | Trajectories: iterate the equilibrium rule through `F`, and the exogenous-shock path. |
| 8 | `Theory/LockIn/DifferentPolicyComparator.lean` | The dynamic-versus-myopic comparison. |
| 9–10 | `Theory/Certificates/StandardComplianceLocal.lean`, `StandardComplianceMain.lean` | Bundle the hypotheses into a certificate and state the paper-facing theorems. |

### Why a carrier (step 4)

A referee's natural question. Two Bellman operators, one per player, each
depending on the other's value function — so the equilibrium is a *joint* fixed
point, and there is no reason in general for joint best-response iteration to
converge. It can cycle.

The carrier is a restricted class of candidate value functions — bounded by
some `M`, Lipschitz with some constant, with a minimum slope — chosen so that
both operators map the class into itself and the pair contracts on it. Existence
is then Banach on the product. Without a carrier there is no fixed-point
argument available; the price is that every application must discharge carrier
membership, which is what the certificates do.

### The keystone (step 5)

A **joint preference basin** is a region `[x̄, 1]` of the state space where three
things hold together: the Sender's forward-looking argmax contains a point at or
above `max(x, s̄)`; that argmax moves weakly upward as the state rises; and the
Target's own objective favours higher sanctions on the relevant range.

From those, persistence is almost kinematics. The floor gives `s_t ≥ x_t`;
`F_mono_s` and `F_diag` then give `x_{t+1} = F(x_t, s_t) ≥ F(x_t, x_t) = x_t`,
so the state cannot fall out of the basin; and monotonicity of the response
turns a non-decreasing state path into a non-decreasing sanction path.

Note what the basin **is**: a hypothesis bundle, not something the model
produces. It must be discharged at each application. Calling it "the basin"
invites reading it as an output; it is an input, discharged from stage
primitives by the bridge lemmas.

### What P4 does, and does not, do

The Target-side condition (P4 in the paper) yields the conclusion that the
Target's complete objective favours higher sanctions — the two-sidedness of the
mechanism. It is **not** needed for the three kinematic conclusions. That
separation is now a theorem, not a reading:
`standardCompliance_persistence_generalF_from_sender_package` proves basin
invariance, the floor and the ratchet with P4 deleted from the hypotheses, and
`equilibriumTop_senderPersistenceF_long_run_with_evidence` adds both
optimality conclusions, still without P4.

Read carefully, though: what is dropped is any hypothesis about how the Target
*ranks sanction levels*. The Target's equilibrium policy is still there, and
still enters the Sender's objective. "The Sender alone sustains the path" would
be an overclaim.

## 4. What is proved

Thirty-two theorems are pinned in `HEADLINE-SNAPSHOT.md`, each with the hash of
its elaborated type and its axiom list. Every one depends only on `propext`,
`Classical.choice` and `Quot.sound` — the three standard axioms of Lean's
library — and on nothing else. There are no `sorry`s and no project axioms
anywhere in the development.

Broadly they divide into: persistence and lock-in at exhibited economies;
existence results; the dynamic-versus-myopic comparison; welfare results for
the four-group microfoundation; uniqueness within a carrier; and refutations.

Two structural cautions, both expanded in [READING-TRAPS.md](READING-TRAPS.md):
the witness theorems are **existential** in the equilibrium, and at most witness
economies the certified equilibrium sits at a corner, so the ratchet conclusion
is satisfied by a constant sanction sequence. That is persistence, not
escalation.

## 5. What is refuted — read this if you are sceptical

Around 55 declarations prove that something attractive is **false**. They are
the most credible material here, because each states a claim a reader might
well have believed and then kills it. A few:

- **Sign conditions are not enough.** There is an economy satisfying every sign
  condition in the model in which every equilibrium sanctions at zero forever
  and the state decays to zero — and it holds on a full-dimensional region of
  parameters, not at a tuned point. So the paper's qualitative story genuinely
  requires a magnitude comparison, not just directions.
- **The ratchet floor forces an absorbing top.** A floor `R(x) ≥ x` on a basin
  ending at `x = 1`, plus feasibility, forces `R(1) = 1` — so maximal ratcheting
  and a live Target continuation channel at the top state cannot be had
  together. This is proved five different ways in the tree.
- **Order-theoretic and contraction routes to interior existence fail**, each
  refuted separately, which is why the interior case is stated as open rather
  than as unfinished work.

Distinguish *route* refutations from *proposition* refutations — much of the
coupled-carrier material refutes a particular route and says so. Trap #13.

## 6. Where to stop reading

You do not need `Sanctions/Examples/` unless you want a specific witness: 93
modules, 44% of the source, of which the `LowDelta*`/`Coupled*` campaign alone
is 35 modules that the register records as **"No promotion"** — a documented
negative result, retained deliberately.

You do not need `Theory/Shocked/` unless you care about the purification route.
`Theory/Bridges/` is a mixed folder and worth one caution: some of its
theorems are deprecated (they are sign-correct only under a resistance reading
of compliance) while their sanctioned replacements sit in the same files and
are consumed by live certificate code. The deprecation is marked per
declaration, not per folder.

`Sanctions/Foundations/` — 48 modules of Stokey–Lucas–Prescott, Topkis,
Milgrom–Shannon, interval dominance, Berge — is external mathematics with no
sanctions content. It is separated precisely so you can check the citations
independently of the economics, and reuse it if you want to.

## 7. Verifying it yourself

```
lake exe cache get      # fetch prebuilt mathlib
lake build              # builds everything, including the axiom replay
```

`Sanctions/Headlines.lean` replays `#print axioms` for all 32 headline
theorems on every build, so the axiom set of every protected theorem is
recomputed from the kernel each time rather than trusted from a cached record.
Note precisely what that does and does not do: `#print axioms` emits an
*information* message, so it does not by itself fail the build. What fails a
round is gate 3 (which greps for `sorry`/`admit`/`axiom`) and gate 6 (which
checks every snapshot row still has a replay line). Reading the replay output
is how you check the axiom *set*; the gates are what make it mandatory.

`scripts/Audit-Round.ps1` runs six gates — toolchain pin, layer architecture,
`sorry`/axiom hygiene, build, snapshot stability, and replay coverage. The last
one exists because the first five once passed while six headline rows had
silently lost their axiom replay.
