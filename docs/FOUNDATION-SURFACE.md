# The Foundations surface

`Foundations/` is meant to hold reusable mathematics: theorems about dynamic
programming, monotone comparative statics, fixed points and convexity, each in a
file named after the source it comes from, checkable against its citation
without reading a line of the economics. This file records how far that is
actually true, measured rather than asserted.

The companion `FOUNDATION-DECLARATION-ROLES.csv` carries one row per top-level
declaration, as recognised by a source scanner — which is a real limit, not a
guarantee: until 2026-08-28 the scanner's pattern did not admit an attribute
prefix, so all 18 declarations written `@[simp] theorem ...` were absent and the
count read 621 instead of 639 (the surface is now 660). The pattern now admits attributes, `inductive`
and `opaque`, and a check against a differently-written scanner finds nothing
further missing — but an exhaustive inventory would have to come from Lean's
elaborated environment (`Batteries.getDeclsInPackage`), not from source text.

That gap never reached the hard gate. Gate 2 of `Audit-Round.ps1` scans each
stripped **file body** for the forbidden vocabulary and does not enumerate
declarations at all, so it could not have missed an attributed one; what the
scanner's blind spot cost was the accuracy of this manifest, not the soundness
of the Rule 19 check. Regenerate both with:

```powershell
powershell -NoProfile -File scripts/Generate-FoundationRoles.ps1
```

## Where it stands

| role | count |
|---|---:|
| `CORE` — reusable mathematics over abstract objects | 583 |
| `DOMAIN_LEAK` — statement is over the project's `[0,1]` | 77 |
| `GAME_LEAK` — statement names `Params` / `AbstractGame` / `affineF` | **0** |

`GAME_LEAK` must stay at zero. It is Rule 19's line: a declaration mentioning the
game structure is about *this* game and belongs in `Theory/`. Gate 2 of
`Audit-Round.ps1` fails the round if the count rises, so the claim is enforced
and not merely recorded here.

`DOMAIN_LEAK` is **expected, and is not a defect.** These 77 declarations
live in 10 modules:

- `BorelBoxLawVerification`
- `BoxPullback`
- `BoxTransfer`
- `ClosedLoopBoxTransfer`
- `DualKantorovichS`
- `FeynmanKacVerification`
- `IntervalDominanceOrder`
- `KrylovBogolyubov`
- `MovingAverage`
- `SemiconcaveRiccati`

They are reusable operator theory — moving-average and box-transfer kernels,
Kantorovich duals, Feynman–Kac and Krylov–Bogolyubov, the semiconcave Riccati
recursion — that happens to be *specialized to the unit interval*. They are not
domain adapters. Moving them into `Domain/` would put general mathematics into a
layer that exists to hold a modelling choice; generalizing them to an arbitrary
`Set.Icc l u` would change theorem statements and is a separate exercise.

This is why `Domain/` sits **below** `Foundations/` rather than above it. The
import records the specialization instead of leaving it implicit in whatever the
build prelude happened to define. What the arrangement buys is that the
dependency is visible and countable; what it does not buy — and what should not
be claimed — is that `Foundations/` is free of `[0,1]`. It is not.

## What a witness is doing if you find one here

Nothing, as of 2026-08-27: counterexamples, sharpness constructions, necessity
refutations and affine dischargers were moved to `Examples/` with a declared role
in each file header, and each surviving theorem points to where its evidence
went. A witness inside the library it certifies reads as part of the general
theory, which is exactly the confusion Rule 9 exists to prevent.

If a new one appears, it belongs in `Examples/` under the role that fits:
`NON_VACUITY`, `SHARPNESS`, `NECESSITY`, `FAILURE OF CONVERSE`,
`FUNCTIONAL-FORM ILLUSTRATION`, or `CERTIFICATE COMPUTATION`.

## How the layering is checked

Gate 2 of `Audit-Round.ps1` now walks the import graph and checks the true
closure of each layer root, rather than reading direct `import` lines and
arguing that per-file checks plus complete aggregators imply the closure. That
argument is sound here, but it couples two gates in a way that could break
silently, and the walk costs nothing.

It is deliberately **not** built on `lake env lean --src-deps`, even though that
is the obvious tool and the one the migration proposal prescribes for exactly
this job. Measured at the 4.29.1 pin on 2026-08-27: `--src-deps` prints *direct*
imports only. `Sanctions/Theory.lean` returns 108 Theory files and no
Foundations; `Sanctions/Foundations/Basic.lean` returns its single `Domain`
import and nothing beneath it. It is a dependency lister, not a closure. Using
it here would have restated the direct-import check while claiming to have done
more — the walk reaches 153 modules from `Sanctions.Theory` where `--src-deps`
reaches 108, and that gap is the whole point of the gate.

## A note on measuring this

The scan strips block comments **before** line comments, and the order is
load-bearing. Stripping `--` first decapitates every `/-- ` doc-comment opener,
after which the block stripper cannot find the region and documentation prose is
scanned as though it were code. Done in the wrong order on 2026-08-27, this scan
reported four Foundations files as mentioning `Params`; every hit was prose
*explaining* that they do not. `scripts/FoundationVocabulary.ps1` holds the one
correct implementation, shared by the generator and the audit gate so the two
cannot drift apart.
