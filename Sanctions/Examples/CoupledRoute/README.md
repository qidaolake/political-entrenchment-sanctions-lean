# The low-δ coupled-existence route

**35 modules, ~14,400 lines — and it did not succeed.** This directory is kept
deliberately, as a documented negative result. Read this before reading any
file in it, or you will mistake an abandoned route for a load-bearing one.

## What the route was trying to do

Everywhere else in this development, an equilibrium is either *constructed*
inside a carrier by a contraction argument, or *assumed* and its consequences
propagated. The gap the project would most like to close is a fully
**coupled** existence result: both players' value functions and both policies
solved jointly, at an explicit economy, with nothing assumed.

The obstacle is that the two Bellman operators depend on each other. Joint
best-response iteration is not a contraction in general and can cycle. So the
route needs the cross-coupling to be *weak enough* that a Perov / Banach
argument closes on the product space.

## Why low δ

`δ` is the adjustment rate: the weight the next political state puts on
today's sanction. In the affine instance, `x' = (1−δ)x + δ·s`.

**When `δ` is small the state barely moves within a period**, so each player's
continuation value is nearly insensitive to the other's current action. The
cross-Lipschitz terms shrink, and the contraction margins that are hopeless at
moderate `δ` can open up.

That is not a guess. The 2026-07-04 kernel-width audit proved the route-A
derivation of the leader-regularity primitive `h_obj_diff` is **quantitatively
impossible** at the P3 mechanism economy, where `δ = 1/5`: the admissible
window is empty there. The same audit showed the window *opens* as `δ` falls.

`LowDeltaWindowWitness.lean` is the positive result that follows. It builds the
**δ-only-modified P3 economy** — identical payoffs, identical discount factors,
identical basin, with `δ = 1/100` instead of `1/5` — and proves all four window
inequalities hold simultaneously with exact rational margins. That file is
real, and it is the reason the rest of the directory exists.

## What went wrong

From that window, the campaign tried to reach an unconditional coupled
equilibrium at an explicit economy. Four obligations stood in the way. **All
four now have route refutations in the tree**, and the register records the
outcome as *No promotion*:

| Obligation | Status |
|---|---|
| Carrier-local Target-selector uniqueness | Refuted along its natural route — two distinct global maximisers exist (`lowDeltaRelativePerturbationCounterexample_two_maxima`) |
| Sender objective-difference channel | Refuted (`not_coupledLeaderObj_sender_uniform_advertised`) |
| Sender-carrier preservation | Refuted (`coupledSteepPolicy_sender_image_not_mem`) |
| Target-policy centre-displacement bound | Reopened 2026-07-28 under a fresh budget, and **also refuted** |

The fourth is the instructive one. The proved slack is the exact rational
`2429552350098203266063975021 / 488157047875412353000038524160 ≈ 4.977 × 10⁻³`,
against a proved localisation of `69/200 = 0.345` — a required tightening of
about 69×. And that gap is unbridgeable *on this route*:
`gate2_localization_floor` exhibits a feasible action at `x = 1` satisfying the
project's own localisation inequality with displacement exactly `3447/10000`,
so no re-derivation from that inequality can go below `0.3447`; and `69/200`
already overshoots the governing quadratic's exact root by 0.07%. Separately,
`gate2_modulus_information_floor` shows a modulus-only argument cannot reach
the slack at **any** constant.

## The route also could not have reached its target (2026-08-13)

Everything above is about the *existence* half of the plan. A later check found
that the **second** half fails independently, at these stage payoffs:
`LowDeltaSubpivotChordObstruction.lean` proves that **P5** — the
transition-adjusted sub-pivot chord of
`Theory/Certificates/SenderPersistencePackage.lean`, which supplies the *level*
half of persistence — is unsatisfiable here.

The chord's limiting slope is exactly `(6/5)·(vertex − x)`, where `6/5` is the
Sender's stage curvature and the vertex is the argument of `mwσ`'s clip. So P5
says precisely *the Sender's own unconstrained optimum lies above the inherited
state*. At `x = 1` that caps Target compliance at `1/10`, while this economy's
own static Stackelberg policy — proved optimal in
`LowDeltaStaticStackelberg.lean` — is `63/116 ≈ 0.5431`. No `K_S ≥ 0` and no `δ`
closes that gap; the slope there is `−257/1160 < 0`.

So even a successful coupled construction would not have delivered persistence
at `lowDeltaParams`. The cause is one coefficient fact: the rally-minus-curvature
margin `27/20 − 6/5 = 3/20` cannot cover the intercept `1/10` plus half the
equilibrium compliance.

Two things this does **not** say. It does not say a coupled equilibrium fails to
exist here — the four refutations above remain route-scoped. And it does not say
persistence forces a corner: `mw_subpivot_chord_at_one_forces_corner` pins
`σ = 1` at `x = 1` **only**, leaving `σ(x) < 1` free at every `x < 1`.

## What this does and does not license

Every refutation here is **route-scoped, not proposition-scoped**. None of the
four propositions is disproved. What is proved is that these particular routes
to them cannot be tightened into success. Reporting this directory as "coupled
equilibria do not exist" would be exactly wrong, and the files say so
individually.

The architectural conclusion the audit reached is that the constructive move is
to **enlarge the slack** rather than sharpen the localisation — the slack is
linear in the packet radii `r_T = 4/5`, `r_S = 3/20`, and re-deriving those
analytically through `Foundations/ValidatedLocalPerovOnCarriers` is the route
that file itself prescribes. Any such attempt must first prove the re-derived
radii keep the Sender ball inside the carrier and preserve the Perov self-map
condition. **That check is not done.**

## What is still load-bearing here

Three things, so do not delete the directory:

1. **`not_coupledLeaderStrongConcave`** was historical headline row 22. It left
   the headline surface in round V (2026-09-15) and stays in the tree as the
   Rule 11 refutation of the modulus-2 leader premise: the coupled Schur matrix
   arithmetic is valid, but that premise is false on the current carriers.
   Keeping the obstruction is the honest alternative to quietly dropping the
   claim.
2. **`LowDeltaWindowWitness`** is the first economy where the kernel-width
   window is provably non-empty — a real positive result about where the route
   *can* work.
3. **`LowDeltaCarrierLocalEquilibriumFrontier`** is cited by the paper. Its
   former conditional-existence theorem was **removed**, because it "exposed
   numerical policy bounds that were not derived from the economy". The file is
   retained as a diagnostic that documents why the packet fails.

## Reading order, if you want to

`LowDeltaWindowWitness` → `CoupledSchurWitness` →
`LowDeltaCarrierLocalEquilibriumFrontier` → `LowDeltaLocalizationFloorCounterexample`.

That is the arc: the window opens, the matrix is built, the packet is assembled,
and the floor proves it cannot be tightened. The remaining thirty-one modules
are the residual arithmetic supporting those four.
