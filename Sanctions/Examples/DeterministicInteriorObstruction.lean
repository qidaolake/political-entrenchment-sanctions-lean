/-
Sanctions/Examples/DeterministicInteriorObstruction.lean

**Index module: the deterministic-interior obstruction cluster (Wave-0
P1d.b, 2026-07-11).**

The genuine two-operator *interior* feedback-Stackelberg equilibrium of
the deterministic (Dirac-kernel) model is provably unreachable by both
standard constructive routes, and the natural algorithm provably fails
to converge. This module imports the kernel-checked artifacts so they
compile together as one citable cluster; it adds no new theorem. The
prose companion is `docs/archive/INTERIOR-EXISTENCE-OBSTRUCTION-2026-06-18.md`
(order route, §3-4) and `docs/archive/EXISTENCE-VIA-PURIFICATION-NOTE.md`
(§1, the atomic-kernel degeneracy).

## The obstruction, artifact by artifact

1. **Order route (Knaster–Tarski) — refuted.**
   `Sanctions.Examples.b2_leaderArgmax_not_antitone_in_V_T`
   (`Examples/JointBellmanNotOrderHom.lean`): the Target leader argmax
   is NOT antitone in the continuation value `V_T` — a pointwise raise
   of `V_T` by a state-antitone ramp flips the leader argmax `0 → 1` at
   the B2 economy. This kills the D3b `OrderHom` requirement of the
   joint dualized-lattice construction on the full value rectangle
   (there is no complete-sublattice escape: the monotone-increment set
   is not a sublattice — see the archived note §3.2).

2. **Contraction route (Banach/Perov) — degraded below Lipschitz.**
   `Sanctions.AbstractGame.Params.SigmaDynHolderOn.of_strongConcave`
   and `sigma_dyn_sq_le_of_strongConcave`
   (`Theory/Bellman/StrongConcaveHolder.lean`): under uniform strong
   concavity the Sender dynamic selector `σ_dyn` is Hölder-½ in the
   continuation value — and this exponent is what strong concavity
   *delivers*; no Lipschitz modulus for the joint operator is available
   on the headline value space, so the contraction margin cannot be
   assembled off the decoupled corners.

3. **Value iteration — provably cycles (this round's upgrade).**
   `Sanctions.Examples.jointIteration_two_cycle` and the image
   identities `jointIteration_cycle_{T01,S01,T10,S10}`
   (`Examples/JointIterationCycleWitness.lean`): an exact rational
   period-2 orbit of the joint Bellman iteration at `cycleParams` — an
   economy whose Sender payoff satisfies the maintained strict
   concavity, with every argmax on the orbit a pinned singleton (both
   selector conventions agree) and clip inactive. The leader flips
   corners `a = 1 ↔ a = 0` through exactly the channel of artifact 1
   (higher `V_T` slope raises the leader argmax). This upgrades the
   numerically-observed Doraszelski–Satterthwaite atomic-kernel cycling
   (archived note §1) from float simulation to a kernel-checked
   certificate: deterministic joint value iteration does not converge.

## Design laws recorded by the Wave-0 search (do not re-attempt)

* A leader-flip affine 2-cycle is IMPOSSIBLE when the Sender selector
  is the same at both pairs: the slope-cycle identities force
  `β_T·(2δ−1) > 1`, unsatisfiable for `β_T, δ ∈ (0,1)`. The cycle
  needs BOTH channels — a `V_T`-level leader flip AND a `V_S`-level
  sender-vertex shift (alternating `V_S` slopes).
* A sender-flip 2-cycle with the leader corner held fixed is provably
  infeasible for all admissible rational parameters (the flip driver
  `β_S·δ·(c₁−e₁)` is dominated uniformly).

## What survives, and where existence honestly lives

The corner route (`Theory/Equilibrium/BasinCornerExistence.lean`) and
the slaved/Banach route (`Theory/Equilibrium/SlavedExistence.lean`)
remain the machine-checked from-primitives constructions; interior
existence lives in the purified (atomless-shock) model
(`Theory/Shocked/*`, conditional on the `h_obj_diff` leader-regularity
primitive — see `ASSUMPTION-SURFACE-REGISTER.md`), with the
deterministic transition as the `ε → 0` limit. The class-level fence is
Levy (2013) / Levy–McLennan (2015): without a kernel restriction a
stationary equilibrium may fail to exist at exactly this structural
signature (continuum state, deterministic transition, perfect
information).
-/

import Sanctions.Examples.JointBellmanNotOrderHom
import Sanctions.Examples.JointIterationCycleWitness
import Sanctions.Theory.Bellman.StrongConcaveHolder
