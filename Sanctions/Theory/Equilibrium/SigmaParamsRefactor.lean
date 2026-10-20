/-
Sanctions/Theory/Equilibrium/SigmaParamsRefactor.lean

**Round 32: 4-into-1 σ-quad shrink — alternative `Params` constructor.**

Refactors the four primitive `AbstractGame.Params` σ-fields (`σ`,
`σ_mem`, `σ_continuous`, `σ_isMaxOn_U_S`) into a single optional
strict-concavity primitive `U_S_strictConcave_in_s` on `U_S` in `s`.
(Round-32 history: since round BJ5.1 (2026-10-07) `Params` has three σ-fields,
`σ`, `σ_mem` and `σ_isMaxOn_U_S`; the joint continuity `σ_continuous` is the
class `Params.StaticSelectorContinuous`, which this file derives as the
instance `ofStrictConcaveUSF_staticSelectorContinuous`.)

The σ-quad is then **auto-constructed** from the strict-concavity
primitive via the generic Berge existence + uniqueness skeleton in
`Foundations/Berge.lean` (Stokey-Lucas-Prescott 1989 §3.7 /
Aliprantis-Border 2006 Theorem 17.31).

## Caveat — alternative constructor, not a replacement

This module supplies an *alternative* constructor
`Params.ofStrictConcaveUS` that builds a full `Params` from a slimmer
data set. The existing primitive-σ instances
(`jointPositiveParams`, `polyComplianceParams`) are **unchanged**:
they continue to supply the σ-quad directly because their `U_S` is
**linear** in `s` (e.g. `U_S = s`), and linear functions are not
strictly concave — so the σ-quad shrink does not apply.

The alternative constructor is useful for any future instantiation
whose `U_S` is strictly concave in `s` (e.g. quadratic loss
`U_S(x, a, s) = -(s - s*(x, a))²`); for such instances the user
supplies only the strict-concavity primitive, and the four σ-fields
follow automatically (since round BJ5.1: the three σ-fields and the derived
instance `Params.StaticSelectorContinuous`).

## Continuity scope

The Foundations Berge skeleton delivers existence + uniqueness of
the per-`(x, a)` argmax (`σ x a`) and per-`(x, a)` `IsMaxOn` /
membership specs. Joint continuity of `(x, a) ↦ σ x a` is the Berge
**continuous selector** half. Until round BJ5.1 (2026-10-07) it was the
`Params` field `σ_continuous`, and the constructors below took it as a local
input (`σ_continuous_of_strictConcave`, `σ_continuous_of_supermodular`). It is
now the class `Params.StaticSelectorContinuous`, outside `Params`, so neither
constructor asks for it: on the strict-concavity route the instance is
*derived* (`bergeSigma_continuous`, from `Berge.argmax_continuous`, installed
as the instance `ofStrictConcaveUSF_staticSelectorContinuous`); on the
supermodular route the greatest selector need not be continuous (a linear
Sender payoff with a state-dependent sign jumps), and the instance is
available exactly when its continuity is supplied
(`ofSupermodularUSF_staticSelectorContinuous`).

The generic Berge continuous-selector theorem (a joint-continuous,
strictly-concave-in-choice, compact-domain family yields a
continuous selector) is documented in
`Theory/Equilibrium/BergeContinuity.lean` for the σ_dyn use case.
It is no longer future work for the σ-quad case:
`Foundations/Berge.lean` proves it as `argmax_continuous` — the
selector `argmax` is continuous in the parameter when the objective
is jointly continuous and strictly concave in the choice on a
nonempty compact set. The quartic witness uses it for its own stage
selector (`qwσ_continuous`, `Examples/ChordEconomyQuarticWitness.lean`),
and since round BJ5.1 the strict-concavity constructor uses it too, so its
continuity input is gone. The structural simplification is the
1-for-4 collapse on the *content* fields (the unique argmax of a
strictly concave function — Rule 1 + feasibility + uniqueness — is
recovered from a single primitive).

## Rule compliance

* **Rule 1.** σ is the per-`(x, a)` argmax of `U_S(x, a, ·)` on
  `[0, 1]` via `Berge.argmax`. By construction it is the Sender's
  stage best response — fully equilibrium-derived, no hand-chosen
  selector.
* **Rule 3.** Pure discharger / cat-2 weakening: the original 4
  σ-fields (`σ`, `σ_mem`, `σ_continuous`, `σ_isMaxOn_U_S`) are
  *replaced* by a single primitive (strict concavity of `U_S` in
  `s`) — strictly stronger logically (any model satisfying the
  alternative constructor's hypotheses produces a `Params`
  satisfying every primitive-σ field). The alternative constructor
  is **opt-in**: existing instances retain the primitive-σ shape.
  Rule 3's "stop and confirm" is satisfied because: (i) we
  *narrow* the assumption surface (one primitive instead of four),
  (ii) the new primitive is the canonical economic content (strict
  concavity of the Sender stage payoff in `s`) — exactly what
  SLP §3.7 and Aliprantis-Border 17.31 use to recover the four
  derived properties. (Since round BJ5.1 the four are three `Params`
  fields plus the derived instance `Params.StaticSelectorContinuous`.)
* **Rule 4.** Foundations layer for the generic Berge skeleton;
  Theory/Equilibrium layer for the `Params`-level wrapper.
* **Rule 5.** Fully parametric over the input data; no
  witness-specific instantiation.
* **Rule 8.** Plain-language docstrings throughout.
* **Rule 9.** RETIRED 2026-06-04; no witness obligation for this
  alternative constructor (existing primitive-σ instances continue
  to inhabit `Params` non-vacuously).
* **Rule 10.** `#print axioms` clean on the new constructor.
* **Rule 19.** External theory (Berge / SLP §3.7) lives in
  `Foundations/Berge.lean`; this `Theory/Equilibrium` file is the
  Params-level application layer.
-/

import Sanctions.Postulates.AbstractGame
import Sanctions.Foundations.Berge
import Sanctions.Foundations.BalbusReffettWozny
import Sanctions.Foundations.MilgromShannon

namespace Sanctions
namespace AbstractGame
namespace Params

open Set

noncomputable section

/-! ## §1 Auxiliary: continuous-on-`I` slice for `U_S(x, a, ·)`

A small helper that extracts the per-`(x, a)` continuity slice of
`U_S(x, a, ·)` on `Set.Icc 0 1` from the joint continuity field
`U_S_continuous`. This is the precondition the Berge skeleton needs
to produce the argmax. -/

/-- **`U_S(x, a, ·)` is continuous on `[0, 1]` for every fixed `(x, a)`.**

Slice of the joint continuity primitive `U_S_continuous` along the
choice axis `s`. Used as the Berge skeleton's per-parameter
continuity hypothesis. -/
theorem uS_slice_continuousOn
    {U_S : ℝ → ℝ → ℝ → ℝ}
    (hU_S : Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (x a : ℝ) :
    ContinuousOn (fun s : ℝ => U_S x a s) (Set.Icc (0 : ℝ) 1) := by
  have h_triple : Continuous (fun s : ℝ => (x, a, s)) := by
    refine .prodMk continuous_const (.prodMk continuous_const continuous_id)
  exact (hU_S.comp h_triple).continuousOn

/-! ## §2 The Berge-built σ-selector

For any `U_S` jointly continuous in `(x, a, s)` and strictly concave
in `s` on `[0, 1]` for every `(x, a)`, the per-`(x, a)` argmax is
unique and given by `Berge.argmax`. This is the σ-selector that
auto-discharges the σ-quad fields. -/

/-- **The Berge-built σ-selector for a strictly-concave `U_S`.**

For each `(x, a) ∈ ℝ²`, returns the unique maximizer of `U_S(x, a, ·)`
on `[0, 1]`. The maximizer exists by Weierstrass (compact + continuous)
and is unique by strict concavity (midpoint argument). -/
noncomputable def bergeSigma
    {U_S : ℝ → ℝ → ℝ → ℝ}
    (hU_S : Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (hSC : ∀ x a : ℝ, StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => U_S x a s)) :
    ℝ → ℝ → ℝ :=
  fun x a =>
    Sanctions.Foundations.Berge.argmax
      (K := Set.Icc (0 : ℝ) 1)
      isCompact_Icc ⟨0, by simp⟩
      (f := fun (xa : ℝ × ℝ) (s : ℝ) => U_S xa.1 xa.2 s)
      (fun xa => uS_slice_continuousOn hU_S xa.1 xa.2)
      (fun xa => hSC xa.1 xa.2)
      (x, a)

/-- **Auto-built σ_mem: the Berge selector lies in `[0, 1]`.** -/
theorem bergeSigma_mem
    {U_S : ℝ → ℝ → ℝ → ℝ}
    (hU_S : Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (hSC : ∀ x a : ℝ, StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => U_S x a s))
    (x a : ℝ) :
    bergeSigma hU_S hSC x a ∈ Set.Icc (0 : ℝ) 1 :=
  Sanctions.Foundations.Berge.argmax_mem
    (K := Set.Icc (0 : ℝ) 1)
    isCompact_Icc ⟨0, by simp⟩
    (f := fun (xa : ℝ × ℝ) (s : ℝ) => U_S xa.1 xa.2 s)
    (fun xa => uS_slice_continuousOn hU_S xa.1 xa.2)
    (fun xa => hSC xa.1 xa.2)
    (x, a)

/-- **Auto-built σ_isMaxOn_U_S: the Berge selector is a Sender stage
argmax of `U_S(x, a, ·)` on `[0, 1]`.** -/
theorem bergeSigma_isMaxOn_U_S
    {U_S : ℝ → ℝ → ℝ → ℝ}
    (hU_S : Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (hSC : ∀ x a : ℝ, StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => U_S x a s))
    (x a : ℝ) :
    IsMaxOn (fun s => U_S x a s) (Set.Icc (0 : ℝ) 1) (bergeSigma hU_S hSC x a) :=
  Sanctions.Foundations.Berge.argmax_isMaxOn
    (K := Set.Icc (0 : ℝ) 1)
    isCompact_Icc ⟨0, by simp⟩
    (f := fun (xa : ℝ × ℝ) (s : ℝ) => U_S xa.1 xa.2 s)
    (fun xa => uS_slice_continuousOn hU_S xa.1 xa.2)
    (fun xa => hSC xa.1 xa.2)
    (x, a)

/-- **Auto-built static-selector continuity: the Berge selector is jointly
continuous in `(x, a)`.** For a Sender payoff jointly continuous in
`(x, a, s)` and strictly concave in `s` on `[0, 1]`, the unique stage maximiser
moves continuously with the state and the compliance level — Berge's maximum
theorem with a singleton argmax (`Foundations/Berge.lean`,
`argmax_continuous`). General in `F`: no transition appears. This is what
removes the `σ_continuous_of_strictConcave` input from `ofStrictConcaveUSF`
(round BJ5.1, 2026-10-07). -/
theorem bergeSigma_continuous
    {U_S : ℝ → ℝ → ℝ → ℝ}
    (hU_S : Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (hSC : ∀ x a : ℝ, StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => U_S x a s)) :
    Continuous (fun (xa : ℝ × ℝ) => bergeSigma hU_S hSC xa.1 xa.2) := by
  have hjoint : Continuous
      (fun θs : (ℝ × ℝ) × ℝ => U_S θs.1.1 θs.1.2 θs.2) :=
    hU_S.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  exact Sanctions.Foundations.Berge.argmax_continuous
    (K := Set.Icc (0 : ℝ) 1)
    isCompact_Icc ⟨0, by simp⟩
    (f := fun (xa : ℝ × ℝ) (s : ℝ) => U_S xa.1 xa.2 s)
    (fun xa => uS_slice_continuousOn hU_S xa.1 xa.2)
    (fun xa => hSC xa.1 xa.2) hjoint

/-! ## §3 The alternative `Params` constructor

Builds a full `AbstractGame.Params` from a slimmer data set that
*omits* the σ-fields. The σ-quad is auto-built via the Berge
selector + the auto-built `_mem` and `_isMaxOn_U_S` theorems. The
selector's continuity is no longer a `Params` field (round BJ5.1): on the
strict-concavity route it is derived (`bergeSigma_continuous`) — see the file
header's "Continuity scope" note. -/


/-- **The Path-A (BRW 2014 supermodular-only) σ-selector for a
continuous `U_S`.**

For each `(x, a) ∈ ℝ²`, returns the *greatest* maximizer of
`U_S(x, a, ·)` on `[0, 1]`. Existence is by Weierstrass; greatness
is by Weierstrass-on-identity over the closed argmax set
(`BalbusReffettWozny.greatestArgmax`). No strict concavity is
required — applies to linear `U_S = s` (where the selector
evaluates to the constant `1`). -/
noncomputable def bergeGreatestSigma
    {U_S : ℝ → ℝ → ℝ → ℝ}
    (hU_S : Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2)) :
    ℝ → ℝ → ℝ :=
  fun x a =>
    Sanctions.Foundations.BalbusReffettWozny.greatestArgmax
      (K := Set.Icc (0 : ℝ) 1)
      isCompact_Icc ⟨0, by simp⟩
      (f := fun (xa : ℝ × ℝ) (s : ℝ) => U_S xa.1 xa.2 s)
      (fun xa => uS_slice_continuousOn hU_S xa.1 xa.2)
      (x, a)

/-- **Auto-built σ_mem: the Path-A greatest σ-selector lies in `[0, 1]`.** -/
theorem bergeGreatestSigma_mem
    {U_S : ℝ → ℝ → ℝ → ℝ}
    (hU_S : Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (x a : ℝ) :
    bergeGreatestSigma hU_S x a ∈ Set.Icc (0 : ℝ) 1 :=
  Sanctions.Foundations.BalbusReffettWozny.greatestArgmax_mem
    (K := Set.Icc (0 : ℝ) 1)
    isCompact_Icc ⟨0, by simp⟩
    (f := fun (xa : ℝ × ℝ) (s : ℝ) => U_S xa.1 xa.2 s)
    (fun xa => uS_slice_continuousOn hU_S xa.1 xa.2)
    (x, a)

/-- **Auto-built σ_isMaxOn_U_S: the Path-A greatest σ-selector is a
Sender stage argmax of `U_S(x, a, ·)` on `[0, 1]`.** -/
theorem bergeGreatestSigma_isMaxOn_U_S
    {U_S : ℝ → ℝ → ℝ → ℝ}
    (hU_S : Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (x a : ℝ) :
    IsMaxOn (fun s => U_S x a s) (Set.Icc (0 : ℝ) 1)
      (bergeGreatestSigma hU_S x a) :=
  Sanctions.Foundations.BalbusReffettWozny.greatestArgmax_isMaxOn
    (K := Set.Icc (0 : ℝ) 1)
    isCompact_Icc ⟨0, by simp⟩
    (f := fun (xa : ℝ × ℝ) (s : ℝ) => U_S xa.1 xa.2 s)
    (fun xa => uS_slice_continuousOn hU_S xa.1 xa.2)
    (x, a)

/-- **Auto-built greatness: any other Sender stage argmax at `(x, a)`
is bounded above by the Path-A selector.**

This is the substantive Path-A *extremality* content — under
multiple maximizers (which is precisely the case for linear `U_S`
on a non-singleton interval), the Path-A selector picks the
greatest. This both selects deterministically (resolving Rule 1's
optimal-strategy ambiguity in the presence of ties) and aligns
with the canonical "high-sanction" selection convention in the
sanctions literature. -/
theorem bergeGreatestSigma_greatest
    {U_S : ℝ → ℝ → ℝ → ℝ}
    (hU_S : Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (x a : ℝ) {t : ℝ}
    (ht_mem : t ∈ Set.Icc (0 : ℝ) 1)
    (ht_max : IsMaxOn (fun s => U_S x a s) (Set.Icc (0 : ℝ) 1) t) :
    t ≤ bergeGreatestSigma hU_S x a :=
  Sanctions.Foundations.BalbusReffettWozny.greatestArgmax_greatest
    (K := Set.Icc (0 : ℝ) 1)
    isCompact_Icc ⟨0, by simp⟩
    (f := fun (xa : ℝ × ℝ) (s : ℝ) => U_S xa.1 xa.2 s)
    (fun xa => uS_slice_continuousOn hU_S xa.1 xa.2)
    (x, a) ht_mem ht_max


end


/-! ## §4 General-transition `Params` constructors

The two constructors below build an `AbstractGame.Params` from a Sender payoff
plus a Berge-selected static sanction rule, leaving the transition law to the
caller. They are the general-`F` parents of the affine constructors
`ofStrictConcaveUS` and `ofSupermodularUS`, which now live in
`Examples/AffineInstance/LockInShocked.lean` as the `affineF delta` members of
these families (Rule 22 axis 3: a constructor that hard-wires `F` is affine by
instantiation, so it is an instance and not part of the general theory).

Nothing about the Berge selection argument uses the transition: the static
Sender rule `sigma` maximises the *stage* payoff `U_S(x, a, .)` over `[0,1]`,
and the transition enters `Params` only through its own six fields. Splitting
them this way is therefore a pure widening --- every economy the affine
constructors could build, these can build, and non-affine ones besides.
-/

/-- **Berge constructor under a GENERAL transition, strict-concavity route.**
Same content as `ofStrictConcaveUS` --- the static Sender selector is the unique
stage maximiser of a strictly concave `U_S(x, a, .)`, so both `sigma_mem` and
`sigma_isMaxOn_U_S` are discharged by the Berge lemmas rather than assumed
(Rule 1: the sanction rule is an optimisation result, not a posited function)
--- except that the transition `F` and its five structural obligations are
supplied by the caller.

Economically: an economy whose Sender has a strictly concave stage sanction
payoff (a quadratic loss, say) and whose political state moves according to any
law that is feasible, continuous, monotone in each argument, and fixes the
diagonal. The affine law is one such member, not the only one.

Round BJ5.1 (2026-10-07): the input `σ_continuous_of_strictConcave` is gone.
It fed the `Params` field `σ_continuous`, which is now the class
`Params.StaticSelectorContinuous`; for this family the class is derived from
strict concavity (`bergeSigma_continuous`) and installed as the instance
`ofStrictConcaveUSF_staticSelectorContinuous`, so nothing is assumed in its
place. -/
noncomputable def ofStrictConcaveUSF
    (delta : ℝ) (delta_mem : delta ∈ Set.Ioo (0 : ℝ) 1)
    (β_T : ℝ) (β_T_mem : β_T ∈ Set.Ico (0 : ℝ) 1)
    (β_S : ℝ) (β_S_mem : β_S ∈ Set.Ico (0 : ℝ) 1)
    (U_T : ℝ → ℝ → ℝ → ℝ)
    (U_S : ℝ → ℝ → ℝ → ℝ)
    (U_T_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_T xas.1 xas.2.1 xas.2.2))
    (U_S_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (U_S_strictConcave_in_s :
      ∀ x a : ℝ, StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => U_S x a s))
    (F : ℝ → ℝ → ℝ)
    (hF_continuous : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x) :
    Sanctions.AbstractGame.Params where
  δ := delta
  δ_mem := delta_mem
  β_T := β_T
  β_T_mem := β_T_mem
  β_S := β_S
  β_S_mem := β_S_mem
  U_T := U_T
  U_S := U_S
  σ := bergeSigma U_S_continuous U_S_strictConcave_in_s
  σ_mem := bergeSigma_mem U_S_continuous U_S_strictConcave_in_s
  σ_isMaxOn_U_S := bergeSigma_isMaxOn_U_S U_S_continuous U_S_strictConcave_in_s
  U_T_continuous := U_T_continuous
  U_S_continuous := U_S_continuous
  F := F
  F_continuous := hF_continuous
  F_mono_x := hF_mono_x
  F_mono_s := hF_mono_s
  F_diag := hF_diag

/-- **Every strictly concave Berge economy has a continuous static selector.**
The instance `[p.StaticSelectorContinuous]` for the whole `ofStrictConcaveUSF`
family, derived from strict concavity by `bergeSigma_continuous` — the
myopic-comparator and static-Sender results apply to these economies with no
further input. General in `F`: the transition is the caller's and is not read.
Round BJ5.1 (2026-10-07); before it, the same continuity was a constructor
input. -/
instance ofStrictConcaveUSF_staticSelectorContinuous
    (delta : ℝ) (delta_mem : delta ∈ Set.Ioo (0 : ℝ) 1)
    (β_T : ℝ) (β_T_mem : β_T ∈ Set.Ico (0 : ℝ) 1)
    (β_S : ℝ) (β_S_mem : β_S ∈ Set.Ico (0 : ℝ) 1)
    (U_T : ℝ → ℝ → ℝ → ℝ)
    (U_S : ℝ → ℝ → ℝ → ℝ)
    (U_T_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_T xas.1 xas.2.1 xas.2.2))
    (U_S_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (U_S_strictConcave_in_s :
      ∀ x a : ℝ, StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun s => U_S x a s))
    (F : ℝ → ℝ → ℝ)
    (hF_continuous : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x) :
    (ofStrictConcaveUSF delta delta_mem β_T β_T_mem β_S β_S_mem U_T U_S
      U_T_continuous U_S_continuous U_S_strictConcave_in_s F hF_continuous
      hF_mono_x hF_mono_s hF_diag).StaticSelectorContinuous :=
  ⟨bergeSigma_continuous U_S_continuous U_S_strictConcave_in_s⟩

/-- **Berge constructor under a GENERAL transition, supermodular route.**
The general-`F` parent of `ofSupermodularUS`. Drops strict concavity in favour
of the BRW 2014 Path-A extremal selection: for a one-dimensional Sender choice
the assumption set collapses to continuity, and the selector is the *greatest*
element of the argmax set rather than its unique element. As above, the
transition is the caller's.

Round BJ5.1 (2026-10-07): the input `σ_continuous_of_supermodular` is gone. It
fed the `Params` field `σ_continuous`, which is now the class
`Params.StaticSelectorContinuous`; the greatest selector need not be continuous
(for a Sender payoff linear in `s` with a state-dependent sign it jumps), so the
economy is built without it, and the instance is supplied, where it holds, by
`ofSupermodularUSF_staticSelectorContinuous`. -/
noncomputable def ofSupermodularUSF
    (delta : ℝ) (delta_mem : delta ∈ Set.Ioo (0 : ℝ) 1)
    (β_T : ℝ) (β_T_mem : β_T ∈ Set.Ico (0 : ℝ) 1)
    (β_S : ℝ) (β_S_mem : β_S ∈ Set.Ico (0 : ℝ) 1)
    (U_T : ℝ → ℝ → ℝ → ℝ)
    (U_S : ℝ → ℝ → ℝ → ℝ)
    (U_T_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_T xas.1 xas.2.1 xas.2.2))
    (U_S_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (F : ℝ → ℝ → ℝ)
    (hF_continuous : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x) :
    Sanctions.AbstractGame.Params where
  δ := delta
  δ_mem := delta_mem
  β_T := β_T
  β_T_mem := β_T_mem
  β_S := β_S
  β_S_mem := β_S_mem
  U_T := U_T
  U_S := U_S
  σ := bergeGreatestSigma U_S_continuous
  σ_mem := bergeGreatestSigma_mem U_S_continuous
  σ_isMaxOn_U_S := bergeGreatestSigma_isMaxOn_U_S U_S_continuous
  U_T_continuous := U_T_continuous
  U_S_continuous := U_S_continuous
  F := F
  F_continuous := hF_continuous
  F_mono_x := hF_mono_x
  F_mono_s := hF_mono_s
  F_diag := hF_diag

/-- **A supermodular Berge economy has a continuous static selector when its
greatest selector is continuous.** The static-selector instance for a member of
the `ofSupermodularUSF` family, from the joint continuity of the greatest stage
best response — exactly the input the constructor took until round BJ5.1
(2026-10-07), now asked only by the results that read it (use with `haveI`).
General in `F`: the transition is the caller's and is not read. -/
theorem ofSupermodularUSF_staticSelectorContinuous
    (delta : ℝ) (delta_mem : delta ∈ Set.Ioo (0 : ℝ) 1)
    (β_T : ℝ) (β_T_mem : β_T ∈ Set.Ico (0 : ℝ) 1)
    (β_S : ℝ) (β_S_mem : β_S ∈ Set.Ico (0 : ℝ) 1)
    (U_T : ℝ → ℝ → ℝ → ℝ)
    (U_S : ℝ → ℝ → ℝ → ℝ)
    (U_T_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_T xas.1 xas.2.1 xas.2.2))
    (U_S_continuous :
      Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (F : ℝ → ℝ → ℝ)
    (hF_continuous : Continuous (fun xs : ℝ × ℝ => F xs.1 xs.2))
    (hF_mono_x : ∀ s, Monotone (fun x => F x s))
    (hF_mono_s : ∀ x, Monotone (fun s => F x s))
    (hF_diag : ∀ x, F x x = x)
    (σ_continuous_of_supermodular :
      Continuous (fun (xa : ℝ × ℝ) =>
        bergeGreatestSigma U_S_continuous xa.1 xa.2)) :
    (ofSupermodularUSF delta delta_mem β_T β_T_mem β_S β_S_mem U_T U_S
      U_T_continuous U_S_continuous F hF_continuous hF_mono_x hF_mono_s
      hF_diag).StaticSelectorContinuous :=
  ⟨σ_continuous_of_supermodular⟩

/-! ## Compliance placates, from decreasing differences and *no* uniqueness

`DifferentPolicyComparator.lean` supplies `hσ_antiOn_a` — compliance placates,
the Sender's stage rule is non-increasing in the Target's compliance — from the
economic primitive one wants: the Sender's stage payoff has **decreasing
differences** in (sanction, compliance), so a more compliant Target makes hard
sanctions relatively less attractive. But it does so through
`sigma_antitoneOn_a_of_U_S_decreasing_differences`, which also demands that the
Sender's stage argmax be **unique** at every compliance level.

That extra demand is not innocent. Uniqueness of a maximizer is a regularity
condition, not an economic primitive, and it fails exactly where the model is
interesting: a linear Sender payoff in the sanction, a flat stretch, a corner
plateau, a tie between two sanction levels. Where it fails, the whole downstream
chain — rule dominance, path ordering, the self-sustaining set — loses its
hypothesis.

Decreasing differences by itself orders the argmax *correspondence* in the strong
set order, and that does not order an arbitrary selection from it. But it does
order one distinguished selection: the **greatest** maximizer. This section
records that, and it is a strict improvement, since a unique maximizer is
trivially the greatest one (`SigmaGreatestSelector.of_unique` below proves the
implication rather than asserting it).

The project already builds the greatest selector. `bergeGreatestSigma` returns
the largest Sender stage best response at each `(x,a)` — existence by
Weierstrass, greatness by `BalbusReffettWozny.greatestArgmax`, no strict
concavity anywhere — and `ofSupermodularUSF` installs it as a `Params`'s `σ`.
What was missing was the theorem connecting the two, so every economy built that
way had to re-assume placation. It no longer does. -/

/-- **The static Sender selector is a greatest stage best response.**

Not a new primitive: it is a *property* a `Params` may have, and it is strictly
weaker than the argmax-uniqueness hypothesis it replaces
(`SigmaGreatestSelector.of_unique`). For the whole `ofSupermodularUSF` family it
is discharged outright by `sigmaGreatestSelector_of_sigma_eq_bergeGreatest`. -/
def SigmaGreatestSelector (p : Sanctions.AbstractGame.Params) : Prop :=
  ∀ x a, ∀ t ∈ Sanctions.I,
    IsMaxOn (fun s => p.U_S x a s) Sanctions.I t → t ≤ p.σ x a

/-- **Uniqueness implies greatness**, so this route dominates the uniqueness
route rather than merely differing from it. If `σ` is the only stage maximizer,
every stage maximizer equals it and so lies below it. -/
theorem SigmaGreatestSelector.of_unique
    {p : Sanctions.AbstractGame.Params}
    (h : ∀ x a, ∀ t ∈ Sanctions.I,
      IsMaxOn (fun s => p.U_S x a s) Sanctions.I t → t = p.σ x a) :
    p.SigmaGreatestSelector :=
  fun x a t ht hmax => le_of_eq (h x a t ht hmax)

/-- **Compliance placates, with no uniqueness hypothesis.**

If the Sender's stage payoff has decreasing differences in (sanction,
compliance) at state `x`, and the selector returns a greatest stage best
response, then the Sender's stage rule is non-increasing in the Target's
compliance.

This is the hypothesis `hσ_antiOn_a` that the rule-dominance, path-ordering, and
self-sustaining-set theorems in `Theory/LockIn/` all consume — now available
from an economic primitive plus a selector convention, rather than from a
regularity condition on the payoff. -/
theorem sigma_antitoneOn_a_of_decreasingDifferences_and_greatest
    {p : Sanctions.AbstractGame.Params}
    (hgreat : p.SigmaGreatestSelector) (x : ℝ)
    (hDD : Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
      (fun s a => p.U_S x a s)) :
    AntitoneOn (fun a => p.σ x a) Sanctions.I := by
  intro a₁ ha₁ a₂ ha₂ hle
  exact Sanctions.MilgromShannon.greatest_argmax_antitone_of_decreasingDifferencesOn
    hDD hle ha₁ ha₂ (p.σ_mem x a₁) (p.σ_mem x a₂)
    (fun y hy => p.σ_isMaxOn_U_S x a₁ hy)
    (fun y hy => p.σ_isMaxOn_U_S x a₂ hy)
    (fun y hy hy_max => hgreat x a₁ y hy (fun z hz => hy_max z hz))

/-- **The Path-A greatest selector is antitone in compliance under decreasing
differences.** The selector-level statement, free of any `Params`. -/
theorem bergeGreatestSigma_antitoneOn_of_decreasingDifferences
    {U_S : ℝ → ℝ → ℝ → ℝ}
    (hU_S : Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (x : ℝ)
    (hDD : Sanctions.MilgromShannon.DecreasingDifferencesOn Sanctions.I Sanctions.I
      (fun s a => U_S x a s)) :
    AntitoneOn (fun a => bergeGreatestSigma hU_S x a) Sanctions.I := by
  intro a₁ ha₁ a₂ ha₂ hle
  exact Sanctions.MilgromShannon.greatest_argmax_antitone_of_decreasingDifferencesOn
    hDD hle ha₁ ha₂
    (bergeGreatestSigma_mem hU_S x a₁) (bergeGreatestSigma_mem hU_S x a₂)
    (fun y hy => bergeGreatestSigma_isMaxOn_U_S hU_S x a₁ hy)
    (fun y hy => bergeGreatestSigma_isMaxOn_U_S hU_S x a₂ hy)
    (fun y hy hy_max =>
      bergeGreatestSigma_greatest hU_S x a₁ hy (fun z hz => hy_max z hz))

/-- **Every `Params` whose selector is the Path-A greatest one has the
property.**

Both equations hold by `rfl` for a `Params` produced by `ofSupermodularUSF`, so
that entire family discharges `hσ_antiOn_a` from decreasing differences alone —
no uniqueness, no strict concavity, and no assumption on the transition. -/
theorem sigmaGreatestSelector_of_sigma_eq_bergeGreatest
    {p : Sanctions.AbstractGame.Params} {U_S : ℝ → ℝ → ℝ → ℝ}
    (hU_S : Continuous (fun (xas : ℝ × ℝ × ℝ) => U_S xas.1 xas.2.1 xas.2.2))
    (hU : p.U_S = U_S)
    (hσ : p.σ = bergeGreatestSigma hU_S) :
    p.SigmaGreatestSelector := by
  intro x a t ht hmax
  rw [hσ]
  refine bergeGreatestSigma_greatest hU_S x a ht (fun z hz => ?_)
  have := hmax hz
  rw [hU] at this
  exact this


end Params
end AbstractGame
end Sanctions
