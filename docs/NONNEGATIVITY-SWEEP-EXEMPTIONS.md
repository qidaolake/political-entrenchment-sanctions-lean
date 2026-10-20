# Nonnegativity-binder sweep: the exemption list

**Status:** safety artifact. Written 2026-08-31 after an audit found roughly thirty
nonnegativity hypotheses that look mechanically dischargeable from primitives.
Most of them are. **Some are not, and one of those sits on a pinned headline row.**

This file exists so that a future round which runs the sweep does not corrupt a
theorem by name-matching. Read it before touching any `h*_nn` binder.

---

## The discriminator

A binder `(h_nn : 0 ≤ c)` is dischargeable exactly when some **companion
hypothesis in the same signature** bounds a quantity by `c` over a domain that is
**provably inhabited by a separated pair** — two points at positive distance, or
one point at which the bounded quantity is an absolute value.

    DERIVABLE     the companion ranges over all reals, over `Sanctions.I`
                  (`= Icc 0 1`, which contains `0`), over the subtype
                  `↥(Sanctions.S : Set ℝ)` (which contains `⟨0,_⟩` and `⟨1,_⟩`
                  at distance exactly `1`), or over all bounded continuous
                  functions.

    NOT DERIVABLE the companion is gated on membership in a set or carrier whose
                  nonemptiness is **not** given in that signature — so the
                  hypothesis may be vacuous and yields nothing; or the scalar has
                  no companion bound at all.

The second case is not hypothetical. It is the difference between a free shrink
and a broken proof, and the two are indistinguishable by name.

---

## Verified EXEMPT — do not sweep these

### 1. `PerovExistence.lean:307-310` — pinned headline row 19

```lean
theorem feedbackStackelbergTop_unique_in_carrier_schur
    (h_inv : D.IsInvariant)
    {β_T β_S L_TS L_ST : ℝ}
    (hβ_T_nn : 0 ≤ β_T) (hβ_S_nn : 0 ≤ β_S)
    (hL_TS_nn : 0 ≤ L_TS) (hL_ST_nn : 0 ≤ L_ST)
    (hT_T : ∀ (V V' : D.CarrierT) (W W' : D.CarrierS), ...)
```

`β_T` and `β_S` here are **abstract implicit scalars**, not the `Params` fields
`p.β_T` / `p.β_S`. So `p.β_T_mem.1` — the projection out of `β_T ∈ Ico 0 1`,
which discharges the binder everywhere else in the tree — **does not apply**.

Nor do the companions help: `hT_T` and `hT_S` quantify over `D.CarrierT` and
`D.CarrierS`, which may be singletons, so no separated pair is available.

This declaration is `Sanctions.AbstractGame.Params.ValueClass2.feedbackStackelbergTop_unique_in_carrier_schur`
(note the `ValueClass2` namespace), pinned as **row 19** at `HEADLINE-SNAPSHOT.md:33`. Removing a binder here moves its
elaborated-type hash, which is a **Rule 18 event requiring the user's decision**
even if the binder were derivable — and it is not.

### 2. `GainBallInvariance.lean:126-131` — `h_T_preserves_gain_of_integrand`

```lean
theorem h_T_preserves_gain_of_integrand
    {M K g xT cube_T : ℝ}
    (hM_nn : 0 ≤ M) (hK_nn : 0 ≤ K) (hg_nn : 0 ≤ g)
    (hcube_T_nn : 0 ≤ cube_T)
    (h_unique_S : ∀ V_S ∈ valLipGainBall M K g xT, p.DynamicArgmaxUnique V_S)
    (hU_T_cube : ∀ x ∈ Sanctions.I, ∀ a ∈ Sanctions.I,
        ∀ s ∈ Sanctions.I, |p.U_T x a s| ≤ cube_T)
```

`hM_nn`, `hK_nn`, `hg_nn` are **exempt**: every companion mentioning `M`, `K` or
`g` is gated on membership in `valLipGainBall M K g xT`, and this signature —
unlike its three siblings below — carries **no** `h_nonempty`. If the ball is
empty the gated hypotheses are vacuous.

`hcube_T_nn` in the same signature **is** derivable, from `hU_T_cube` at
`(0,0,0)` plus `abs_nonneg`. Do not let the shared prefix mislead you: the four
binders on these two lines split two-and-two.

---

## Verified DERIVABLE — safe to sweep

| Binder | Where | Discharge |
|---|---|---|
| `hβ_T_nn` / `hβ_S_nn` on `p.β_T` / `p.β_S` | `InvariantBall.lean:142,239`; `InvariantLipBall.lean:356,430,510,547,582`; `InvariantLipGainBall.lean:520,611` | `p.β_T_mem.1` / `p.β_S_mem.1`. Already Rule 3's named "obvious restatement" exception, so it was never on the assumption surface. The newest file, `GeneralFOperatorRow.lean`, declines the binder outright and derives it in-proof |
| `hcube_T_nn` / `hcube_S_nn` — "the uniform bound on stage payoffs over the unit cube is nonnegative" | `InvariantBall.lean:141,238`; `InvariantLipBall.lean:509`; `GainBallInvariance.lean:128,189,278,365` | Instantiate the companion `hU_*_cube` at `(0,0,0)`; membership witness `⟨le_refl 0, zero_le_one⟩`; close by `abs_nonneg`. The companion ranges over `Sanctions.I`, which provably contains `0` |
| `hR_T_nn` / `hR_S_nn` / `hM_nn` — "the sup-norm radius is nonnegative" | `InvariantBall.lean:144,241`; `InvariantLipBall.lean:508` | `le_trans (norm_nonneg V_T) hV_T_norm`, from the adjacent norm bound |
| `hK_nn` — "the value-function Lipschitz modulus is nonnegative" | `InvariantLipBall.lean:508` | Companion `h_integrand_lipschitz` ranges over `∀ x₁ x₂ : ↥(Sanctions.S : Set ℝ)`, a subtype containing `⟨0,_⟩` and `⟨1,_⟩` at distance `1` |
| `hL_U_nn` — "the stage-payoff Lipschitz constant in the sanction is nonnegative" | `GeneralFOperatorRow.lean:98,192` | Companion `h_U_lipschitz` quantifies over **all reals** with no membership guard; instantiate at `s = 1`, `s' = 0` |
| `hK_V_nn` — "the value-function Lipschitz constant is nonnegative" | `GeneralFOperatorRow.lean:98` **only** | `ValueLipschitzWith.nonneg` (`Theory/Basin/PrimitiveHighBasin.lean:96`) up to renaming — instantiates at the subtype endpoints where the distance is exactly `1`. **Corrected 2026-08-31b:** this row previously also claimed `:192`. At the operator level the companion is `h_V_T_lipschitz_carrier` (`:197-199`), **guarded by `V_T ∈ D.carrier`** — so it is derivable only through `ValueClass.nonempty` (`Theory/Bellman/InvariantValueClass.lean:86`), which that signature does supply. Derivable, but by a different route than stated |
| `hKS_nonneg` — "the Sender value-function Lipschitz modulus is nonnegative" | **four** structure fields (`StandardComplianceLocal.lean:180`, `StandardComplianceSchur.lean:99`, `StandardComplianceLocalC1.lean:113`, `RegularEconomy.lean:329`) plus free-standing binders; measured totals are 51 binder lines and 132 mention lines, not the ~14 first recorded here. **Only the first two are dischargeable** — see the addendum | `hV_S_lip.nonneg` at binder sites; at certificate-field sites route through `hV_S_lip_carrier` plus `ValueClass2.nonempty_S` |

### One caution that is not about derivability

At `InvariantBall.lean:149` the derived quantity is consumed **before** its
companion appears:

```lean
have h_rhs_nn : 0 ≤ cube_T + p.β_T * R_T :=
  add_nonneg hcube_T_nn (mul_nonneg hβ_T_nn hR_T_nn)
```

So a replacement `have` must **lead** the proof body, not sit where the binder
used to be. Mechanically deleting the binder and appending the derivation at the
point of use will fail.

---

## The subtle middle — carrier-gated but with nonemptiness supplied

Three siblings of the exempt case above **do** carry the missing hypothesis:

* `GainBallInvariance.lean:186` — `h_S_preserves_gain_of_payoff`
* `GainBallInvariance.lean:275` — `ofLipGainBall_IsInvariant_of_primitives`
* `GainBallInvariance.lean:362` — `ofLipGainBall_IsInvariant_of_chords`

each with `(h_nonempty : (valLipGainBall M K g xT).Nonempty)`.

That restores a separated pair, so `hM_nn` and `hK_nn` become derivable there —
take a member of the ball, and read `‖V‖ ≤ M` and `ValueLipschitzWith V K` off
its membership.

**`hg_nn` is different and is NOT cleared by `h_nonempty`.**

**Corrected 2026-08-31b — the first version of this paragraph gave the wrong
reason, and the wrong reason was the more dangerous kind: it implied the binder
becomes derivable once someone proves `xT < 1`.** It does not, at any parameter
value.

`LowerSlopeOnValueOn V B g` (`Theory/Certificates/TargetSanctionLossOffset.lean:108`)
unfolds to `g * dist y₁ y₂ ≤ V y₂ − V y₁`. A separated pair therefore gives
`g ≤ (V y₂ − V y₁) / dist y₁ y₂` — an **upper** bound on `g`, whose right-hand
side has unknown sign. No instantiation of a lower-slope condition can produce
`0 ≤ g`, because the condition constrains `g` from above and says nothing from
below. A degenerate pair gives `0 ≤ 0`; a separated pair gives an upper bound.
Neither is a sign.

**`hg_nn` is permanently exempt.** It is a genuine hypothesis — economically,
that the Target continuation-gain rate is nonnegative — and no amount of carrier
nonemptiness or interval width will discharge it.

---

## Standing rule

Before removing any `h*_nn` binder:

1. Find its companion in the **same signature**. If there is none, stop.
2. Ask what domain the companion quantifies over. If it is a set or carrier, ask
   whether that signature proves it nonempty. If it does not, stop.
3. Check whether the declaration is pinned in `HEADLINE-SNAPSHOT.md`. If it is,
   the change is a Rule 18 event and belongs to the user, not to the sweep.
4. Check the consumption order in the proof body.

## Provenance

Every entry above was established by opening the file at HEAD `6ea8a7a`. The
`PerovExistence` exemption and the `GainBallInvariance` two-and-two split were
each confirmed against the source rather than inferred from a name scan — which
is the point: a name scan cannot see either of them.

Coverage is partial by design. `Theory/LockIn/`, `Theory/Shocked/` and
`Theory/Bridges/` have not been swept for this pattern and may hold further
exemptions.

---

## Addendum (2026-08-31b): a third exemption category

Beyond "carrier not proved nonempty", there is a stricter case: **the companion
quantifies over objects whose existence the structure never asserts.**

* `Theory/Certificates/RegularEconomy.lean:329` — `hKS_nonneg` in
  `RegularEconomyCertificateC1ComplianceCore`, whose only Lipschitz field
  quantifies over `E : p.FeedbackStackelbergEquilibriumTop`, i.e. over
  *equilibria*. Nothing in the structure asserts an equilibrium exists, so the
  companion may be vacuous. **Permanently exempt.**
* `Theory/Certificates/StandardComplianceLocalC1.lean:113` — the companion
  quantifies over `z : D_C1.carrier`, and `C1BellmanSystem` carries **no**
  carrier-nonemptiness field. **Exempt** unless `hComplete` is shown to supply an
  inhabitant.

So of the four `hKS_nonneg` structure fields, exactly **two** are dischargeable:
`StandardComplianceLocal.lean:180` and `StandardComplianceSchur.lean:99`, both of
which carry `hV_S_lip_carrier` over a `ValueClass2` whose `nonempty_S` field
(`Theory/Bellman/InvariantValueClass2.lean:92`) inhabits the Sender carrier.

**And the payoff is smaller than this file first implied.** `grep -rn hKS_nonneg
paper/` returns zero — nothing referee-facing carries the field. The slim MS-form
certificate (`StandardComplianceLocal.lean:456`) already omits it, and the
register's two preferred paper-facing rows route through the MS form. The
reduction is real, but it lands on a legacy route for which a slimmer
alternative already ships.
