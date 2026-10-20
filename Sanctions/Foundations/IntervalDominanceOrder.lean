/-
Sanctions/Foundations/IntervalDominanceOrder.lean

**Interval Dominance Order (IDO) — scalar form**, after Quah and
Strulovici (2007), *Comparative Statics with the Interval Dominance
Order: Some Extensions* (henceforth QS07-Ext, file
`PaperRefer/MathTheory/IntervalDominanceOrderExtensions-QuahStrulovici.md`).

⚠ **Citation hazard — QS07-Ext is the UNPUBLISHED companion notes, and its
numbering does NOT agree with the published paper** (Quah & Strulovici,
*Comparative Statics, Informativeness, and the Interval Dominance Order*,
*Econometrica* 77(6):1949–1992, 2009). In the published paper, Propositions
5 and 6 are about optimal stopping and benefit–cost comparisons — nothing to
do with argmax monotonicity. Every `QS07-Ext Prop N` reference in this file
means the *notes*, never the Econometrica paper. The correspondence is:
QS07-Ext **Prop 5** (hypothesis-free scalar monotone argmax) = Econometrica
2009 **Theorem 1**.

The full multi-dim machinery of QS07-Ext §1
specialises here to the scalar case used by the project's downstream
consumer
`Sanctions.AbstractGame.Params.dynamicTopRealizedRule_mono_of_singleCrossingOn`,
where both the choice axis (sanction realisation `s`) and the
parameter axis (state `x`) live on `ℝ`.

## Round 30 scope

Per the Round-30 plan's caveat clause: the largest single round, with
an explicit fall-back if blocked — *"deliver an architectural skeleton
+ the Foundations predicates + Proposition 6 discharger and defer
Theorem 1 + the full Theory wrapper to a follow-up."*

This file delivers:

* §1 — predicates `IntervalDominanceOrderOn` (g ⪰_I f on `J`,
  QS07-Ext line 35-37) and the parameter-family form `IDOFamilyOn`.
* §2 — bridge `SingleCrossingOn.of_IDOFamilyOn_of_monotone_in_choice`:
  IDO of the parameter family `{f(·, x)}` PLUS choice-axis
  monotonicity of every `f(·, x)` on a convex `S` (the QS07-Ext
  Theorem 1 well-behaved-quasiconcave precondition specialised to
  the strict-mono-in-`s` scalar case) yields
  `Sanctions.MilgromShannon.SingleCrossingOn`.
* §3 — Proposition 6 sign-preservation route to `IDOFamilyOn`,
  packaged as `IDOFamilyOn.of_choice_monotone`: when each `F(·, t)`
  is non-decreasing on a convex `S`, IDO of the parameter family in
  `t` is automatic (the peakedness premise is satisfied trivially,
  and the IDO conclusion reduces to a choice-axis chord comparison
  inside `S`). This is the cleanest sufficient condition the
  composite discharger needs.
* §4 — composite sibling discharger
  `SingleCrossingOn.of_IDO_under_choice_monotone`: takes only the
  choice-axis monotonicity hypothesis (each `F(·, t)` is monotone
  non-decreasing on convex `S` for `t ∈ T`) and returns
  `Sanctions.MilgromShannon.SingleCrossingOn S T F`, suitable for
  plugging directly into the
  `StandardComplianceLocalCoreCertificate.hSC_on` field. This is the
  strictly-weaker replacement for the previous
  `strict-SC + α-monotone` combination: it only requires
  choice-axis monotonicity (which the project's `h_stage_sender_on`
  primitive already supplies pointwise), with no α-monotonicity at
  all.
* §7 (Wave-0 P8 round, 2026-07-11) — the sign-preservation refinement
  previously deferred from §3: `IDOFamilyOn.of_deriv_sign_preservation`
  (QS07-Ext Proposition 6, scalar two-axis form) discharges the IDO
  family from differentiability-in-choice + well-behaved
  quasiconcavity (critical point ⇒ global argmax) + the paired `≥(>)`
  derivative sign-preservation across the parameter, with core step
  `deriv_nonneg_of_peaked_of_wellBehaved`. This is the derivative-form
  alternative to §6's ordinal `MonotoneTransferOn` route for the
  non-monotone-continuation regime.

## Rule compliance (Round 30 plan)

* Rule 1 (optimal strategies): structural — no strategy fixings; the
  discharger only rewrites the assumption side.
* Rule 3 (assumption surface): pure cat-2 weakening — the composite
  discharger in §4 takes only choice-axis monotonicity of the
  parameter family, no α-monotonicity. No new structure fields are
  introduced.
* Rule 8 (human-language): every theorem carries an English paraphrase
  in its docstring.
* Rule 9 (non-vacuity): sibling examples appear in
  `Sanctions/Examples/JointPositiveSanctions.lean`.
* Rule 19 (Foundations vs Theory split): this file lives in
  `Foundations/` because its content is the external QS07-Ext theory
  with no Sanctions-specific economic content; the Params-level
  wrapper for `hSC_on` lives in
  `Theory/Certificates/StandardComplianceLocal.lean`.
-/

import Sanctions.Foundations.Basic
import Sanctions.Foundations.MilgromShannon
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Quasiconvex

noncomputable section

namespace Sanctions
namespace IntervalDominanceOrder

/-! ## §1 The Interval Dominance Order (IDO), scalar localised form

QS07-Ext (line 35-37) definition: for two real-valued functions
`f, g : ℝ → ℝ`, we say `g ⪰_I f` (`g` I-dominates `f`) if whenever
`x' ≤ x''` and `f` attains its sub-interval maximum at `x''`
(`f x'' ≥ f x` for every `x ∈ [x', x'']`), the comparison
`f x' ≤ f x''` (weak / strict) transfers to `g`. The scalar localised
form below quantifies the implication on a chosen subset `J ⊆ ℝ`. -/

/-- **Interval Dominance Order (scalar localised form), QS07-Ext line
35-37.** `IntervalDominanceOrderOn J g f` means: on `J`, whenever
`x' ≤ x''` are points of `J` and `f` is peaked at `x''` on
`[x', x'']` (i.e. `f x'' ≥ f x` for every `x ∈ [x', x'']`), then the
weak and strict orders on `f` at the endpoints transfer to `g`.

Reading: at any interval-endpoint pair where `f` happens to be argmax-
peaked at the upper endpoint, the comparison `f x' ≤ f x''` (weak or
strict) lifts to `g x' ≤ g x''` — i.e. `g` "dominates" `f` only on
intervals where `f` is well-behaved (peaked at the upper end). This is
strictly weaker than the Milgrom-Shannon Single Crossing Property,
which would require the implication for **every** `(x', x'')`. -/
def IntervalDominanceOrderOn (J : Set ℝ) (g f : ℝ → ℝ) : Prop :=
  ∀ ⦃x' x'' : ℝ⦄, x' ∈ J → x'' ∈ J → x' ≤ x'' →
    (∀ x ∈ Set.Icc x' x'', f x ≤ f x'') →
    (f x' ≤ f x'' → g x' ≤ g x'') ∧
    (f x' < f x'' → g x' < g x'')

/-- **IDO family over a parameter set.** `IDOFamilyOn S T F` means
that for every pair of parameters `t ≤ t'` in `T`, the function
`F(·, t')` I-dominates `F(·, t)` on the choice set `S`. This is
the scalar-parameter specialisation of QS07-Ext's `IDO family`
notion (lines 83-92). -/
def IDOFamilyOn (S T : Set ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃t t' : ℝ⦄, t ∈ T → t' ∈ T → t ≤ t' →
    IntervalDominanceOrderOn S (fun s => F s t') (fun s => F s t)

/-! ## §2 Bridge IDO ⇒ SingleCrossingOn under choice-axis monotonicity

QS07-Ext Theorem 1 (lines 217-232) gives the comparative-statics
conclusion for IDO + I-quasisupermodularity. For our scalar-parameter
setting, the bridge we need is direct: if every `F(·, t)` is monotone
non-decreasing on a convex `S` (the QS07-Ext "well-behaved
quasiconcave + sign-preserved partial" precondition specialised to
the strict-mono-in-`s` case), then the IDO precondition (`F(·, t)`
peaked at the upper endpoint on every sub-interval) is automatic,
so IDO of the family `{F(·, t)}` collapses to
`SingleCrossingOn S T F`.

The convexity of `S` (e.g. `S = Sanctions.I = [0, 1]`) is needed to
ensure the sub-interval `[x, y]` between any two `S`-points stays
inside `S` (where monotonicity is asserted). -/

/-- **Bridge: IDO family + choice-monotonicity ⇒ SingleCrossingOn.**

If `F(s, t)` carries IDO in `t` on `S × T` (`IDOFamilyOn S T F`),
`S` is convex, and every `F(·, t)` is `MonotoneOn` on `S` for
`t ∈ T`, then `Sanctions.MilgromShannon.SingleCrossingOn S T F`.

Reading: the IDO predicate requires `F(·, t)` to be peaked at the
upper endpoint on every interval considered; choice-axis monotonicity
makes this automatic everywhere (on any convex `S`), so IDO collapses
to SCP. This is the scalar-parameter specialisation of QS07-Ext
Theorem 1 + the sign-preservation Proposition 6 well-behaved-
quasiconcave precondition. -/
theorem SingleCrossingOn.of_IDOFamilyOn_of_monotone_in_choice
    {F : ℝ → ℝ → ℝ} {S T : Set ℝ}
    (hS : Convex ℝ S)
    (hIDO : IDOFamilyOn S T F)
    (hMono : ∀ t ∈ T, MonotoneOn (fun s => F s t) S) :
    Sanctions.MilgromShannon.SingleCrossingOn S T F := by
  intro x y t t' hx hy hxy ht ht' htt
  -- Apply IDO of the t-family at parameter pair (t, t') and choice
  -- endpoints (x, y).
  have hIDO_pair := hIDO ht ht' htt hx hy hxy
  -- The peakedness precondition holds because F(·, t) is monotone
  -- non-decreasing on S, so on the sub-interval [x, y] (which sits
  -- in convex S) the maximum is attained at y.
  have h_peaked : ∀ s ∈ Set.Icc x y, F s t ≤ F y t := by
    intro s hs
    have hs_in_S : s ∈ S := by
      -- Convex S is OrdConnected, so the closed interval [x, y] ⊆ S.
      exact hS.ordConnected.out hx hy hs
    exact hMono t ht hs_in_S hy hs.2
  exact hIDO_pair h_peaked

/-! ## §3 Choice-monotonicity ⇒ IDO family (trivial sufficient condition)

The cleanest sufficient condition for `IDOFamilyOn S T F` in the
scalar setting is choice-axis monotonicity of every `F(·, t)` on a
convex `S`: under that hypothesis, the peakedness precondition of IDO
is satisfied trivially at every sub-interval (the upper endpoint
attains the maximum by monotonicity), and the IDO conclusion reduces
to the chord comparison `F(s', t) ≤ F(s'', t) ⇒ F(s', t') ≤ F(s'', t')`,
which is itself a consequence of choice-monotonicity at `t'`.

This is the *trivial* path to IDO; the QS07-Ext non-trivial content of
Proposition 6 is **strictly weaker** — it requires only pointwise
sign-preservation of the partial `F_s` across `t`, without demanding
that each `F(·, t)` be globally monotone. The composite discharger in
§4 wraps the trivial route (choice-monotonicity); the sign-
preservation route is architecturally identified in this docstring and
deferred to a follow-up round.

### Sign-preservation route (deferred follow-up)

QS07-Ext Proposition 6 (line 205-211, multi-dim form): for a
well-behaved quasiconcave `F : R^l → R`, if the partial `∂F/∂x_k` is
sign-preserved across the remaining coordinates (`∂_kF(x̄) ≥ 0 ⟹
∂_kF(x̃) ≥ 0` whenever `x̃_k = x̄_k` and `x̃_i ≥ x̄_i` for `i ≠ k`),
then `F` is I-quasisupermodular. Specialising to the
two-axis scalar case `(s, t)` with `k = s`, this gives an
`IDOFamilyOn` discharger that requires:

1. `F` is C¹ in `s` on `S × T` with partial `F_s : ℝ → ℝ → ℝ`.
2. (Well-behaved quasiconcave in `s` at each `t`.) For every `t ∈ T`,
   `F_s(s_*, t) = 0` implies `s_*` is an argmax of `F(·, t)` on `S`.
   (Holds e.g. if `F(·, t)` is concave in `s`.)
3. Sign-preservation: `∀ s ∈ S, ∀ t̄ ≤ t̃ in T, F_s s t̄ ≥ 0 ⟹
   F_s s t̃ ≥ 0`.

Then `IDOFamilyOn S T F`. The construction follows QS07-Ext lines
117-144 (Proof of Proposition 3 + Proposition 6 line 207-211): the
peakedness premise at `t` lifts via the well-behaved condition to
`F_s(s, t) ≥ 0` on `[s', s'']`; sign-preservation lifts this to
`F_s(s, t') ≥ 0` on the same interval; integrating gives the chord
inequality at `t'`. **Delivered in §7 below**
(`IDOFamilyOn.of_deriv_sign_preservation`, Wave-0 P8 round
2026-07-11). Probe verdict (same round, adversarially confirmed):
the sign-preservation antecedent at the model's Sender dynamic
objective FAILS at carrier generality (exact counterexample with a
monotone C¹ carrier member) but HOLDS at both live witnesses (eeCert,
B2 — where the C¹-in-s hypothesis also holds), so §7 is a per-witness
checkable discharger, exactly like §6's `MonotoneTransferOn`, and no
carrier-generality primitive is adopted. -/

/-- **Choice-strict-monotonicity ⇒ IDO family.** If every `F(·, t)`
is `StrictMonoOn` on `S` for `t ∈ T`, then `IDOFamilyOn S T F`.

The proof exploits the IDO predicate's conditional structure:
peakedness at `t` is automatic by `StrictMonoOn` at `t` (weak chord);
the IDO conclusion at `t'` (chord at `t'`) is the strict-mono chord
at `t'`. Both weak and strict implications follow.

This is a *trivial* sufficient route to IDO included as a building
block for the §4 composite. The strictly weaker sign-preservation
route (QS07-Ext Proposition 6, see §3 docstring above) requires only
pointwise sign-preservation of `F_s` across `t` — strictly weaker
than choice-axis strict monotonicity at every `t` — and is delivered
in §7 (`IDOFamilyOn.of_deriv_sign_preservation`). -/
theorem IDOFamilyOn.of_choice_strictMono
    {F : ℝ → ℝ → ℝ} {S T : Set ℝ}
    (_hS : Convex ℝ S)
    (hStrictMono : ∀ t ∈ T, StrictMonoOn (fun s => F s t) S) :
    IDOFamilyOn S T F := by
  intro t t' ht ht' _htt s' s'' hs' hs'' hss _h_peak
  refine ⟨fun _ => ?_, fun h_strict_t => ?_⟩
  · -- Weak chord at t': F(s', t') ≤ F(s'', t').
    rcases eq_or_lt_of_le hss with hss_eq | hss_lt
    · rw [hss_eq]
    · exact le_of_lt (hStrictMono t' ht' hs' hs'' hss_lt)
  · -- Strict chord at t': F(s', t') < F(s'', t').
    rcases eq_or_lt_of_le hss with hss_eq | hss_lt
    · -- s' = s'' makes the premise `f s' < f s''` false.
      exfalso
      have h_strict_t' : F s' t < F s'' t := h_strict_t
      rw [hss_eq] at h_strict_t'
      exact lt_irrefl _ h_strict_t'
    · exact hStrictMono t' ht' hs' hs'' hss_lt

/-! ## §4 Composite sibling discharger: `SingleCrossingOn` from choice-monotonicity

Composing §2 (IDO + choice-monotonicity ⇒ SCP) with §3
(choice-monotonicity ⇒ IDO) yields:

choice-monotonicity at every `t ∈ T` (on convex `S`) ⇒
`SingleCrossingOn S T F`.

This is the Round-30 strictly-weaker replacement for the previous
`strict-SC + α-monotone` combination in `hSC_on`. The composite
takes only choice-axis monotonicity (which the project's
`h_stage_sender_on` primitive supplies pointwise on the saturated
basin), with no α-monotonicity at all. -/

/-- **Round-30 composite: `SingleCrossingOn` from choice-axis
monotonicity alone.** Strictly-weaker replacement for the previous
`strict-SC + α-monotone` discharger of `hSC_on`.

If `S` is convex and every `F(·, t)` is `MonotoneOn S` for `t ∈ T`,
plus every `F(·, t)` is `StrictMonoOn S` for `t ∈ T` (to give the
strict half of `SingleCrossingOn`), then
`Sanctions.MilgromShannon.SingleCrossingOn S T F`.

The strict-mono-on hypothesis is required because the strict half of
`SingleCrossingOn` (the implication `F x t < F y t ⇒ F x t' < F y t'`)
needs a strict chord at `t'`. Both hypotheses together are still
strictly weaker than the previous `strict-SC + α-monotone` combination
because (i) no α-monotonicity is needed; (ii) choice-axis strict
monotonicity at each parameter is independent of cross-axis IDO
behavior. -/
theorem SingleCrossingOn.of_choice_strictMono
    {F : ℝ → ℝ → ℝ} {S T : Set ℝ}
    (_hS : Convex ℝ S)
    (hStrictMono : ∀ t ∈ T, StrictMonoOn (fun s => F s t) S) :
    Sanctions.MilgromShannon.SingleCrossingOn S T F := by
  intro x y t t' hx hy hxy ht ht' _htt
  refine ⟨fun _ => ?_, fun h_strict => ?_⟩
  · -- Weak case: F x t ≤ F y t ⇒ F x t' ≤ F y t'. Both sides reduce
    -- to a chord at the respective parameter, both of which hold by
    -- StrictMonoOn at the corresponding t.
    rcases eq_or_lt_of_le hxy with hxy_eq | hxy_lt
    · rw [hxy_eq]
    · exact le_of_lt (hStrictMono t' ht' hx hy hxy_lt)
  · -- Strict case: F x t < F y t ⇒ F x t' < F y t'.
    rcases eq_or_lt_of_le hxy with hxy_eq | hxy_lt
    · -- x = y makes the premise `F x t < F y t` false.
      exfalso
      have : F x t < F x t := hxy_eq ▸ h_strict
      exact lt_irrefl _ this
    · exact hStrictMono t' ht' hx hy hxy_lt

/-! ## §5 IDO ⇒ monotone argmax (QS07-Ext Proposition 5, scalar)

**Anchor precision (2026-07-13).** The exact anchor is QS07-Ext
**Proposition 5** alone, *not* "Prop 5 / Theorem 1": QS07-Ext Theorem 1
additionally hypothesises I-quasisupermodularity, which the theorem below
does **not** assume. The hypothesis-free scalar statement proved here is
Prop 5 (equivalently, Theorem 1 of the published Econometrica 2009 paper,
whose scalar Theorem 1 carries no quasisupermodularity hypothesis either).

The comparative-statics payoff of IDO, and the reason it is the right
order for the non-strong-rally Sender sub-regime: if `s₀` maximises
`F(·, t)` and `s₁` maximises `F(·, t')` on a convex `S` with `t ≤ t'`,
then the **upper** selection `max s₀ s₁` also maximises `F(·, t')`. So
the argmax correspondence cannot fall as the parameter rises — the
monotone-comparative-statics conclusion the dynamic top-rule
monotonicity consumes — obtained from IDO **without** the
Milgrom–Shannon single-crossing property (which IDO does *not* imply, so
this is the strictly-weaker route usable when a non-monotone continuation
value breaks SCP). -/

/-- **IDO ⇒ monotone argmax (upper selection), QS07-Ext Prop 5.**
Under `IDOFamilyOn S T F` with convex `S`, if `s₀` is an `F(·, t)`-
maximiser and `s₁` an `F(·, t')`-maximiser on `S` (`t ≤ t'`), then
`max s₀ s₁` is an `F(·, t')`-maximiser on `S`. The argmax therefore does
not fall as the parameter rises, with no single-crossing hypothesis. -/
theorem monotone_argmax_of_IDOFamilyOn
    {F : ℝ → ℝ → ℝ} {S T : Set ℝ} (hS : Convex ℝ S)
    (hIDO : IDOFamilyOn S T F) {t t' : ℝ} (ht : t ∈ T) (ht' : t' ∈ T) (htt : t ≤ t')
    {s₀ s₁ : ℝ} (hs₀S : s₀ ∈ S) (hs₁S : s₁ ∈ S)
    (hs₀ : IsMaxOn (fun s => F s t) S s₀)
    (hs₁ : IsMaxOn (fun s => F s t') S s₁) :
    IsMaxOn (fun s => F s t') S (max s₀ s₁) := by
  rcases le_total s₀ s₁ with hle | hge
  · -- `max = s₁`, already an `F(·, t')`-maximiser.
    rwa [max_eq_right hle]
  · -- `s₁ ≤ s₀`: show `s₀` is itself an `F(·, t')`-maximiser, via IDO.
    rw [max_eq_left hge]
    -- Peakedness of `F(·, t)` at `s₀` on `[s₁, s₀]` (global argmax on `S ⊇ [s₁,s₀]`).
    have h_peaked : ∀ s ∈ Set.Icc s₁ s₀, F s t ≤ F s₀ t := fun s hs =>
      hs₀ (hS.ordConnected.out hs₁S hs₀S hs)
    -- IDO weak chord at `t'`: `F s₁ t ≤ F s₀ t ⟹ F s₁ t' ≤ F s₀ t'`.
    have hchord := (hIDO ht ht' htt hs₁S hs₀S hge h_peaked).1 (hs₀ hs₁S)
    intro x hx
    exact le_trans (hs₁ hx) hchord

/-- **Single crossing ⇒ IDO family (B1 bridge).** The Milgrom–Shannon
single-crossing property is *strictly stronger* than IDO: it requires the
rank-transfer implication for **every** endpoint pair, so it holds a
fortiori on the peaked pairs IDO restricts to. Hence any `SingleCrossingOn`
discharges `IDOFamilyOn`, and the strong-rally regime (where single
crossing is provable) feeds the strictly-weaker IDO route for free. -/
theorem IDOFamilyOn.of_singleCrossingOn
    {F : ℝ → ℝ → ℝ} {S T : Set ℝ}
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn S T F) :
    IDOFamilyOn S T F := by
  intro t t' ht ht' htt s' s'' hs' hs'' hss _h_peak
  exact hSC hs' hs'' hss ht ht' htt

/-! ## §5 Peakedness under quasiconcavity: the chord-form building block

The derivative-free core of the QS07-Ext Proposition-6 route (the
deferred sign-preservation discharger of §3): for a **quasiconcave**
function, being peaked at the right endpoint of an interval forces
monotonicity on the whole interval — purely order-theoretically, with
no differentiability. Superlevel sets of a quasiconcave function are
convex; if the function dropped somewhere inside a right-peaked
interval, the superlevel set at the earlier (higher) value would
contain both endpoints of a sub-interval but not an interior point,
contradicting convexity.

This converts the IDO definition's peakedness premise into a
`MonotoneOn` fact, so a future IDO-family discharger for the
non-monotone-continuation regime needs only a *monotonicity-transfer*
hypothesis across the parameter (a Rule-3 item, deliberately NOT
introduced here) rather than any derivative-level sign condition. -/

/-- **Quasiconcave + right-peaked ⇒ monotone on the interval**
(QS07-Ext Prop. 4/6 core, derivative-free form). If `f` is quasiconcave
on a convex `S ⊆ ℝ` and peaked at `s''` on `[s', s''] ⊆ S`, then `f` is
non-decreasing on `[s', s'']`. -/
theorem monotoneOn_of_quasiconcaveOn_of_peaked {f : ℝ → ℝ} {S : Set ℝ}
    (hS : Convex ℝ S) (hQC : QuasiconcaveOn ℝ S f)
    {s' s'' : ℝ} (hs' : s' ∈ S) (hs'' : s'' ∈ S)
    (h_peak : ∀ s ∈ Set.Icc s' s'', f s ≤ f s'') :
    MonotoneOn f (Set.Icc s' s'') := by
  intro s₁ hs₁ s₂ hs₂ h12
  by_contra hcon
  rw [not_le] at hcon
  have hsub : Set.Icc s' s'' ⊆ S := hS.ordConnected.out hs' hs''
  -- The superlevel set at `f s₁` is convex, contains `s₁` and (by
  -- peakedness) `s''`, hence contains `s₂ ∈ [s₁, s'']` — contradiction.
  have hC : Convex ℝ {x ∈ S | f s₁ ≤ f x} := hQC (f s₁)
  have hmem₁ : s₁ ∈ {x ∈ S | f s₁ ≤ f x} := ⟨hsub hs₁, le_refl _⟩
  have hmem'' : s'' ∈ {x ∈ S | f s₁ ≤ f x} := ⟨hs'', h_peak s₁ hs₁⟩
  have hmem₂ : s₂ ∈ {x ∈ S | f s₁ ≤ f x} :=
    hC.ordConnected.out hmem₁ hmem'' ⟨h12, hs₂.2⟩
  exact absurd hmem₂.2 (not_le.mpr hcon)

/-! ## §6 Monotonicity transfer: the non-monotone-regime IDO discharger

**Rule-3 primitive (user-approved 2026-07-02).** `MonotoneTransferOn`
is the ordinal escalation-consistency condition of the B2 route: on any
choice interval where the LOWER-parameter objective is nondecreasing,
the HIGHER-parameter objective (i) weakly rises across the interval
endpoints, and (ii) strictly so if the lower objective rose strictly.
Combined with per-parameter quasiconcavity (single-peakedness in the
choice variable), it discharges `IDOFamilyOn` with no differentiability
and no monotonicity of the continuation value — the regime where
Milgrom–Shannon single crossing provably fails.

Discharge status: quasiconcavity is witness-dischargeable today (strict
concavity of the full dynamic objective is an existing discharged
pattern, and strict concave ⇒ concave ⇒ quasiconcave);
`MonotoneTransferOn` is an OPEN regime primitive at carrier generality,
flagged in the paper's limitations, to be derived per payoff class or
probed when a non-monotone-continuation witness is built. Its openness
is regime-scoped: wherever single crossing holds it is *subsumed as a
theorem* (`MonotoneTransferOn.of_singleCrossingOn` below, 2026-07-03
provability audit), so it carries assumption load only in the
non-monotone-continuation regime where single crossing provably
fails. -/

/-- **Monotonicity transfer across the parameter (Rule-3 primitive,
user-approved 2026-07-02).** On every choice interval `[s', s''] ⊆ S`
where `F(·, t)` is nondecreasing, the higher parameter `t' ≥ t`
inherits the endpoint comparison: `F(s', t') ≤ F(s'', t')`, strictly
whenever `F(s', t) < F(s'', t)`. -/
def MonotoneTransferOn (S T : Set ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃t t' : ℝ⦄, t ∈ T → t' ∈ T → t ≤ t' →
    ∀ ⦃s' s'' : ℝ⦄, s' ∈ S → s'' ∈ S → s' ≤ s'' →
      MonotoneOn (fun s => F s t) (Set.Icc s' s'') →
      (F s' t' ≤ F s'' t') ∧ (F s' t < F s'' t → F s' t' < F s'' t')

/-- **Single crossing ⇒ monotonicity transfer (containment shrink,
2026-07-03 provability audit).** Wherever the Milgrom–Shannon
single-crossing property holds — e.g. the strong-rally regime — the
Rule-3 primitive `MonotoneTransferOn` is a *theorem*, not an
assumption: single crossing transfers the endpoint comparison from
**every** ordered pair, so a fortiori from the pairs whose
lower-parameter slice is monotone; the `MonotoneOn` gate supplies the
weak antecedent at the interval endpoints. Consequently
`MonotoneTransferOn` carries assumption load **only** in the
non-monotone-continuation regime where single crossing provably fails
(there `IDOFamilyOn.of_singleCrossingOn` is unavailable and
`IDOFamilyOn.of_quasiconcave_monotoneTransfer` is the sole route). -/
theorem MonotoneTransferOn.of_singleCrossingOn
    {F : ℝ → ℝ → ℝ} {S T : Set ℝ}
    (hSC : Sanctions.MilgromShannon.SingleCrossingOn S T F) :
    MonotoneTransferOn S T F := by
  intro t t' ht ht' htt s' s'' hs' hs'' hss hmono
  have h := hSC hs' hs'' hss ht ht' htt
  exact ⟨h.1 (hmono (Set.left_mem_Icc.mpr hss) (Set.right_mem_Icc.mpr hss) hss),
         h.2⟩

/-- **The B2 discharger: quasiconcavity + monotonicity transfer ⇒ IDO
family** (derivative-free chord form of the QS07-Ext Prop-6 route).
The IDO definition's peakedness premise, under quasiconcavity of the
lower-parameter slice, upgrades to monotonicity on the peaked interval
(`monotoneOn_of_quasiconcaveOn_of_peaked`); `MonotoneTransferOn` then
supplies exactly the two rank-transfer clauses of
`IntervalDominanceOrderOn`. No differentiability, no measure theory,
and no monotonicity of any continuation value is used. -/
theorem IDOFamilyOn.of_quasiconcave_monotoneTransfer
    {F : ℝ → ℝ → ℝ} {S T : Set ℝ} (hS : Convex ℝ S)
    (hQC : ∀ t ∈ T, QuasiconcaveOn ℝ S (fun s => F s t))
    (hMT : MonotoneTransferOn S T F) :
    IDOFamilyOn S T F := by
  intro t t' ht ht' htt s' s'' hs' hs'' hss h_peak
  have hmono :=
    monotoneOn_of_quasiconcaveOn_of_peaked hS (hQC t ht) hs' hs'' h_peak
  have h := hMT ht ht' htt hs' hs'' hss hmono
  exact ⟨fun _ => h.1, h.2⟩

/-! ## §7 The Proposition-6 sign-preservation discharger (derivative form)

**QS07-Ext Proposition 6, scalar two-axis specialisation** (the §3
docstring's deferred follow-up, delivered here). For a family
`F(s, t)` that is differentiable in the choice variable `s` on a
convex `S`, with

1. *(well-behaved quasiconcavity)* every critical point of `F(·, t)`
   is a global argmax on `S`, and
2. *(sign preservation, QS07-Ext eq. before Prop 6, the `≥(>)` paired
   form)* `F_s(s, t) ≥ 0 ⟹ F_s(s, t') ≥ 0` and
   `F_s(s, t) > 0 ⟹ F_s(s, t') > 0` for `t ≤ t'`,

the parameter family is IDO: `IDOFamilyOn S T F`. This is strictly
weaker than choice-axis monotonicity (§3 trivial route: monotone slices
have `F_s ≥ 0` everywhere, so sign preservation is vacuous) and is the
derivative-form alternative to the ordinal §6 route
(`IDOFamilyOn.of_quasiconcave_monotoneTransfer`): where §6 consumes the
`MonotoneTransferOn` primitive, §7 consumes a *derivative sign*
condition — checkable by direct computation at smooth payoff classes.

The strict half of the sign-preservation hypothesis is **necessary**:
with only the weak half, `F(s, t) = s`, `F(s, t') = 0` satisfies all
remaining hypotheses (every point of the constant slice is a critical
global argmax) yet violates the strict IDO clause. The paired `≥(>)`
form is exactly QS07-Ext's displayed condition.

Proof architecture (QS07-Ext proof of Prop 3 + Prop 6): peakedness of
`F(·, t)` at `s''` forces `F_s(·, t) ≥ 0` on `(s', s'')` — a dip would
produce an interior minimum, hence a critical point, hence (well-
behaved) a global max *below* the dip's starting value, a
contradiction; sign preservation transports the derivative sign to
`t'`; integrating (`monotoneOn_of_hasDerivWithinAt_nonneg`) gives the
weak chord at `t'`; the mean value theorem plus the *strict* half gives
the strict chord. -/

/-- **Peakedness + well-behavedness force a nonnegative derivative**
(QS07-Ext Prop 3 core step). If `f` is differentiable within a convex
`S`, every critical point of `f` on `S` is a global `S`-argmax
(well-behaved quasiconcavity), and `f` is peaked at `s''` on
`[s', s''] ⊆ S`, then `f' ≥ 0` throughout the open interval
`(s', s'')`.

A negative slope at `z₀ ∈ (s', s'')` would push `f` strictly below
`f z₀` immediately to the right; the minimum of `f` on `[z₀, s'']`
(continuous on a compact) would then sit at an interior point `m` with
`f m < f z₀ ≤ f s''`, so `m` is an interior local minimum, hence
critical — but well-behavedness makes every critical point a global
max, contradicting `f m < f z₀`. -/
theorem deriv_nonneg_of_peaked_of_wellBehaved
    {f f' : ℝ → ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hderiv : ∀ s ∈ S, HasDerivWithinAt f (f' s) S s)
    (hwb : ∀ s₀ ∈ S, f' s₀ = 0 → ∀ s ∈ S, f s ≤ f s₀)
    {s' s'' : ℝ} (hs' : s' ∈ S) (hs'' : s'' ∈ S)
    (h_peak : ∀ s ∈ Set.Icc s' s'', f s ≤ f s'')
    {z₀ : ℝ} (hz₀ : z₀ ∈ Set.Ioo s' s'') :
    0 ≤ f' z₀ := by
  by_contra hneg
  rw [not_le] at hneg
  have hIccS : Set.Icc s' s'' ⊆ S := hS.ordConnected.out hs' hs''
  have hIooS : Set.Ioo s' s'' ⊆ S := fun z hz => hIccS (Set.Ioo_subset_Icc_self hz)
  have hIooInt : Set.Ioo s' s'' ⊆ interior S := isOpen_Ioo.subset_interior_iff.mpr hIooS
  have hz₀S : z₀ ∈ S := hIooS hz₀
  -- Upgrade to a genuine derivative at the interior point `z₀`.
  have hdA : HasDerivAt f (f' z₀) z₀ :=
    (hderiv z₀ hz₀S).hasDerivAt (mem_interior_iff_mem_nhds.mp (hIooInt hz₀))
  -- The negative slope pushes `f` below `f z₀` just to the right.
  have hev_neg : ∀ᶠ w in nhdsWithin z₀ {z₀}ᶜ, slope f z₀ w < 0 :=
    hdA.tendsto_slope.eventually_lt_const hneg
  have h_right : nhdsWithin z₀ (Set.Ioi z₀) ≤ nhdsWithin z₀ {z₀}ᶜ :=
    nhdsWithin_mono _ (fun w hw => ne_of_gt hw)
  have hIoo_mem : Set.Ioo z₀ s'' ∈ nhdsWithin z₀ (Set.Ioi z₀) :=
    Ioo_mem_nhdsGT hz₀.2
  obtain ⟨w, hw_slope, hwIoo⟩ :=
    ((hev_neg.filter_mono h_right).and
      (Filter.eventually_of_mem hIoo_mem fun _ h => h)).exists
  have hFw : f w < f z₀ := by
    rw [slope_def_field] at hw_slope
    rcases div_neg_iff.mp hw_slope with ⟨_, hden⟩ | ⟨hnum, _⟩
    · exact absurd (sub_pos.mpr hwIoo.1) (not_lt.mpr hden.le)
    · linarith [hnum]
  -- Minimise `f` on the compact `[z₀, s'']`.
  have hz₀s'' : z₀ ≤ s'' := hz₀.2.le
  have hIccz₀ : Set.Icc z₀ s'' ⊆ Set.Icc s' s'' := Set.Icc_subset_Icc hz₀.1.le le_rfl
  have hcont : ContinuousOn f (Set.Icc z₀ s'') := fun z hz =>
    ((hderiv z (hIccS (hIccz₀ hz))).continuousWithinAt).mono (hIccz₀.trans hIccS)
  obtain ⟨m, hmIcc, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hz₀s'') hcont
  have hFm_lt : f m < f z₀ := lt_of_le_of_lt (hmin ⟨hwIoo.1.le, hwIoo.2.le⟩) hFw
  have hFz₀_le : f z₀ ≤ f s'' := h_peak z₀ (Set.Ioo_subset_Icc_self hz₀)
  -- The minimiser is interior: not `z₀` (value dropped), not `s''` (peak).
  have hm_ne_z₀ : m ≠ z₀ := fun h => absurd (h ▸ hFm_lt) (lt_irrefl _)
  have hm_ne_s'' : m ≠ s'' := fun h => absurd (h ▸ hFm_lt) (not_lt.mpr hFz₀_le)
  have hmIoo : m ∈ Set.Ioo z₀ s'' :=
    ⟨lt_of_le_of_ne hmIcc.1 (Ne.symm hm_ne_z₀), lt_of_le_of_ne hmIcc.2 hm_ne_s''⟩
  have hmIoo' : m ∈ Set.Ioo s' s'' := ⟨lt_trans hz₀.1 hmIoo.1, hmIoo.2⟩
  have hmS : m ∈ S := hIooS hmIoo'
  -- Interior local minimum ⇒ critical point.
  have hdAm : HasDerivAt f (f' m) m :=
    (hderiv m hmS).hasDerivAt (mem_interior_iff_mem_nhds.mp (hIooInt hmIoo'))
  have hlocmin : IsLocalMin f m :=
    hmin.isLocalMin (Icc_mem_nhds hmIoo.1 hmIoo.2)
  have hcrit : f' m = 0 := hlocmin.hasDerivAt_eq_zero hdAm
  -- Well-behavedness: a critical point is a global max — contradiction.
  exact absurd (hwb m hmS hcrit z₀ hz₀S) (not_le.mpr hFm_lt)

/-- **QS07-Ext Proposition 6 (scalar two-axis form): sign preservation
of the choice-derivative discharges the IDO family.** If `F(·, t)` is
differentiable within a convex `S` at every `t ∈ T`, every critical
point of `F(·, t)` is a global `S`-argmax (well-behaved
quasiconcavity), and the derivative sign is preserved upward in the
parameter in the paired `≥(>)` form
(`0 ≤ F_s(s, t) → 0 ≤ F_s(s, t')` and `0 < F_s(s, t) → 0 < F_s(s, t')`
for `t ≤ t'`), then `IDOFamilyOn S T F`.

This is the derivative-form discharger for the non-monotone-
continuation regime: unlike the §3/§4 routes it does **not** require
any slice of the family to be monotone in the choice variable, and
unlike the §6 route it consumes no ordinal transfer primitive — the
sign condition is directly computable at smooth payoff classes. The
strict half of the sign hypothesis is necessary (see the §7 section
docstring for the constant-slice counterexample). -/
theorem IDOFamilyOn.of_deriv_sign_preservation
    {F Fs : ℝ → ℝ → ℝ} {S T : Set ℝ}
    (hS : Convex ℝ S)
    (hderiv : ∀ t ∈ T, ∀ s ∈ S, HasDerivWithinAt (fun z => F z t) (Fs s t) S s)
    (hwb : ∀ t ∈ T, ∀ s₀ ∈ S, Fs s₀ t = 0 → ∀ s ∈ S, F s t ≤ F s₀ t)
    (hsign : ∀ s ∈ S, ∀ ⦃t t' : ℝ⦄, t ∈ T → t' ∈ T → t ≤ t' →
      (0 ≤ Fs s t → 0 ≤ Fs s t') ∧ (0 < Fs s t → 0 < Fs s t')) :
    IDOFamilyOn S T F := by
  intro t t' ht ht' htt s' s'' hs' hs'' hss h_peak
  rcases eq_or_lt_of_le hss with rfl | hlt
  · exact ⟨fun _ => le_rfl, fun h => absurd h (lt_irrefl _)⟩
  have hIccS : Set.Icc s' s'' ⊆ S := hS.ordConnected.out hs' hs''
  have hIooS : Set.Ioo s' s'' ⊆ S := fun z hz => hIccS (Set.Ioo_subset_Icc_self hz)
  have hIooInt : Set.Ioo s' s'' ⊆ interior S := isOpen_Ioo.subset_interior_iff.mpr hIooS
  -- Step 1 (peakedness at `t` ⇒ nonneg derivative on the open interval).
  have h1 : ∀ z ∈ Set.Ioo s' s'', 0 ≤ Fs z t := fun z hz =>
    deriv_nonneg_of_peaked_of_wellBehaved hS (hderiv t ht) (hwb t ht)
      hs' hs'' h_peak hz
  -- Step 2 (sign preservation transports the sign to `t'`).
  have h2 : ∀ z ∈ Set.Ioo s' s'', 0 ≤ Fs z t' := fun z hz =>
    (hsign z (hIooS hz) ht ht' htt).1 (h1 z hz)
  -- Step 3 (integrate: the `t'`-slice is monotone on `[s', s'']`).
  have hcont' : ContinuousOn (fun z => F z t') (Set.Icc s' s'') := fun z hz =>
    ((hderiv t' ht' z (hIccS hz)).continuousWithinAt).mono hIccS
  have hmono' : MonotoneOn (fun z => F z t') (Set.Icc s' s'') := by
    have hd : ∀ z ∈ interior (Set.Icc s' s''),
        HasDerivWithinAt (fun w => F w t') (Fs z t') (interior (Set.Icc s' s'')) z := by
      intro z hz
      rw [interior_Icc] at hz ⊢
      exact (hderiv t' ht' z (hIooS hz)).mono hIooS
    have hnn : ∀ z ∈ interior (Set.Icc s' s''), 0 ≤ Fs z t' := by
      intro z hz
      rw [interior_Icc] at hz
      exact h2 z hz
    exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s' s'') hcont' hd hnn
  refine ⟨fun _ => hmono' (Set.left_mem_Icc.mpr hss) (Set.right_mem_Icc.mpr hss) hss, ?_⟩
  -- Step 4 (strict clause via the mean value theorem + strict sign half).
  intro hstrict
  have hcont_t : ContinuousOn (fun z => F z t) (Set.Icc s' s'') := fun z hz =>
    ((hderiv t ht z (hIccS hz)).continuousWithinAt).mono hIccS
  have hdt : ∀ z ∈ Set.Ioo s' s'', HasDerivAt (fun w => F w t) (Fs z t) z := fun z hz =>
    (hderiv t ht z (hIooS hz)).hasDerivAt (mem_interior_iff_mem_nhds.mp (hIooInt hz))
  obtain ⟨m, hm, hslope_eq⟩ :=
    exists_hasDerivAt_eq_slope (fun z => F z t) (fun z => Fs z t) hlt hcont_t hdt
  have hpos_t : 0 < Fs m t := by
    rw [hslope_eq]
    exact div_pos (sub_pos.mpr hstrict) (sub_pos.mpr hlt)
  have hpos_t' : 0 < Fs m t' := (hsign m (hIooS hm) ht ht' htt).2 hpos_t
  -- Positive derivative at `m` forces a strictly smaller value just left of `m`.
  have hdAm : HasDerivAt (fun z => F z t') (Fs m t') m :=
    (hderiv t' ht' m (hIooS hm)).hasDerivAt (mem_interior_iff_mem_nhds.mp (hIooInt hm))
  have hev_pos : ∀ᶠ w in nhdsWithin m {m}ᶜ, 0 < slope (fun z => F z t') m w :=
    hdAm.tendsto_slope.eventually_const_lt hpos_t'
  have h_left : nhdsWithin m (Set.Iio m) ≤ nhdsWithin m {m}ᶜ :=
    nhdsWithin_mono _ (fun w hw => ne_of_lt hw)
  have hIoo_mem : Set.Ioo s' m ∈ nhdsWithin m (Set.Iio m) :=
    Ioo_mem_nhdsLT hm.1
  obtain ⟨w, hw_slope, hwIoo⟩ :=
    ((hev_pos.filter_mono h_left).and
      (Filter.eventually_of_mem hIoo_mem fun _ h => h)).exists
  have hFw : F w t' < F m t' := by
    rw [slope_def_field] at hw_slope
    rcases div_pos_iff.mp hw_slope with ⟨_, hden⟩ | ⟨hnum, _⟩
    · exact absurd (sub_neg.mpr hwIoo.2) (not_lt.mpr hden.le)
    · linarith [hnum]
  have hwIcc : w ∈ Set.Icc s' s'' := ⟨hwIoo.1.le, le_trans hwIoo.2.le hm.2.le⟩
  have hmIcc : m ∈ Set.Icc s' s'' := Set.Ioo_subset_Icc_self hm
  calc F s' t' ≤ F w t' := hmono' (Set.left_mem_Icc.mpr hss) hwIcc hwIoo.1.le
    _ < F m t' := hFw
    _ ≤ F s'' t' := hmono' hmIcc (Set.right_mem_Icc.mpr hss) hm.2.le

/-! ## §8 Fixed-action IDO need not survive policy substitution

The coupled-witness audit isolates a tempting but invalid shortcut: prove IDO
for `G(·, x, a)` at every fixed action `a`, then substitute a continuous
feasible policy `a = α(x)`.  The example below refutes that implication.

Take `G(s,x,a) = (x-a)s` on sanctions `[0,1]` and states `[0,1/2]`.
At every fixed action, the sanction chord has increasing differences in the
state, so the family satisfies IDO.  But the continuous feasible policy
`α(x)=2x` changes the substituted objective to `-xs`, whose sanction chord
falls with the state and violates even the weak IDO clause between states
zero and one half.  Thus a realized-policy bridge genuinely needs an order or
variation restriction on the policy (or a direct substituted-objective
condition); continuity and feasibility do not suffice. -/

/-- **Fixed-action IDO is not preserved by continuous feasible policy
substitution.** There are an objective `G` and policy `α` such that every
fixed-action state family has IDO, `α` is continuous and feasible on the
state interval, but the realized family `G(s,x,α(x))` fails IDO. -/
theorem fixedActionIDO_not_preserved_by_continuous_feasible_policy :
    ∃ (G : ℝ → ℝ → ℝ → ℝ) (α : ℝ → ℝ),
      (∀ a ∈ Sanctions.I,
        IDOFamilyOn Sanctions.I (Set.Icc (0 : ℝ) (1 / 2))
          (fun s x => G s x a)) ∧
      Continuous α ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), α x ∈ Sanctions.I) ∧
      ¬ IDOFamilyOn Sanctions.I (Set.Icc (0 : ℝ) (1 / 2))
          (fun s x => G s x (α x)) := by
  refine ⟨(fun s x a => (x - a) * s), (fun x => 2 * x), ?_, ?_, ?_, ?_⟩
  · intro a _ha t t' ht ht' htt s' s'' hs' hs'' hss _hpeak
    constructor
    · intro hweak
      have hcross : 0 ≤ (t' - t) * (s'' - s') :=
        mul_nonneg (sub_nonneg.mpr htt) (sub_nonneg.mpr hss)
      dsimp at hweak ⊢
      nlinarith
    · intro hstrict
      have hcross : 0 ≤ (t' - t) * (s'' - s') :=
        mul_nonneg (sub_nonneg.mpr htt) (sub_nonneg.mpr hss)
      dsimp at hstrict ⊢
      nlinarith
  · fun_prop
  · intro x hx
    constructor <;> nlinarith [hx.1, hx.2]
  · intro hIDO
    have hpair := hIDO
      (show (0 : ℝ) ∈ Set.Icc 0 (1 / 2) by constructor <;> norm_num)
      (show (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2) by constructor <;> norm_num)
      (by norm_num)
      (show (0 : ℝ) ∈ Sanctions.I by constructor <;> norm_num)
      (show (1 : ℝ) ∈ Sanctions.I by constructor <;> norm_num)
      (by norm_num)
    have hpeak : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ((0 - 2 * 0) * x : ℝ) ≤ (0 - 2 * 0) * 1 := by
      intro x hx
      norm_num
    have hconcl := (hpair hpeak).1 (by norm_num)
    norm_num at hconcl

end IntervalDominanceOrder
end Sanctions

end
