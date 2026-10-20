/-
Sanctions/Theory/Equilibrium/SlavedExistence.lean

**Conditional slaved-existence bridge for `FeedbackStackelbergEquilibriumTop`.**

This module records the "slaved single-lattice Tarski" existence route
documented in `docs/archive/INTERIOR-EXISTENCE-OBSTRUCTION-2026-06-18.md` §4.2. The
genuine two-operator *joint* lattice route is provably blocked (D3b is
not an `OrderHom` property on the full value rectangle — see that
note §3). The route that *does* survive slaves the Target value to its
own best response and runs Knaster–Tarski on a **single** lattice — the
Sender value — with the slaved Sender composite

  `Φ(V_S) = bellmanS( α*(V_S), V_S )`,
  `α*(V_S) = argmax over a of joint_T_top_integrand (V_T_dyn V_S) V_S x a`,
  `V_T_dyn V_S = targetDynValue (σ_dyn_top V_S)`  (the slaved Target value).

The *monotonicity* of `Φ` on the basin is numerically verified but its
from-primitives discharge needs increment-preservation machinery (a
separate, hard effort — see `docs/archive/INTERIOR-EXISTENCE-OBSTRUCTION-2026-06-18.md` §4 and the
preservation scratch tests). This module therefore delivers a **conditional
bridge**: it *consumes* the slaved-operator monotonicity packaged as a
bundled `OrderHom Φ : L →o L` on an abstract Sender complete-lattice
carrier `L`, applies the in-repo single-lattice Tarski
`Sanctions.MPE.joint_MPE_exists` to obtain a fixed point `q = Φ q`, and
*consumes a realization map* turning the fixed-point equation into a
`FeedbackStackelbergEquilibriumTop`.

This is the exact analogue of `MPE.joint_value_fixedPoint_via_dual`: that
theorem consumes the two value operators as `OrderHom`s (their
monotonicity is the supplier's economic obligation) and *constructs only
the fixed point*; here we consume one slaved operator as an `OrderHom`
and a realization, and construct only the fixed point + equilibrium
packaging.

**Rule-1.** Every strategic object in the *realized* equilibrium is
equilibrium-derived: `V_S` is a Sender Bellman fixed point, `α*` is the
Target leader argmax, `V_T_dyn` is the slaved single-agent Banach value,
`σ_dyn_top` is the greatest Sender selector. Nothing is hand-fixed; the
slaved operator `Φ` is itself built from those argmaxes by the supplier.

**Rule-3.** No new `Params` field, no new Postulate. The carrier `L`, the
operator `Φ`, and the realization are *theorem parameters* (a conditional
bridge), exactly as `joint_value_fixedPoint_via_dual` takes its operators
as parameters. The monotonicity of `Φ` is **not** discharged here.

**Rule-5.** Fully parametric in `(p, L, Φ, …)`; no witness.

**Rule-14 / 15.** The realization is expressed over the *equilibrium
data itself* (it produces an honest `FeedbackStackelbergEquilibriumTop`,
whose fields are concrete relations over BCF data), and the existence of
the Sender fixed point is *constructed* by Tarski (`joint_MPE_exists`),
not assumed via an opaque `…HasFixedPoint` field. The theorem is named
and documented *conditional on* the supplied monotone `Φ` and realization.
-/

import Sanctions.Theory.Equilibrium.BasinCornerExistence
import Sanctions.Foundations.TarskiMPE

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## The slaved-existence bridge

We work over an **abstract Sender complete-lattice carrier** `L`. The
deliverable's economic carrier is the Sender value lattice (Icc-valued
function lattice ∘ `Pi`), but the bridge does not need the concrete
carrier — it needs only that the slaved Sender composite is a monotone
self-map of *some* complete lattice, which is what Tarski requires.
Keeping `L` abstract makes the bridge reusable for *any* complete-lattice
encoding of the Sender value the supplier chooses (Rule 5). -/

/-- **Conditional slaved-existence bridge.**

Given:

* an abstract Sender complete-lattice carrier `L`;
* the **slaved Sender composite operator** packaged as a bundled
  `OrderHom` `Φ : L →o L` — this is exactly the slaved-operator
  *monotonicity* hypothesis, supplied by the user and **not** discharged
  from primitives here (its from-primitives discharge needs the
  increment-preservation machinery flagged in
  `docs/archive/INTERIOR-EXISTENCE-OBSTRUCTION-2026-06-18.md` §4);
* a **realization map** `realize` that, *given any fixed point `q = Φ q`
  of the slaved operator*, produces a genuine
  `FeedbackStackelbergEquilibriumTop` — encoding the (conditional)
  fact that at the slaved fixed point the decoded Sender value, the
  slaved Target value `V_T_dyn`, and the Target leader argmax `α*`
  assemble into the equilibrium fields;

there exists a `FeedbackStackelbergEquilibriumTop`.

The construction is: apply the in-repo single-lattice Tarski
`Sanctions.MPE.joint_MPE_exists Φ` to obtain a fixed point `q = Φ q`,
then hand it to `realize`. Only the fixed point is *constructed*; the
monotonicity of `Φ` and the realization are *consumed*. -/
theorem feedbackStackelbergTop_of_slaved_orderHom
    {L : Type*} [CompleteLattice L]
    (Φ : L →o L)
    (realize : ∀ q : L, Φ q = q → Nonempty p.FeedbackStackelbergEquilibriumTop) :
    Nonempty p.FeedbackStackelbergEquilibriumTop := by
  obtain ⟨q, hq⟩ := Sanctions.MPE.joint_MPE_exists Φ
  exact realize q hq

/-! ## A concrete slaved value operator at the basin corner

The bridge above is fully abstract in the carrier. To make the slaved
*data* concrete and tie it to the actual Sender Bellman map, we record
the slaved Sender composite at the value level over `Val`, and a
specialization of the bridge that consumes the realization at the value
fixed point directly. This is the value-level form the supplier of the
increment-preservation discharge will plug into. -/

/-- **Slaved Target value at a Sender value.** The single-agent Banach
Target value `V_T_dyn V_S` at the greatest Sender selector `σ_dyn_top V_S`,
given continuity of that selector (`hσc`). This is the value the Target
is *slaved* to: its own best response to the Sender's forward-looking
play. Constructed (Rule-15) via `V_T_dyn` / `targetDynValue` /
`ContractingWith.fixedPoint`. -/
noncomputable def slavedTargetValue
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (hσc : Continuous (fun xa : ℝ × ℝ => p.σ_dyn_top V_S xa.1 xa.2)) :
    ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  p.V_T_dyn V_S hσc

/-- **Slaved Sender composite operator** at the value level. Given a
Sender value `V_S` and a continuous Target leader policy `α`, the
composite returns the Sender Bellman image `bellmanS_BCF α … V_S`. A
fixed point of this composite is a Sender value
`V_S = bellmanS_BCF α … V_S`, i.e. the follower fixed-point condition
`V_S_fix`; in the slaved route `α` is simultaneously certified as the
Target's *top* argmax against the slaved Target value (Rule-1). -/
noncomputable def slavedSenderOp
    (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ) (α : ℝ → ℝ) (hα : Continuous α) :
    ↥(Sanctions.S : Set ℝ) →ᵇ ℝ :=
  p.bellmanS_BCF α hα V_S

/-- **Decode-based slaved-existence bridge (more assembled).**

This is the substantive form of `feedbackStackelbergTop_of_slaved_orderHom`:
instead of consuming the equilibrium realization as an opaque function,
it *reconstructs the equilibrium fields explicitly* from a slaved fixed
point, consuming only the genuinely-conditional slaved data.

Given:

* an abstract Sender complete-lattice carrier `L` and a **decode** map
  `decode : L → SVal` recovering the Sender BCF value from a carrier
  element (the supplier's encoding of the Sender value lattice);
* the **slaved Sender composite** as a bundled `OrderHom Φ : L →o L`
  (the monotonicity hypothesis, **consumed not derived**);
* a continuous **Target leader policy at the decoded value**,
  `α : ℝ → ℝ` with `hα : Continuous α`, that is feasible (`hα_mem`)
  on the basin and attains the *top* Target integrand argmax against
  the slaved Target value `V_T_dyn (decode q) hσc` at the fixed point
  (`h_top_opt` — the Rule-1 leader-optimality certificate);
* continuity `hσc` of the greatest Sender selector at the decoded value;
* the **slaved consistency at the fixed point** `h_decode_fix`:
  decoding the slaved image `Φ q` returns the Sender Bellman image
  `bellmanS_BCF α hα (decode q)` — i.e. the slaved operator on `L`
  *is* the Sender Bellman map under the chosen Target policy, read
  through `decode`. Combined with the Tarski fixed point `Φ q = q`,
  this yields exactly the follower fixed-point condition
  `decode q = bellmanS_BCF α hα (decode q)`.

Then a `FeedbackStackelbergEquilibriumTop` exists: its Sender value is
`decode q`, its Target value is the slaved `V_T_dyn (decode q) hσc`, its
leader policy is `α`, and the equilibrium fields are discharged from the
slaved consistency (`V_S_fix`), the slaved Target Bellman equation
(`V_T_fix_top`, via `V_T_dyn_bellman_eq`), and the supplied top-optimality
(`α_opt_top`).

Only the Sender fixed point is *constructed* (by Tarski); the
monotonicity of `Φ`, the slaved consistency, the leader continuity /
feasibility / top-optimality, and the selector continuity are *consumed*.
The from-primitives discharge of the monotonicity remains the open
increment-preservation effort (`docs/archive/INTERIOR-EXISTENCE-OBSTRUCTION-2026-06-18.md` §4). -/
theorem feedbackStackelbergTop_of_slaved_orderHom_decode
    {L : Type*} [CompleteLattice L]
    (decode : L → ↥(Sanctions.S : Set ℝ) →ᵇ ℝ)
    (Φ : L →o L)
    (α : ℝ → ℝ) (hα : Continuous α)
    (hα_mem : ∀ x ∈ Sanctions.S, α x ∈ Sanctions.I)
    -- continuity of the greatest Sender selector at every decoded value
    -- (so the slaved Target value `V_T_dyn` is well-defined there)
    (hσc : ∀ q : L, Continuous (fun xa : ℝ × ℝ =>
      p.σ_dyn_top (decode q) xa.1 xa.2))
    -- slaved consistency: decoding the slaved image is the Sender Bellman
    -- image of the decoded value under the chosen leader policy
    (h_decode_fix : ∀ q : L,
      decode (Φ q) = p.bellmanS_BCF α hα (decode q))
    -- leader top-optimality at every fixed point of `Φ`
    (h_top_opt : ∀ q : L, Φ q = q → ∀ x ∈ Sanctions.S,
      IsMaxOn (fun a => p.joint_T_top_integrand
        (p.V_T_dyn (decode q) (hσc q)) (decode q) x a) Sanctions.I (α x)) :
    Nonempty p.FeedbackStackelbergEquilibriumTop := by
  -- Tarski: a fixed point of the slaved Sender operator on `L`.
  obtain ⟨q, hq⟩ := Sanctions.MPE.joint_MPE_exists Φ
  -- The follower fixed-point condition from slaved consistency + `Φ q = q`.
  have hVS_fix : decode q = p.bellmanS_BCF α hα (decode q) := by
    calc decode q = decode (Φ q) := by rw [hq]
      _ = p.bellmanS_BCF α hα (decode q) := h_decode_fix q
  -- Package the equilibrium with the slaved Target value `V_T_dyn`.
  refine ⟨{
    V_T := p.V_T_dyn (decode q) (hσc q)
    V_S := decode q
    α := α
    hα := hα
    α_mem := hα_mem
    V_S_fix := hVS_fix
    V_T_fix_top := p.V_T_dyn_bellman_eq (decode q) (hσc q)
    α_opt_top := h_top_opt q hq }⟩

/-- **Value-level slaved realization at a basin corner.** When the
supplied Target policy is the constant corner `α ≡ c` (`c ∈ I`), the
slaved Sender fixed point `V_S = bellmanS_BCF (fun _ => c) … V_S`
*is* the canonical corner Sender value `p.V_S (fun _ => c) continuous_const`
(both are the unique Banach fixed point of the same contraction), so the
corner equilibrium of `BasinCornerExistence` realizes the slaved fixed
point. This connects the abstract bridge to the concrete corner route:
the slaved realization at the corner is exactly
`feedbackStackelbergTop_of_constant_corner_optimal`. -/
theorem slaved_realization_at_corner
    (c : ℝ) (hc : c ∈ Sanctions.I)
    (hσc : Continuous (fun xa : ℝ × ℝ =>
      p.σ_dyn_top (p.V_S (fun _ => c) continuous_const) xa.1 xa.2))
    (h_corner : ∀ x ∈ Sanctions.S,
      IsMaxOn (fun a => p.joint_T_top_integrand
        (p.slavedTargetValue (p.V_S (fun _ => c) continuous_const) hσc)
        (p.V_S (fun _ => c) continuous_const) x a) Sanctions.I c) :
    Nonempty p.FeedbackStackelbergEquilibriumTop := by
  -- `slavedTargetValue … = V_T_dyn …` definitionally, so `h_corner`
  -- is exactly the `BasinCornerExistence` corner certificate.
  obtain ⟨E, _⟩ :=
    p.feedbackStackelbergTop_of_constant_corner_optimal c hc hσc h_corner
  exact ⟨E⟩

end Params
end AbstractGame

end -- noncomputable section

end Sanctions
