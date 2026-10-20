/-
Sanctions/Paper/Statements.lean

**Statements of the paper's main-text results.** One proposition per result of the manuscript,
stated from the model's definitions and written out in full. Nothing here is proved and no
theorem is referenced: this file is the statement interface a reader can check against the paper.
`Sanctions/Paper/Proofs.lean` proves each proposition from the existing development, and the
formal verification supplement maps every result to its backing declarations.

The imports are the modules that define the vocabulary used below. Some of them also contain the
backing proofs; the statements do not use those proofs, so importing them introduces no
circularity.

Results on the paper's class are stated for the structures that formalize it (`ChordEconomy` and
its extensions); the formal supplement explains the correspondence. A hypothesis that the
conclusion mentions keeps the name it has in the backing theorem; one it does not mention is
written as an arrow, with that name in a comment. The docstrings name the paper condition each
hypothesis carries.
-/
import Sanctions.Theory.LockIn.SigmaDynComparison
import Sanctions.Theory.Certificates.SenderPersistencePackage
import Sanctions.Theory.Certificates.StandardComplianceLocalised
import Sanctions.Theory.Welfare.PlannerZeroSanction
import Sanctions.Examples.PlacableSenderRegimes
import Sanctions.Examples.PlacableSenderRegime01
import Sanctions.Examples.PlacableSenderDefianceClosed
import Sanctions.Examples.PlacableSenderPatienceExistence
import Sanctions.Examples.ChordEconomyWelfareGeneral

namespace Sanctions
namespace Paper

open Set Filter Topology BoundedContinuousFunction
open Sanctions.GeometricApproach (approach)
open Sanctions.InfiniteHorizonVerification (MarkovPlan discountedPayoff stationaryPlan)
open Sanctions.Welfare (zeroI plannerFlow plannerStep zeroSanctionPlan InterestGroupRep)

/-- **Proposition 2 (the myopic benchmark)**, `prop:myopic-benchmark`. Under the one-period
conditions (myopic interiority `hS`, myopic relief `hSR`, the myopic lifting condition `hPs`),
clause (2): at every state the myopic Target's unique optimum is interior partial compliance, the
myopic equilibrium sanctions at no state, and the state falls at least geometrically to zero.
Clauses (3)-(4) carry the forward-looking comparison of Theorem 3 under the entrenchment condition
`hTM` and the Sender margin `hmargin`. -/
def myopicBenchmark : Prop :=
  ∀ (E : Sanctions.Examples.ChordEconomyRelief) (hS : E.uhi < E.q)
    (hSR : E.StageRelief) (hTM : E.LossOffset) (hPs : E.uhi < E.klo)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo),
    -- (1) the same primitives at both views
    (E.pM.U_T = E.toParams.U_T ∧ E.pM.U_S = E.toParams.U_S ∧ E.pM.F = E.toParams.F) ∧
    -- (2) the myopic equilibrium: interior partial compliance, unique, zero sanction, wash-out
    (∀ x ∈ Sanctions.I,
      (E.myopicEquilibriumTopS hS hSR hPs).α x ∈ Ioo (0 : ℝ) 1 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pM.joint_T_top_integrand (E.myopicEquilibriumTopS hS hSR hPs).V_T
          (E.myopicEquilibriumTopS hS hSR hPs).V_S x b) Sanctions.I a →
            a = (E.myopicEquilibriumTopS hS hSR hPs).α x) ∧
      E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTopS hS hSR hPs) x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, (E.myopicPathS hS hSR hPs) x₀ t ≤ (1 - E.dlo) ^ t * x₀) ∧
      Tendsto ((E.myopicPathS hS hSR hPs) x₀) atTop (𝓝 0)) ∧
    -- (3) the forward-looking equilibrium: non-compliance, strict premium, the cap
    (∀ x ∈ Sanctions.I,
      ((E.equilibriumTop_of_margin hTM) hmargin).α x = 0 ∧
      E.toParams.σ x 0
        < E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x ∧
      E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x ≤ E.cap) ∧
    -- (4) paths: wash-in, strict dominance, the limit
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach E.sfloor E.dlo t ≤ (E.dynamicPath hTM) hmargin x₀ t) ∧
      (∀ t, 1 ≤ t → (E.myopicPathS hS hSR hPs) x₀ t < (E.dynamicPath hTM) hmargin x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
        Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z))

/-- **Theorem 3 (foresight versus the myopic benchmark)**, `thm:regime-separation`, with the cap
below one under interiority (`hInt`; `hP` is the lifting condition, `hTM` the entrenchment
condition, `hmargin` the Sender margin): the forward-looking equilibrium has full non-compliance
and a sanction strictly above the myopic sanction and at most the cap, which is below one; the
state path lies strictly above the myopic path at every positive date and converges to a positive
steady state. -/
def regimeSeparation : Prop :=
  ∀ (E : Sanctions.Examples.ChordEconomyRelief) (hInt : E.Interior)
    (hSR : E.StageRelief) (hTM : E.LossOffset) (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo),
    -- (1) the same primitives at both views
    (E.pM.U_T = E.toParams.U_T ∧ E.pM.U_S = E.toParams.U_S ∧ E.pM.F = E.toParams.F) ∧
    -- (2) the myopic equilibrium: interior partial compliance, unique, zero sanction, wash-out
    (∀ x ∈ Sanctions.I,
      (E.myopicEquilibriumTop hInt hSR hP).α x ∈ Ioo (0 : ℝ) 1 ∧
      (∀ a ∈ Sanctions.I,
        IsMaxOn (fun b => E.pM.joint_T_top_integrand (E.myopicEquilibriumTop hInt hSR hP).V_T
          (E.myopicEquilibriumTop hInt hSR hP).V_S x b) Sanctions.I a →
            a = (E.myopicEquilibriumTop hInt hSR hP).α x) ∧
      E.pM.dynamicEquilibriumRule (E.myopicEquilibriumTop hInt hSR hP) x = 0) ∧
    (∀ x₀ ∈ Sanctions.I, (∀ t, (E.myopicPath hInt hSR hP) x₀ t ≤ (1 - E.dlo) ^ t * x₀) ∧
      Tendsto ((E.myopicPath hInt hSR hP) x₀) atTop (𝓝 0)) ∧
    -- (3) the forward-looking equilibrium: non-compliance, strict premium, interior cap
    (∀ x ∈ Sanctions.I,
      ((E.equilibriumTop_of_margin hTM) hmargin).α x = 0 ∧
      E.toParams.σ x 0
        < E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x ∧
      E.toParams.dynamicEquilibriumRule ((E.equilibriumTop_of_margin hTM) hmargin) x ≤ E.cap ∧
      E.cap < 1) ∧
    -- (4) paths: wash-in, strict dominance, interior limit
    (∀ x₀ ∈ Sanctions.I,
      (∀ t, approach E.sfloor E.dlo t ≤ (E.dynamicPath hTM) hmargin x₀ t) ∧
      (∀ t, 1 ≤ t → (E.myopicPath hInt hSR hP) x₀ t < (E.dynamicPath hTM) hmargin x₀ t) ∧
      ∃ z ∈ Sanctions.I, E.responsePath E.VSstar z = z ∧ E.sfloor < z ∧ z ≤ E.cap ∧
        Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z))

/-- **Theorem 4 (dynamic versus myopic sanctions at a fixed target policy)**, `thm:dominance`:
for any game, any bounded continuous Sender continuation value that is non-decreasing in the
state, any target policy and any state, the myopic best response lies weakly below the largest
dynamic best response. -/
def dominance : Prop :=
  ∀ (p : Sanctions.AbstractGame.Params) (V_S : ↥(Sanctions.S : Set ℝ) →ᵇ ℝ),
    Monotone V_S →  -- h_V_S_mono
    ∀ (α : ℝ → ℝ) (x : ℝ), p.σ x (α x) ≤ p.σ_dyn_top V_S x (α x)

/-- **Proposition 5, no exit (lock-in)**, `prop:lock-in`, conclusions (i)-(iii): under the
Sender package (the set, monotonicity and level conditions, without any condition on how the
Target ranks sanction levels), from every start in the high basin `[max xT xS, 1]` the state
stays in the basin, the sanction stays at least the threshold, and sanctions never fall. -/
def lockInNoExit : Prop :=
  ∀ (p : Sanctions.AbstractGame.Params) {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop} {xT xS K_S : ℝ},
    p.SenderPersistencePackage D E xT xS K_S →  -- P
    ∀ x₀ ∈ Set.Icc (max xT xS) 1,
      (∀ n, p.dynamicTopLockInPathF E.V_S E.α x₀ n ∈ Set.Icc (max xT xS) 1) ∧
      (∀ n, max xT xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α x₀ n) ∧
      Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α x₀)

/-- **Proposition 5, entry (lock-in)**, `prop:lock-in`, last clause: when full sanctions raise
every state below the basin, a temporary full-sanction shock of the explicit length
`⌈max xT xS / η⌉`, with `η` the least drift of a full sanction below the basin, carries the state
from any start into the basin, and conclusions (i)-(iii) hold along the equilibrium path resumed
from there. -/
def lockInEntry : Prop :=
  ∀ (p : Sanctions.AbstractGame.Params) {D : p.ValueClass2}
    {E : p.FeedbackStackelbergEquilibriumTop} {xT xS K_S : ℝ},
    p.SenderPersistencePackage D E xT xS K_S →  -- P
    (∀ x ∈ Set.Icc (0 : ℝ) (max xT xS), x < p.F x 1) →  -- hF_top_pre
    ∃ η : ℝ, 0 < η
      ∧ (∃ xmin ∈ Set.Icc (0 : ℝ) (max xT xS), η = p.fullShockDrift xmin)
      ∧ (∀ x ∈ Set.Icc (0 : ℝ) (max xT xS), η ≤ p.fullShockDrift x)
      ∧ ∀ x₀shock ∈ Set.Icc (0 : ℝ) 1,
        p.shockPathF x₀shock (Nat.ceil (max xT xS / η)) ∈ Set.Icc (max xT xS) 1
        ∧ (∀ n, p.dynamicTopLockInPathF E.V_S E.α
                  (p.shockPathF x₀shock (Nat.ceil (max xT xS / η))) n
                  ∈ Set.Icc (max xT xS) 1)
        ∧ (∀ n, max xT xS ≤ p.dynamicTopLockInSanctionsF E.V_S E.α
                  (p.shockPathF x₀shock (Nat.ceil (max xT xS / η))) n)
        ∧ Monotone (p.dynamicTopLockInSanctionsF E.V_S E.α
              (p.shockPathF x₀shock (Nat.ceil (max xT xS / η))))

/-- **Proposition 6 (threshold discount factor for full non-compliance)**,
`prop:collapse-threshold`: in the linear-quadratic special case (the equalities from `SigV = 0`
to `dlo = dhi`), under interiority, myopic relief and the lifting condition, an equilibrium with
full non-compliance at every state exists if and only if the Target's discount factor is at least
the closed-form threshold `betaStar`. -/
def collapseThreshold : Prop :=
  ∀ (E : Sanctions.Examples.ChordEconomyCs),
    E.Interior → E.StageRelief → E.Placable →  -- hInt, hSR, hP
    E.SigV = 0 → E.Ms = 0 → E.τx = 0 → E.Mcx = 0 → E.Mcs = 0 → E.Mmix = 0 →
    E.Qbar = E.q → E.klo = E.khi → E.ℓlo = E.ℓhi → E.plo = E.c → E.vlo = E.vhi →
    E.nhi = 0 → E.glo = E.ghi → E.dlo = E.dhi →
    ((∃ Eq : E.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0)
      ↔ E.betaStar ≤ E.β_T)

/-- **Proposition 7 (i)**, `prop:patience-existence`: the slope condition at a non-negative
slope `g` is inherited by every larger Target discount factor `β'`. -/
def patienceSlope : Prop :=
  ∀ (E : Sanctions.Examples.ChordEconomyRelief) {β' : ℝ},
    E.β_T ≤ β' →  -- hβ
    ∀ {g : ℝ}, 0 ≤ g →  -- hg
    g * (1 - E.β_T * E.glo) + max 0 (E.c - E.β_T * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor →  -- hginv
    g * (1 - β' * E.glo) + max 0 (E.c - β' * E.dlo * g) * (E.Lresp / E.mu)
      ≤ E.vlo + E.nlo * E.sfloor

/-- **Proposition 7 (ii)**, `prop:patience-existence`: for two economies that differ only in the
Target's discount factor, with the Sender's response at full non-compliance non-decreasing in the
state and the slope condition at the less patient economy, a full-non-compliance equilibrium at
the less patient economy implies one at the more patient economy. -/
def patienceExistence : Prop :=
  ∀ {E₁ E₂ : Sanctions.Examples.ChordEconomyRelief},
    Sanctions.Examples.ChordEconomy.SameGameButβT E₁.toChordEconomy E₂.toChordEconomy →  -- h
    E₁.β_T ≤ E₂.β_T →  -- hβ
    MonotoneOn (E₁.responsePath E₁.VSstar) (Icc (0 : ℝ) 1) →  -- hmono
    ∀ {g : ℝ}, 0 ≤ g →  -- hg
    g * (1 - E₁.β_T * E₁.glo) + max 0 (E₁.c - E₁.β_T * E₁.dlo * g) * (E₁.Lresp / E₁.mu)
      ≤ E₁.vlo + E₁.nlo * E₁.sfloor →  -- hginv
    (∃ Eq : E₁.toParams.FeedbackStackelbergEquilibriumTop,
      ∀ x ∈ Sanctions.I, Eq.α x = 0) →  -- h₁
    ∃ Eq : E₂.toParams.FeedbackStackelbergEquilibriumTop, ∀ x ∈ Sanctions.I, Eq.α x = 0

/-- **Proposition 9 (welfare non-identification on the class)**,
`prop:welfare-nonidentification`: two interest-group representations of the same government
payoffs rank the forward-looking equilibrium strictly above the myopic benchmark and strictly
below it, at every initial state and every common planner discount factor. -/
def welfareNonidentification : Prop :=
  ∀ (E : Sanctions.Examples.ChordEconomyRelief) (hS : E.uhi < E.q)
    (hSR : E.StageRelief) (hTM : E.LossOffset) (hPs : E.uhi < E.klo)
    (hmono : MonotoneOn (E.responsePath E.VSstar) (Icc (0 : ℝ) 1)),
    ∃ Rp Rm : InterestGroupRep E.U_S E.U_T,
      ∀ x₀ ∈ Sanctions.I, ∀ β ∈ Set.Ico (0 : ℝ) 1,
        Sanctions.Examples.discountedWelfare β (E.repFlowMyopic hS hSR hPs Rp x₀)
            < Sanctions.Examples.discountedWelfare β (E.repFlowForward hTM hmono Rp x₀)
        ∧ Sanctions.Examples.discountedWelfare β (E.repFlowForward hTM hmono Rm x₀)
            < Sanctions.Examples.discountedWelfare β (E.repFlowMyopic hS hSR hPs Rm x₀)

/-- **Proposition 10 (when zero sanctions are socially optimal)**,
`prop:zero-sanction-planner`: for a bounded welfare flow `W`, a transition `Fc`, a compliance rule
`astar` and the planner discount factor `β`, conditions (i)-(iii) and the planner condition make
the zero-sanction path with compliance `astar` optimal against every time-dependent plan, from
every start. -/
def zeroSanctionPlanner : Prop :=
  ∀ (Fc : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ↥(Sanctions.S : Set ℝ))
    (W : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ↥(Sanctions.I : Set ℝ) → ℝ)
    (astar : ↥(Sanctions.S : Set ℝ) → ↥(Sanctions.I : Set ℝ))
    (β lam L B η M : ℝ),
    0 ≤ β → β < 1 → 0 ≤ lam → β * lam < 1 →  -- hβ0, hβ1, hlam0, hβlam
    (∀ x a s, |W x a s| ≤ M) →  -- hbound
    (∀ x a s, W x a s ≤ W x (astar x) zeroI + η * s.1) →  -- hsoc, condition (i)
    (∀ x y : ↥(Sanctions.S : Set ℝ), x.1 ≤ y.1 →
      W y (astar y) zeroI - W x (astar x) zeroI ≤ B * (y.1 - x.1)) →  -- hchordW, (ii)
    (∀ x y : ↥(Sanctions.S : Set ℝ), x.1 ≤ y.1 →
      (Fc x zeroI).1 ≤ (Fc y zeroI).1) →  -- hmono0
    (∀ x y : ↥(Sanctions.S : Set ℝ), x.1 ≤ y.1 →
      (Fc y zeroI).1 - (Fc x zeroI).1 ≤ lam * (y.1 - x.1)) →  -- hchord0, (iii)
    (∀ (x : ↥(Sanctions.S : Set ℝ)) (s : ↥(Sanctions.I : Set ℝ)),
      (Fc x zeroI).1 ≤ (Fc x s).1) →  -- hmonoS
    (∀ (x : ↥(Sanctions.S : Set ℝ)) (s : ↥(Sanctions.I : Set ℝ)),
      (Fc x s).1 - (Fc x zeroI).1 ≤ L * s.1) →  -- hchordS, (iii)
    η + β * (max B 0 / (1 - β * lam)) * L ≤ 0 →  -- hcond, the planner condition
    ∀ (π : MarkovPlan ↥(Sanctions.S : Set ℝ) (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
      (x₀ : ↥(Sanctions.S : Set ℝ)),
      discountedPayoff (plannerFlow W) (plannerStep Fc) β π x₀
        ≤ discountedPayoff (plannerFlow W) (plannerStep Fc) β
            (stationaryPlan (zeroSanctionPlan astar)) x₀

/-- **Proposition 11 (persistent play can be socially optimal)**,
`prop:planner-efficient-persistence`: under compliance neutrality there is an interest-group
representation whose aggregate welfare is the Sender's payoff, such that at every equilibrium with
full non-compliance the equilibrium play attains the planner's optimum at the Sender's discount
factor against every time-dependent plan, from every start. -/
def plannerEfficientPersistence : Prop :=
  ∀ (E : Sanctions.Examples.ChordEconomy),
    E.ZeroSanctionNeutral →  -- hZ
    ∃ R : InterestGroupRep E.U_S E.U_T,
      (∀ x a s, R.welfare x a s = E.U_S x a s) ∧
      ∀ (Eq : E.toParams.FeedbackStackelbergEquilibriumTop),
        (∀ x ∈ Sanctions.I, Eq.α x = 0) →
        (∀ x : ↥(Sanctions.S : Set ℝ),
          (E.defiancePlan x).1.1 = Eq.α x.1 ∧
          (E.defiancePlan x).2.1 = E.toParams.dynamicEquilibriumRule Eq x.1) ∧
        ∀ (π : MarkovPlan ↥(Sanctions.S : Set ℝ)
              (↥(Sanctions.I : Set ℝ) × ↥(Sanctions.I : Set ℝ)))
          (x₀ : ↥(Sanctions.S : Set ℝ)),
          discountedPayoff (E.repFlow R) E.cubeStep E.β_S π x₀
            ≤ discountedPayoff (E.repFlow R) E.cubeStep E.β_S
                (stationaryPlan E.defiancePlan) x₀

/-- **Theorem 12 (four cases)**, `thm:four-cells`: under the four-case conditions (interiority
`hInt`, the entrenchment condition `hTM`, the lifting condition `hP`, the Sender margin
`hmargin`, the forward-looking relief condition `hrelief` and compliance neutrality `hN`), from
every initial state the political state converges to zero in cases 00 and 01, to a positive
fixed point `z₁₀` of the myopic sanction rule in case 10, and to a steady state `z` strictly above
it in case 11. -/
def fourCases : Prop :=
  ∀ (E : Sanctions.Examples.ChordEconomyCs) (hInt : E.Interior) (hTM : E.LossOffset)
    (hP : E.Placable)
    (hmargin : E.β_S * (E.SigC * E.ghi * E.dhi + (E.KS + 2 * E.SigC) * E.Mmix) ≤ E.rlo)
    (hrelief : E.ℓhi * E.Mtot < E.klo * E.plo) (hN : E.ZeroSanctionNeutral),
    (∀ x₀ ∈ Sanctions.I, Tendsto
      ((E.myopicPath hInt (E.stageRelief_of_reliefSharp hrelief) hP) x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, Tendsto ((E.senderOnlyPath' hInt hP) hrelief hN x₀) atTop (𝓝 0)) ∧
    (∀ x₀ ∈ Sanctions.I, ∃ z₁₀ ∈ Sanctions.I, ∃ z ∈ Sanctions.I, E.σ z₁₀ 0 = z₁₀ ∧
      E.responsePath E.VSstar z = z ∧ 0 < z₁₀ ∧ z₁₀ < z ∧
      Tendsto ((E.targetOnlyPath hTM) x₀) atTop (𝓝 z₁₀) ∧
      Tendsto ((E.dynamicPath hTM) hmargin x₀) atTop (𝓝 z))

end Paper
end Sanctions
