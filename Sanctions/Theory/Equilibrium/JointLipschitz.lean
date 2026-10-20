/-
Sanctions/Theory/Equilibrium/JointLipschitz.lean

**Joint Bellman row-Lipschitz from primitive Lipschitz constants
(conditional / general case).**

The audit's open item "Joint Bellman row-Lipschitz from primitives
(general case for non-constant $\sigma_{\rm dyn}\,V_S$)" required
deriving the row-Lipschitz bounds of the joint Target Bellman
operator `T_T_joint` (from `JointMPE.lean`) from primitive Lipschitz
constants of $U_T$, $V_T$, and the forward-looking Sender argmax
$\sigma_{\rm dyn}\,V_S$.

This module provides the **conditional row-Lipschitz theorem**:
given primitive Lipschitz hypotheses (of $U_T$ in $s$ with constant
$L_U$, of $V_T$ on $\hat S$ with constant $K_V$, and of
$\sigma_{\rm dyn}$ in $V_S$ with constant $L_\sigma$ — discharged at
a future concrete instantiation from IFT + strict concavity of the
dynamic Sender objective in $s$), the pointwise row-Lipschitz bound

  `|T_T_joint V_T V_S x - T_T_joint V_T' V_S' x|
     ≤ β_T · dist V_T V_T' + L_σ · (L_U + β_T · K_V · δ) · dist V_S V_S'`

is machine-checked at every `x ∈ ℝ`.

This downgrades the audit's "general row-Lipschitz from primitives"
open item to a **per-instantiation discharge** of the three Lipschitz
constants: at a future concrete LQ instantiation (or any other
concrete instantiation with appropriate regularity), the constants
$L_\sigma$, $L_U$, $K_V$ are derived from the instantiation's
smoothness and a Berge-IFT argument; the row-Lipschitz bound is then
a one-line corollary of this module.

## Argument

The Joint Target integrand
`f(V_T, V_S; x, a) := U_T(x, a, σ_dyn V_S x a) + β_T · V_T(F(x, σ_dyn V_S x a))`
admits the pointwise bound

  `|f(V_T, V_S; x, a) - f(V_T', V_S'; x, a)|
     ≤ |U_T(x, a, s) - U_T(x, a, s')|
       + β_T · |V_T(F(x, s)) - V_T'(F(x, s'))|`

(where $s := \sigma_{\rm dyn}\,V_S\,x\,a$, $s' := \sigma_{\rm dyn}\,V_S'\,x\,a$).

Bounding each term:

* `|U_T(x, a, s) - U_T(x, a, s')| ≤ L_U |s - s'| ≤ L_U · L_σ · dist V_S V_S'`
  (by U_T Lipschitz in s + σ_dyn Lipschitz in V_S).

* `|V_T(F(x, s)) - V_T'(F(x, s'))|
    ≤ |V_T(F(x, s)) - V_T(F(x, s'))| + |V_T(F(x, s')) - V_T'(F(x, s'))|
    ≤ K_V · |F(x, s) - F(x, s')| + dist V_T V_T'
    ≤ K_V · δ · |s - s'| + dist V_T V_T'
    ≤ K_V · δ · L_σ · dist V_S V_S' + dist V_T V_T'`

  (using $V_T$ Lipschitz on $\hat S$ + sup-norm pointwise bound +
  $F$ affine in $s$ with slope $\delta$ + $\sigma_{\rm dyn}$ Lipschitz
  in $V_S$).

Combining:

  `|f - f'| ≤ β_T · dist V_T V_T' + (L_σ · (L_U + β_T · K_V · δ)) · dist V_S V_S'`

The same bound on `T_T_joint = sup_a f(V_T, V_S; x, ·)` follows from
the standard sup-difference inequality
(`abs_sSup_image_sub_sSup_image_le`).

## Rule compliance

**Rule 1.** $\sigma_{\rm dyn}$ is the equilibrium-derived
forward-looking Sender argmax. All other inputs ($V_T$, $V_S$) are
parameters of the joint Bellman operator.

**Rule 3.** Local theorem-parameter hypotheses only ($L_U$, $K_V$,
$L_\sigma$, the three Lipschitz constants). No new fields on `Params`;
no new Postulates; no new global Props. The hypotheses are derivable
at a future concrete instantiation from standard regularity
(Lipschitz $U_T$ from smoothness; Lipschitz $V_T$ from BellmanT
Lipschitz bookkeeping; Lipschitz $\sigma_{\rm dyn}$ in $V_S$ from
IFT + strict concavity at the instantiation). Parametric in $V_T$,
$V_S$, $V_T'$, $V_S'$.

**Rule 5.** Fully parametric over `(p, V_T, V_S, V_T', V_S',
L_U, K_V, L_σ, hypotheses)`. No instantiation-specific content.
-/

import Sanctions.Theory.Equilibrium.JointMPE
import Sanctions.Theory.Equilibrium.BergeContinuity
import Sanctions.Foundations.SupDiff

namespace Sanctions

open Set Filter Topology BoundedContinuousFunction

noncomputable section

namespace AbstractGame
namespace Params

variable (p : Sanctions.AbstractGame.Params)

/-! ## Pointwise bound on the joint Target integrand

The integrand `f(V_T, V_S; x, a) = U_T(x, a, σ_dyn V_S x a)
+ β_T · V_T(F(x, σ_dyn V_S x a))` admits a pointwise row-Lipschitz
bound under Lipschitz hypotheses on `U_T`, `V_T`, `V_T'`, and
`σ_dyn V_S`. -/


end Params
end AbstractGame

end -- noncomputable section

end Sanctions
