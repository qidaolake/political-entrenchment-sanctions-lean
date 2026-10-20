/-
Sanctions/Domain.lean

Aggregator for the **domain layer**: the project's state and action space, and
the projection onto it. Nothing here is mathematics --- `[0,1]` is a modelling
choice, and this layer is where that choice is declared and nowhere else.

The layering is

  Domain -> Foundations -> Postulates -> Theory -> Examples

with `Domain` at the base. That is the honest direction for this tree: twelve
`Foundations/` modules are stated over `S`, and they are reusable operator
theory specialized to this interval rather than adapters that could sit above
it. Putting the interval underneath makes each such specialization a visible
`import` instead of an invisible dependency on a definition that happened to be
in the build prelude.

`Domain` imports nothing from the project, which the audit gate enforces.
-/

import Sanctions.Domain.UnitInterval
import Sanctions.Domain.UnitIntervalProjection
import Sanctions.Domain.UnitIntervalDerivatives
