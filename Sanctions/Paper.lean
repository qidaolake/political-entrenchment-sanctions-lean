/-
Sanctions/Paper.lean

Umbrella for the paper interface: `Sanctions/Paper/Statements.lean` states each main-text result
of the manuscript in full, without proofs, and `Sanctions/Paper/Proofs.lean` proves each statement
by its backing declaration. The layer sits above Examples: it may import any layer, and no other
layer imports it. The audit gate checks that every module under `Sanctions/Paper/` appears here and
that the statements import neither the proofs nor the headline gate file.
-/

import Sanctions.Paper.Statements
import Sanctions.Paper.Proofs
