/-
Sanctions/Postulates.lean

**The entire assumption surface of the formalization.**

This aggregator imports every structure / Prop in `Sanctions/Postulates/`.
Importing this single file is equivalent to importing every assumption
bundle the rest of the codebase uses.

An auditor reading `Sanctions/Postulates/*.lean` gets the complete
list of what the project postulates.

## Files

| File | Postulates |
|------|------------|
| `Postulates/AbstractGame.lean` | `Sanctions.AbstractGame.Params` (abstract two-player dynamic game — the project's CORE structure) |
| `Postulates/ShockedParams.lean` | `Sanctions.AbstractGame.ShockedParams` (atomless-shock extension: the purification kernel `κ` and its normalization — the shock-side assumption surface) |

(`SenderResponse.lean` — the write-only `JointMPE.SenderResponse`
interface, consumed by no theorem or operator — was moved to
`Theory/Bridges/` in the 2026-07-24 cleanup so this layer contains only
live assumption surface.)
-/

import Sanctions.Postulates.AbstractGame
import Sanctions.Postulates.ShockedParams
import Sanctions.Postulates.ParamsOfCube
