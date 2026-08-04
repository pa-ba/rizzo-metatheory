/-
This module aggregates the formalisation of the machine behaviour of
the example programs:

  * `Examples.Machine.Reflect`: the proof-by-reflection
    infrastructure: fuel-driven evaluators `evalF` (for `⇓`) and
    `advF` (for `⇘`), each proved sound, so a concrete
    operational-semantics goal is discharged by *computing* the
    evaluator .
  * `Examples.Machine.Common`: the shared infrastructure
  * `Examples.Machine.Sample`: the `sample` program.
  * `Examples.Machine.Filter`: the `filter` program with the concrete
    predicate `isEven : Nat → Bool`.
  * `Examples.Machine.Switch`: the `switch` program.
-/

import Examples.Machine.Reflect
import Examples.Machine.Common
import Examples.Machine.Sample
import Examples.Machine.Filter
import Examples.Machine.Switch
