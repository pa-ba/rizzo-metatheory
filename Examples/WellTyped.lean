/-
Example Rizzo terms, well-typed according to the `HasType` judgement.

This is an umbrella module re-exporting the well-typed examples:

  * `Examples.WellTyped.Common`: shared infrastructure
  * `Examples.WellTyped.Notation`: the `termdef`/`[rz| …]` surface
    syntax for writing terms with named variables
  * `Examples.WellTyped.Simple`: simple terms using neither `Sig` nor
    the later modalities
  * `Examples.WellTyped.SignalCombinators`: operations on signals and
     later modalities
  * `Examples.WellTyped.Programs`: terms that are used in
    `Examples.Machine`
  * `Examples.WellTyped.GUI`: a small GUI program over a recursive
    `Widget` type.
-/

import Examples.WellTyped.Common
import Examples.WellTyped.Notation
import Examples.WellTyped.Simple
import Examples.WellTyped.SignalCombinators
import Examples.WellTyped.Programs
import Examples.WellTyped.GUI
