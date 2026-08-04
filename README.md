# Lean formalisation of Rizzo

This repository contains the Lean formalisation of Rizzo as presented
in the paper [*Simple Modal Types for Functional Reactive Programming*](https://bahr.io/pubs/entries/rizzo.html).

## How to check this formalisation

To check the formalisation, you can build this project by issuing
the command `lake build`. Alternatively, you can open the file
[Rizzo.lean](Rizzo.lean) in VS Code.

## Overview of theorems and lemmas from the paper

- [Theorem 4.1 (i)](Rizzo/MainResults.lean#L12)
- [Theorem 4.1 (ii)](Rizzo/MainResults.lean#L34)
- [Theorem 4.2 (part 1)](Rizzo/MainResults.lean#L130)
- [Theorem 4.2 (part 2)](Rizzo/MainResults.lean#L139)
- [Corollary 4.3 (i)](Rizzo/MainResults.lean#L100)
- [Corollary 4.3 (ii)](Rizzo/MainResults.lean#L113)
- [Corollary 4.4](Rizzo/MainResults.lean#L81)
- [Theorem 4.5](Rizzo/MainResults.lean#L149)

- [Lemma 5.1 (i)](Rizzo/Deterministic.lean#L257)
- [Lemma 5.1 (ii)](Rizzo/Deterministic.lean#L244)
- [Proposition 5.2 (i)](Rizzo/Preservation.lean#L62)
- [Proposition 5.2 (ii)](Rizzo/Preservation.lean#L202)
- [Proposition 5.2 (iii)](Rizzo/Preservation.lean#L312)
- [Proposition 5.2 (iv) part 1](Rizzo/Preservation.lean#L443)
- [Proposition 5.2 (iv) part 2](Rizzo/Preservation.lean#L455)
- [Proposition 5.2 (v)](Rizzo/Preservation.lean#L349)
- [Lemma 5.3](Rizzo/Typing.lean#L473)
- [Lemma 5.4 (part 1)](Rizzo/Preservation.lean#L402)
- [Lemma 5.4 (part 2)](Rizzo/Preservation.lean#L421)
- [Proposition 5.5 (i)](Rizzo/Progress.lean#L9)
- [Proposition 5.5 (ii)](Rizzo/Progress.lean#L25)
- [Proposition 5.5 (iii)](Rizzo/Progress.lean#L116)
- [Proposition 5.5 (iv)](Rizzo/Progress.lean#L207)
- [Proposition 5.5 (v)](Rizzo/Progress.lean#L191)
- [Lemma 5.6](Rizzo/Semantics.lean#L197)
- [Proposition 5.7](Rizzo/FundamentalProperty.lean#L14)
- [Lemma 5.8 (part 1)](Rizzo/LogicalRelation/Properties.lean#L346)
- [Lemma 5.8 (part 2)](Rizzo/LogicalRelation/Properties.lean#L353)
- [Lemma 5.8 (part 3)](Rizzo/LogicalRelation/Properties.lean#L541)
- [Corollary 5.9](Rizzo/FundamentalProperty.lean#L332)
- [Proposition 5.10](Rizzo/Clocks.lean#L724)
- [Proposition 5.11](Rizzo/Clocks.lean#L1008)

## Overview of definitions

- [Fig. 1, events](Rizzo/Env.lean#L17)
- [Fig. 1, terms](Rizzo/Terms.lean#L10)
- [Fig. 1, values](Rizzo/Terms.lean#L170)
- [Fig. 1, types](Rizzo/Types.lean#L6)
- [Fig. 2](Rizzo/Types.lean#L36)
- [Fig. 3](Rizzo/Typing.lean#L17) (These are in fact the typing rules
  for the generalised typing judgement from sect. 4.5. Fig. 3 is the
  special case for when H is empty.)
- [Sect. 2.2, clock of a delayed computation](Rizzo/Clocks.lean#L749)
- [Sect. 4, machine values](Rizzo/Terms.lean#L68)
- [Fig. 7, evaluation semantics](Rizzo/Semantics.lean#L14)
- [Fig. 7, fmap](Rizzo/Terms.lean#L120)
- [Fig. 8, advance semantics](Rizzo/Semantics.lean#L66)
- [Fig. 8, update semantics](Rizzo/Semantics.lean#L84)
- [Fig. 8, step semantics (reactive step)](Rizzo/Semantics.lean#L114)
- [Fig. 8, step semantics (init step)](Rizzo/Semantics.lean#L127)
- [Fig. 8, reactive evaluation semantics](Rizzo/Semantics.lean#L153)
- [Fig. 8, event typing judgement](Rizzo/Typing.lean#L106)
- [Fig. 8, ticked predicate](Rizzo/Env.lean#L123)
- [Sect. 4.2, clock of a delayed computation (in the machine)](Rizzo/Clocks.lean#L79)
- [Fig. 9, 'now' heap typing judgement](Rizzo/Typing.lean#L72)
- [Fig. 9, 'earlier' heap typing judgement](Rizzo/Typing.lean#L118)
- [Fig. 9, environment typing judgement](Rizzo/Typing.lean#L136)
- [Fig. 10, value logical relation](Rizzo/LogicalRelation/Core.lean#L14)
- [Fig. 10, term logical relation](Rizzo/LogicalRelation/Core.lean#L43)
- [Fig. 10, context logical relation](Rizzo/LogicalRelation/Core.lean#L98)
- [Fig. 10, heap logical relation](Rizzo/LogicalRelation/Properties.lean#L517)

## File overview of metatheory formalisation

The metatheory formalisation is found in the [Rizzo](Rizzo) directory.

### Main results

- Type preservation property of the operational semantics: 
  [Preservation](Rizzo/Preservation.lean)
- Progress property of the operational semantics:
  [Progress](Rizzo/Progress.lean)
- Main theorems (productivity and causality):
  [MainResults](Rizzo/MainResults.lean)
- Ticked-clock correspondence & clock/machine clock correspondence:
  [Clocks](Rizzo/Clocks.lean)

### Logical relation argument
The progress property is proved via a logical relations argument:
- Definition of the logical relation + lemmas:
  [LogicalRelation](Rizzo/LogicalRelation.lean)
- Proof of the fundamental property of the logical relation:
  [FundamentalProperty](Rizzo/FundamentalProperty.lean)

### Overview of remaining files
- Definition of the term syntax of the language:
  [Terms](Rizzo/Terms.lean)
- Definition of the Type syntax of the language:
  [Types](Rizzo/Types.lean)
- Definition of subsitutions + lemmas:
  [Substitution](Rizzo/Substitution.lean)
- Definition of type subsitutions + lemmas:
  [TypeSubstitution](Rizzo/TypeSubstitution.lean)
- Definition of the type system + lemmas:
  [Typing](Rizzo/Typing.lean)
- Additional definitions and lemmas about Mathlibs associative lists:
  [AList](Rizzo/AList.lean)
- Definition of environments (and heaps and channel contexts) +
  lemmas: [Env](Rizzo/Env.lean)
- Definition of the operational semantics:
  [Semantics](Rizzo/Semantics.lean)
- Proof that the semantics is deterministic:
  [Deterministic](Rizzo/Deterministic.lean)

## File overview of example formalisation

The formalisation of examples is found in the [Examples](Examples)
directory.

- [WellTyped](Examples/WellTyped) proves that the example Rizzo terms
  in the paper typecheck (see overview in
  [WellTyped.lean](Examples/WellTyped.lean)).
- [Machine](Examples/Machine) proves that the example machine runs in
  sect. 4.4 and Appendix A are correct according to the operational
  semantics (see overview in [Machine](Examples/Machine.lean)).