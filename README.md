# Lean formalisation of Rizzo

This repository contains the Lean formalisation of Rizzo as presented
in the paper [*Simple Modal Types for Functional Reactive Programming*](https://bahr.io/pubs/entries/rizzo.html).

## Overview of theorems and lemmas from the paper

- [Theorem 4.1 (i)](Rizzo/StepSequence.lean#L9)
- [Theorem 4.1 (ii)](Rizzo/StepSequence.lean#L41)
- [Theorem 4.2 (part 1)](Rizzo/StepSequence.lean#L96)
- [Theorem 4.2 (part 2)](Rizzo/StepSequence.lean#L105)
- [Theorem 4.3](Rizzo/StepSequence.lean#L115)

- [Lemma 5.1 (i)](Rizzo/Deterministic.lean#L277)
- [Lemma 5.1 (ii)](Rizzo/Deterministic.lean#L264)
- [Proposition 5.2 (i)](Rizzo/Preservation.lean#L56)
- [Proposition 5.2 (ii)](Rizzo/Preservation.lean#L238)
- [Proposition 5.2 (iii)](Rizzo/Preservation.lean#L343)
- [Proposition 5.2 (iv) part 1](Rizzo/Preservation.lean#L475)
- [Proposition 5.2 (iv) part 2](Rizzo/Preservation.lean#L487)
- [Proposition 5.2 (v)](Rizzo/Preservation.lean#L460)
- [Lemma 5.3](Rizzo/Typing.lean#L183)
- [Lemma 5.4 (part 1)](Rizzo/Preservation.lean#L430)
- [Lemma 5.4 (part 2)](Rizzo/Preservation.lean#L449)
- [Proposition 5.5 (i)](Rizzo/Progress.lean#L12)
- [Proposition 5.5 (ii)](Rizzo/Progress.lean#L27)
- [Proposition 5.5 (iii)](Rizzo/Progress.lean#L119)
- [Proposition 5.5 (iv)](Rizzo/Progress.lean#L210)
- [Proposition 5.5 (v)](Rizzo/Progress.lean#L194)
- [Lemma 5.6](Rizzo/Semantics.lean#L134)
- [Proposition 5.7](Rizzo/FundamentalProperty.lean#L12)
- [Lemma 5.8 (part 1)](Rizzo/LogicalRelation.lean#L473)
- [Lemma 5.8 (part 2)](Rizzo/LogicalRelation.lean#L482)
- [Lemma 5.8 (part 3)](Rizzo/LogicalRelation.lean#L558)
- [Corollary 5.9](Rizzo/FundamentalProperty.lean#L413)

## File overview

### Main results

- Type preservation property of the operational semantics: 
  [Preservation](Rizzo/Preservation.lean)
- Progress property of the operational semantics:
  [Progress](Rizzo/Progress.lean)
- Main theorems (productivity and causality):
  [StepSequence](Rizzo/StepSequence.lean)

### Logical relation argument
The progress property is proved via a logical relations argument:
- Definition of the logical relation + lemmas:
  [LogicalRelation](Rizzo/LogicalRelation.lean)
- Proof of the fundamental property of the logical relation:
  [FundamentalProperty](Rizzo/FundamentalProperty.lean)

### Overview of remaining files
- Definition of the syntax of the language:
  [Syntax](Rizzo/Syntax.lean)
- Definition of subsitutions + lemmas:
  [Substitution](Rizzo/Substitution.lean)
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
