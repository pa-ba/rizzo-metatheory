/-
Shared infrastructure for the well-typed example terms.
-/

import Rizzo.Typing

open Term Typ

variable {Γ : Ctx} {Δ : ChanCtx} {H : HeapTy} {A B : Typ}

----------------------------------------------------------------------
-- `let` as sugar for an immediate application
----------------------------------------------------------------------

/-- `let x = e in b`, encoded as `(λx. b) e`. -/
def Term.letIn (e b : Term) : Term := (lam b).app e

/-- Typing rule for `let`: bind `e ∷ A` (with `A` closed) and type the
body `b` in the extended context. -/
lemma HasType.letIn :
    A.Closed → Γ ⊢[Δ, H] e ∷ A → (A :: Γ) ⊢[Δ, H] b ∷ B →
    Γ ⊢[Δ, H] letIn e b ∷ B :=
  fun hA he hb => HasType.app (HasType.lam hA hb) he

----------------------------------------------------------------------
-- Church-style natural numbers, lists, booleans and option types
----------------------------------------------------------------------

/-- `Nat = μα. 1 + α`. -/
abbrev NatTy : Typ := μ (𝟭 ⨁ α₀)

/-- `List A = μα. 1 + (A × α)`. -/
abbrev ListTy (A : Typ) : Typ := μ (𝟭 ⨁ (A ⨂ α₀))

/-- `0 : Nat`. -/
abbrev Term.zero : Term := cons (𝟭 ⨁ α₀) (in1 unit)

/-- `succ n : Nat`. -/
abbrev Term.succ (n : Term) : Term := cons (𝟭 ⨁ α₀) (in2 n)

/-- `Bool = 1 + 1`. -/
abbrev BoolT : Typ := 𝟭 ⨁ 𝟭

/-- `Maybe A = A + 1`, with `just = in1 ·` and `nothing = in2 ()`. -/
abbrev MaybeT (A : Typ) : Typ := A ⨁ 𝟭

abbrev Term.just (t : Term) : Term := in1 t
abbrev Term.nothing : Term := in2 unit

---------------------------------------------------------------------
-- A reusable tactic for proving well-typedness of closed programs --
---------------------------------------------------------------------

macro "solve_wf" : tactic =>
  `(tactic|
    repeat' first
      | assumption
      | omega
      | exact Typ.Wf.unit
      | apply Typ.Wf.prod
      | apply Typ.Wf.sum
      | apply Typ.Wf.arr
      | apply Typ.Wf.delayA
      | apply Typ.Wf.delayE
      | apply Typ.Wf.sig
      | apply Typ.Wf.chan
      | apply Typ.Wf.mu
      | apply Typ.Wf.var
      | apply Typ.Wf.subAt
      | apply Typ.Wf.weaken)


lemma Typ.subAt_closed {A B : Typ} {k} : A.Closed → A.subAt k B = A :=
  fun h => h.subAt_ge (Nat.zero_le _)

open Lean Elab Tactic in
elab "solve_wf_grounded" : tactic => do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  if ty.hasExprMVar then throwError "solve_wf_grounded: goal has metavariables"
  else evalTactic (← `(tactic| solve_wf))

macro "norm_recty" : tactic =>
  `(tactic| set_option linter.unusedSimpArgs false in
      simp (disch := solve_wf_grounded) only
        [Typ.sub, ↓Typ.subAt_closed, ↓Typ.shift_closed, Typ.subAt, Typ.shift,
         reduceIte, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT])


macro "type_step" : tactic =>
  `(tactic|
    first
      | exact HasType.var rfl
      | (first
          | apply HasType.letIn
          | apply HasType.unit
          | apply HasType.lam
          | apply HasType.sig
          | apply HasType.app
          | apply HasType.appA
          | apply HasType.appE
          | apply HasType.pair
          | apply HasType.pr1
          | apply HasType.pr2
          | apply HasType.in1
          | apply HasType.in2
          | apply HasType.case
          | apply HasType.delay
          | apply HasType.head
          | apply HasType.tail
          | apply HasType.cons
          | apply HasType.recur
          | apply HasType.fix
          | apply HasType.select
          | apply HasType.wait
          | apply HasType.watch
          | apply HasType.never
          | apply HasType.newchan
          | apply HasType.loc
          | apply HasType.chan) <;> (try exact HasType.var rfl))

syntax "type_check" : tactic
syntax "type_check" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
syntax "type_check" " [" Lean.Parser.Tactic.simpLemma,* "]" " using "
  "[" term,* "]" : tactic
macro_rules
  | `(tactic| type_check) =>
      `(tactic| ((repeat' (first | type_step | norm_recty)) <;> solve_wf))
  | `(tactic| type_check [$args,*]) =>
      `(tactic| (simp only [$args,*];
                 (repeat' (first | type_step | norm_recty)) <;> solve_wf))

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| type_check [$args,*] using [$lems,*]) => do
      evalTactic (← `(tactic| simp only [$args,*]))
      let alts ← lems.getElems.mapM fun l => `(tacticSeq| apply $l)
      evalTactic (← `(tactic| repeat' (first
          | exact HasType.var rfl
          | first $[| $alts]*
          | type_step
          | norm_recty)))
      evalTactic (← `(tactic| all_goals solve_wf))
