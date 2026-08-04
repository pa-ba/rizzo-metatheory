/-
A surface syntax for writing the example `Term`s with named variables
instead of de Bruijn indices.
-/

import Examples.WellTyped.Common

open Lean

namespace RizzoNotation

declare_syntax_cat rzt

-- atoms
scoped syntax:max ident : rzt
scoped syntax:max num : rzt          -- a numeric literal (e.g. a `loc`/`chan` index)
scoped syntax:max "(" rzt ")" : rzt
scoped syntax:max "~" term:max : rzt

-- `{e}` marks a *meta* (type) argument in an application spine: `Term.scan {B} f b`
-- meta-applies `B` (a Lean term) and object-applies `f`, `b` — i.e.
-- `(Term.scan B) ⬝ f ⬝ b`, so no `⬝` is needed for the object arguments
scoped syntax:max "{" term "}" : rzt

-- tuple `(e₁, e₂, …, eₙ)` ↦ right-nested `Term.pair`
scoped syntax:max "(" rzt ", " rzt,+ ")" : rzt

-- application by juxtaposition (left associative, tightest)
scoped syntax:100 rzt:100 rzt:101 : rzt

-- the three explicit object-level applications
scoped syntax:65 rzt:65 " ⬝ " rzt:66 : rzt
scoped syntax:60 rzt:60 " ⊛ " rzt:61 : rzt
scoped syntax:60 rzt:60 " ⧁ " rzt:61 : rzt

-- `a ▷ b` (delayed application) ↦ the `Term.fmapE` combinator applied
scoped syntax:50 rzt:50 " ▷ " rzt:51 : rzt

-- signal cons:  `hd ::{A} tl`  ↦  `Term.sig A hd tl`
scoped syntax:55 rzt:56 " :: " "{" term "} " rzt:55 : rzt

-- patterns for `λ`/`case`/`let` binders: a name, a signal `(p :: q)`, or an
-- n-ary pair `(p₁, …, pₙ)`.  `(p :: q)` destructures with `head`/`tail`, a pair
-- with `pr1`/`pr2`; components are themselves patterns, so they nest.
declare_syntax_cat rzpat
scoped syntax Lean.binderIdent : rzpat
scoped syntax "(" rzpat " :: " rzpat ")" : rzpat
scoped syntax "(" rzpat ", " rzpat,+ ")" : rzpat

-- binders, with `.` as the separator
scoped syntax:10 "λ" rzpat+ " . " rzt:10 : rzt
scoped syntax:10 "fun" rzpat+ " . " rzt:10 : rzt
scoped syntax:10 "fix" Lean.binderIdent " . " rzt:10 : rzt
scoped syntax:10 "let " rzpat " = " rzt " in " rzt:10 : rzt

-- `case … of in1 x . … | in2 y . …`.  The `in1`/`in2` labels are parsed as
-- ordinary identifiers (not keyword tokens) so that the bare `Term` constructors
-- `in1`/`in2` stay usable everywhere else; the macro validates them.  Each branch
-- binder is a pattern, so `in1 (x :: xs) . …` destructures the injection payload.
scoped syntax:10 "case " rzt " of " ident rzpat " . " rzt
  " | " ident rzpat " . " rzt:10 : rzt

-- `case s of left x . … | right y . … | both u v . …`: matching on the result of
-- a `select`, of type `◯((A₁ + A₂) + (A₁ × A₂))`.  `left`/`right` select the
-- `in1 (in1 ·)` / `in1 (in2 ·)` cases (one side ticked); `both u v` selects the
-- `in2 ·` case (both ticked) and binds the pair's components via `pr1`/`pr2`.
-- `u`/`v` are patterns, so `both (x :: xs) (y :: ys)` destructures both signals.
scoped syntax:10 "case " rzt " of " "left " rzpat " . " rzt
  " | " "right " rzpat " . " rzt
  " | " "both " rzpat ppSpace rzpat " . " rzt:10 : rzt

-- `if c then t else e` ↦ `case c of in1 _ . t | in2 _ . e`  (Bool = 𝟭 ⊕ 𝟭, in1 = true)
scoped syntax:10 "if " rzt " then " rzt " else " rzt:10 : rzt

-- `recur {T} (p . s) arg`: the step `s` binds the unfolded value `p` (no `λ` — the
-- step is a fold, not a first-class function); the bracketed `T` is the result
-- *type*, written in Lean syntax (the same `{·}` type-argument notation as `::{A}`).
scoped syntax:10 "recur " "{" term "} " "(" Lean.binderIdent " . " rzt ")" rzt:max : rzt

-- entry point
scoped syntax:max "[rz|" rzt "]" : term

/-- The de Bruijn-free name of a binder (`_` ↦ the anonymous name, which never
matches a referenced identifier). -/
private def bname (b : TSyntax ``Lean.binderIdent) : Name :=
  match b with
  | `(binderIdent| $x:ident) => x.getId
  | _ => .anonymous

/-- Right-nested `Term.pair` from a tuple's (already translated) elements. -/
private partial def mkTuple : List (TSyntax `term) → MacroM (TSyntax `term)
  | [x] => return x
  | x :: rest => do `(Term.pair $x $(← mkTuple rest))
  | [] => Macro.throwUnsupported

mutual
/-- The leaves of a pattern, each paired with the projection tags (`head`/`tail`/
`pr1`/`pr2`) reaching it from the matched value (root-first). -/
private partial def patLeaves : TSyntax `rzpat → List (Name × List Name)
  | `(rzpat| $x:binderIdent) => [(bname x, [])]
  | `(rzpat| ($p :: $q)) =>
      (patLeaves p).map (fun (n, ts) => (n, `head :: ts)) ++
      (patLeaves q).map (fun (n, ts) => (n, `tail :: ts))
  | `(rzpat| ($p, $qs,*)) => pairLeaves (p :: qs.getElems.toList)
  | _ => []
/-- Leaves of a right-nested pair pattern `(p₁, …, pₙ)`. -/
private partial def pairLeaves : List (TSyntax `rzpat) → List (Name × List Name)
  | [p] => patLeaves p
  | p :: rest =>
      (patLeaves p).map (fun (n, ts) => (n, `pr1 :: ts)) ++
      (pairLeaves rest).map (fun (n, ts) => (n, `pr2 :: ts))
  | [] => []
end

/-- The `head`/`tail`/`pr1`/`pr2` projection named by `tag`, applied to `t`. -/
private def applyProj (tag : Name) (t : TSyntax `term) : MacroM (TSyntax `term) :=
  match tag with
  | `head => `(Term.head $t)
  | `tail => `(Term.tail $t)
  | `pr1  => `(Term.pr1 $t)
  | `pr2  => `(Term.pr2 $t)
  | _     => pure t

/-- Emit the destructuring `let`s binding a pattern's `leaves` (from `patLeaves`),
with the matched value at de Bruijn index `baseIdx`; then run `kont` with the
extended context.  (Each `let` shifts the matched value, hence `baseIdx + 1`.) -/
private partial def emitLeafLets (leaves : List (Name × List Name)) (baseIdx : Nat)
    (ctx : List Name) (kont : List Name → MacroM (TSyntax `term)) : MacroM (TSyntax `term) := do
  match leaves with
  | [] => kont ctx
  | (name, tags) :: rest =>
      let proj ← tags.foldlM (fun t tag => applyProj tag t) (← `(Term.var $(Lean.quote baseIdx)))
      `(Term.letIn $proj $(← emitLeafLets rest (baseIdx + 1) (name :: ctx) kont))

/-- The `Term` constructors, whose unqualified names clash with `Typ`/`List`
(`cons`, `head`, `tail`, `chan`, …); a free occurrence of one is emitted
`Term`-qualified to keep the meta-application unambiguous. -/
private def ctorNames : List Name :=
  [`unit, `pair, `in1, `in2, `lam, `app, `pr1, `pr2, `var, `delay, `never,
   `wait, `newchan, `chan, `select, `appE, `appA, `head, `tail, `sig, `cons,
   `loc, `watch]

/-- `Term`-qualify a free head identifier when it names a constructor (see
`ctorNames`), so the meta-application stays unambiguous. -/
private def qualifyHead (head : Ident) : Ident :=
  match head.getId.components.getLast? with
  | some c => if ctorNames.contains c then mkIdent (`Term ++ c) else head
  | none => head

/-- Is this spine argument a `{e}` meta-argument marker? -/
private def isBraceArg : TSyntax `rzt → Bool
  | `(rzt| {$_:term}) => true
  | _ => false

/-- The `Term` *constructors* (as opposed to combinators) that take *all* their
arguments — the type *and* the value(s) — at the meta (Lean) level: `cons {A} t`
is `Term.cons A t` and `newchan {A}` is `Term.newchan A`.  So in a `{T}`-braced
spine their plain args are meta-applied, not object-applied (`Term.app`) the way a
combinator's value arguments are.  (`recur`/`sig` carry a `{T}` type too but have
their own dedicated syntax.) -/
private def metaCtorNames : List Name := [`cons, `newchan]

/-- Does this spine head name a `metaCtorNames` constructor? -/
private def isMetaCtor (head : Ident) : Bool :=
  match head.getId.components.getLast? with
  | some c => metaCtorNames.contains c
  | none   => false

mutual

/-- Translate a surface term in context `ctx` (innermost binder first) to a
`Term`-valued Lean term with de Bruijn indices. -/
partial def expandRzt (ctx : List Name) : TSyntax `rzt → MacroM (TSyntax `term)
  | `(rzt| ($e)) => expandRzt ctx e
  | `(rzt| ($e, $es,*)) => do mkTuple (← ((#[e] ++ es.getElems).toList).mapM (expandRzt ctx))
  | `(rzt| ~$e:term) => return e
  | `(rzt| {$m:term}) => return m
  | `(rzt| $n:num) => `($n)
  | `(rzt| λ $xs:rzpat* . $b) => expandLam ctx xs.toList b
  | `(rzt| fun $xs:rzpat* . $b) => expandLam ctx xs.toList b
  | `(rzt| fix $r:binderIdent . $b) => do `(Term.fix $(← expandRzt (bname r :: ctx) b))
  | `(rzt| let $pat:rzpat = $e in $b) => do
      match pat with
      | `(rzpat| $x:binderIdent) =>                         -- plain `let x = e in b`
          `(Term.letIn $(← expandRzt ctx e) $(← expandRzt (bname x :: ctx) b))
      | _ =>                                                -- destructuring `let`
          -- if the RHS is a bound variable, bind the leaves off it directly;
          -- otherwise `let`-bind it first (anonymously) and destructure that
          match e with
          | `(rzt| $v:ident) =>
              match ctx.findIdx? (· == v.getId) with
              | some i => emitLeafLets (patLeaves pat) i ctx (fun ctx' => expandRzt ctx' b)
              | none   => do `(Term.letIn $(← expandRzt ctx e)
                  $(← emitLeafLets (patLeaves pat) 0 (.anonymous :: ctx) (fun ctx' => expandRzt ctx' b)))
          | _ => do `(Term.letIn $(← expandRzt ctx e)
              $(← emitLeafLets (patLeaves pat) 0 (.anonymous :: ctx) (fun ctx' => expandRzt ctx' b)))
  | `(rzt| case $sc of $l1:ident $x:rzpat . $e1 | $l2:ident $y:rzpat . $e2) => do
      unless [l1.getId, l2.getId] == [`in1, `in2] || [l1.getId, l2.getId] == [`in2, `in1] do
        Macro.throwErrorAt l1 "`case … of` branches must be labelled `in1` and `in2`"
      let sc' ← expandRzt ctx sc
      let e1' ← expandBranch ctx x e1
      let e2' ← expandBranch ctx y e2
      if l1.getId == `in1 then `(Term.case $sc' $e1' $e2') else `(Term.case $sc' $e2' $e1')
  | `(rzt| case $sc of left $x:rzpat . $eL | right $y:rzpat . $eR | both $u:rzpat $v:rzpat . $eB) => do
      -- a `select` result `◯((A₁+A₂)+(A₁×A₂))`: `left`/`right` nest under `in1`,
      -- `both u v` takes the `in2` pair apart (`u` ← `pr1`, `v` ← `pr2`)
      let sc' ← expandRzt ctx sc
      let eL' ← expandBranch (.anonymous :: ctx) x eL
      let eR' ← expandBranch (.anonymous :: ctx) y eR
      let bothLeaves := (patLeaves u).map (fun (n, ts) => (n, `pr1 :: ts)) ++
                        (patLeaves v).map (fun (n, ts) => (n, `pr2 :: ts))
      let eB' ← emitLeafLets bothLeaves 0 (.anonymous :: ctx) (fun ctx' => expandRzt ctx' eB)
      `(Term.case $sc' (Term.case (Term.var 0) $eL' $eR') $eB')
  | `(rzt| if $c then $t else $e) => do
      -- `Bool = 𝟭 ⊕ 𝟭`: each branch binds the (ignored) unit payload, so `t`/`e`
      -- are translated under an anonymous binder
      `(Term.case $(← expandRzt ctx c)
          $(← expandRzt (.anonymous :: ctx) t) $(← expandRzt (.anonymous :: ctx) e))
  | `(rzt| recur {$T:term} ($p:binderIdent . $s) $arg) => do
      let step' ← expandRzt (bname p :: ctx) s
      `(Term.recur $T $step' $(← expandRzt ctx arg))
  | `(rzt| $hd :: {$T:term} $tl) => do `(Term.sig $T $(← expandRzt ctx hd) $(← expandRzt ctx tl))
  | `(rzt| $a ⬝ $b) => do `(Term.app $(← expandRzt ctx a) $(← expandRzt ctx b))
  | `(rzt| $a ⊛ $b) => do `(Term.appA $(← expandRzt ctx a) $(← expandRzt ctx b))
  | `(rzt| $a ⧁ $b) => do `(Term.appE $(← expandRzt ctx a) $(← expandRzt ctx b))
  | `(rzt| $a ▷ $b) => do
      -- `Term.fmapE` is resolved at the use site (it lives in `WellTyped.GUI`, which
      -- this module does not import), so emit it with `mkIdent`, not a quotation
      `(Term.app (Term.app $(mkIdent `Term.fmapE) $(← expandRzt ctx a)) $(← expandRzt ctx b))
  | `(rzt| $x:ident) => do
      match ctx.findIdx? (· == x.getId) with
      | some i => `(Term.var $(quote i))
      | none   => `($x)
  | s@`(rzt| $_ $_) => expandApp ctx s
  | _ => Macro.throwUnsupported

/-- A `λ`/`fun` binder list.  A plain name is one `Term.lam`; a pattern binder is
a `lam` binding the (anonymous) matched value, then the destructuring `let`s. -/
partial def expandLam (ctx : List Name) (pats : List (TSyntax `rzpat))
    (b : TSyntax `rzt) : MacroM (TSyntax `term) := do
  match pats with
  | []        => expandRzt ctx b
  | pat :: rest =>
    match pat with
    | `(rzpat| $x:binderIdent) => `(Term.lam $(← expandLam (bname x :: ctx) rest b))
    | _ => `(Term.lam $(← emitLeafLets (patLeaves pat) 0 (.anonymous :: ctx)
              (fun ctx' => expandLam ctx' rest b)))

/-- A `case` branch binder.  The injection payload is already bound by `Term.case`,
so a plain name just extends the context, while a pattern destructures the
(anonymous) payload with the `let`s from `patLeaves`. -/
partial def expandBranch (ctx : List Name) (pat : TSyntax `rzpat)
    (b : TSyntax `rzt) : MacroM (TSyntax `term) := do
  match pat with
  | `(rzpat| $x:binderIdent) => expandRzt (bname x :: ctx) b
  | _ => emitLeafLets (patLeaves pat) 0 (.anonymous :: ctx) (fun ctx' => expandRzt ctx' b)

/-- An application spine `h a₁ … aₙ`.  When the head `h` is a bound variable this
is object-level application; when it is a free name it is a Lean
function/constructor applied to the (recursively translated) arguments.  A free
head whose spine contains a `{e}` *meta* marker is the mixed case: each `{e}` is
a meta (Lean) application and each plain argument an object (`Term.app`) one — so
`Term.scan {B} f b` ≡ `(Term.scan B) ⬝ f ⬝ b`. -/
partial def expandApp (ctx : List Name) (s : TSyntax `rzt) : MacroM (TSyntax `term) := do
  let (head, args) := flatten s #[]
  match head with
  | `(rzt| $x:ident) =>
      if ctx.contains x.getId then objApp (← expandRzt ctx head) args.toList ctx
      else if args.any isBraceArg then
        -- a `{T}`-braced spine: each `{m}` meta-applies the raw Lean term `m`; a
        -- plain arg is meta-applied too for a constructor head (`cons {A} t` ≡
        -- `Term.cons A t`), but object-applied for a combinator head (`scan {B} f`)
        let ctorHead := isMetaCtor x
        let mut t : TSyntax `term ← `($(qualifyHead x))
        for a in args do
          match a with
          | `(rzt| {$m:term}) => t ← `($t $m)
          | _ =>
              if ctorHead then t ← `($t $(← expandRzt ctx a))
              else             t ← `(Term.app $t $(← expandRzt ctx a))
        return t
      else metaApp x args ctx
  | _ => objApp (← expandRzt ctx head) args.toList ctx

/-- Flatten nested juxtaposition `((h a₁) a₂) …` into `(h, #[a₁, a₂, …])`. -/
partial def flatten (s : TSyntax `rzt) (acc : Array (TSyntax `rzt)) :
    TSyntax `rzt × Array (TSyntax `rzt) :=
  match s with
  | `(rzt| $f $a) => flatten f (#[a] ++ acc)
  | _ => (s, acc)

/-- Object-level application: fold `Term.app` over the spine. -/
partial def objApp (head : TSyntax `term) (args : List (TSyntax `rzt))
    (ctx : List Name) : MacroM (TSyntax `term) := do
  match args with
  | [] => return head
  | a :: rest => objApp (← `(Term.app $head $(← expandRzt ctx a))) rest ctx

/-- Meta-level application: a Lean function/constructor applied to translated
arguments (constructor heads are `Term`-qualified to stay unambiguous). -/
partial def metaApp (head : Ident) (args : Array (TSyntax `rzt))
    (ctx : List Name) : MacroM (TSyntax `term) := do
  let mut e : TSyntax `term ← `($(qualifyHead head))
  for a in args do
    e ← `($e $(← expandRzt ctx a))
  return e

end

macro_rules
  | `([rz| $e]) => expandRzt [] e

/-- `termdef Term.foo … := e` ≡ `def Term.foo … := [rz| e]` — define a `Term` with
the named-variable surface syntax. -/
scoped syntax "termdef " ident (ppSpace bracketedBinder)* (" : " term)? " := " rzt : command
macro_rules
  | `(termdef $id $bs* : $t := $body) => `(def $id $bs* : $t := [rz| $body])
  | `(termdef $id $bs* := $body)      => `(def $id $bs* := [rz| $body])

/-- `termabbrev` is to `abbrev` what `termdef` is to `def`. -/
scoped syntax "termabbrev " ident (ppSpace bracketedBinder)* (" : " term)? " := " rzt : command
macro_rules
  | `(termabbrev $id $bs* : $t := $body) => `(abbrev $id $bs* : $t := [rz| $body])
  | `(termabbrev $id $bs* := $body)      => `(abbrev $id $bs* := [rz| $body])

----------------------------------------------------------------------
-- Regression checks: pin the exact de Bruijn translation of each construct.
----------------------------------------------------------------------

section
open Term Typ

-- `λ`, and bound-variable juxtaposition is object application
example : [rz| λ x . x ] = lam (var 0) := rfl
example : [rz| λ f x . f x ] = lam (lam (app (var 1) (var 0))) := rfl
example : [rz| λ f x y . f x y ] = lam (lam (lam (app (app (var 2) (var 1)) (var 0)))) := rfl

-- free-headed juxtaposition is meta (Lean) application
example : [rz| λ s . head s ] = lam (head (var 0)) := rfl

-- the explicit applicative operators
example : [rz| λ a b . a ⬝ b ] = lam (lam (app (var 1) (var 0))) := rfl
example : [rz| λ a b . a ⊛ b ] = lam (lam (appA (var 1) (var 0))) := rfl
example : [rz| λ a b . a ⧁ b ] = lam (lam (appE (var 1) (var 0))) := rfl

-- signal cons carries the element type
example : [rz| λ h t . h ::{𝟭} t ] = lam (lam (sig 𝟭 (var 1) (var 0))) := rfl

-- the same `{·}` type-argument notation builds the `cons`/`newchan` constructors;
-- a constructor's plain (value) args are meta- not object-applications
example : [rz| λ t . cons {𝟭} t ] = lam (Term.cons 𝟭 (var 0)) := rfl
example : [rz| λ t . cons {𝟭 ⨁ 𝟭} (in2 t) ] = lam (Term.cons (𝟭 ⨁ 𝟭) (Term.in2 (var 0))) := rfl
example : [rz| newchan {𝟭} ] = Term.newchan 𝟭 := rfl
example : [rz| λ x . (newchan {𝟭}, x) ] = lam (pair (Term.newchan 𝟭) (var 0)) := rfl

-- `fix` binds the recursor without an extra `lam`
example : [rz| fix r . λ x . r x ] = Term.fix (lam (app (var 1) (var 0))) := rfl

-- `let`
example : [rz| λ a . let x = a in x ] = lam (letIn (var 0) (var 0)) := rfl

-- `recur`: the step binds the unfolded value; no `lam` is emitted around it.  The
-- result type is a `{·}`-bracketed Lean term (here `𝟭`).
example : [rz| λ a . recur {𝟭} (p . p) a ] = lam (Term.recur 𝟭 (var 0) (var 0)) := rfl

-- `case`: branches bind the injection payloads; labels work in either order
example : [rz| case unit of in1 x . x | in2 y . y ] = Term.case unit (var 0) (var 0) := rfl
example : [rz| case unit of in2 y . unit | in1 x . x ] = Term.case unit (var 0) unit := rfl

-- pattern binders desugar via `head`/`tail` (signals) and `pr1`/`pr2` (pairs),
-- in both `λ` and `case` branches
example : [rz| λ (x :: xs) . pair x xs ]
        = [rz| λ s . let x = head s in let xs = tail s in pair x xs ] := rfl
example : [rz| λ (x , y) . pair x y ]
        = [rz| λ s . let x = pr1 s in let y = pr2 s in pair x y ] := rfl
example : [rz| λ f (x :: xs) . pair (f x) xs ]
        = [rz| λ f s . let x = head s in let xs = tail s in pair (f x) xs ] := rfl
example : [rz| case unit of in1 (x :: xs) . pair x xs | in2 y . y ]
        = [rz| case unit of in1 s . let x = head s in let xs = tail s in pair x xs | in2 y . y ] := rfl
-- patterns nest, are n-ary, and work in a destructuring `let` (off a variable)
example : [rz| λ ((a :: b) :: c) . pair a (pair b c) ]
        = [rz| λ s . let a = head (head s) in let b = tail (head s) in let c = tail s in pair a (pair b c) ] := rfl
example : [rz| λ (a, b, c) . pair a (pair b c) ]
        = [rz| λ s . let a = pr1 s in let b = pr1 (pr2 s) in let c = pr2 (pr2 s) in pair a (pair b c) ] := rfl
example : [rz| λ s . let (x :: xs) = s in pair x xs ]
        = [rz| λ s . let x = head s in let xs = tail s in pair x xs ] := rfl

-- `select`-result matching: `left`/`right` nest under `in1`; `both u v` takes the
-- `in2` pair apart with `pr1`/`pr2`
example : [rz| λ s . case s of left x . x | right y . y | both u v . pair u v ]
        = [rz| λ s . case s of in1 q . (case q of in1 x . x | in2 y . y)
                             | in2 w . let u = pr1 w in let v = pr2 w in pair u v ] := rfl

-- `if c then t else e` is `case` on `Bool = 𝟭 ⊕ 𝟭` (in1 = true)
example : [rz| λ x . if x then just x else nothing ]
        = [rz| λ x . case x of in1 _ . just x | in2 _ . nothing ] := rfl

-- tuples are right-nested `pair`s
example : [rz| (unit, never) ] = pair unit never := rfl
example : [rz| λ a b c . (a, b, c) ] = lam (lam (lam (pair (var 2) (pair (var 1) (var 0))))) := rfl

-- `{e}` meta-applies a (type) argument; plain spine args stay object — so the
-- explicit `⬝` is unnecessary for a combinator's value arguments
example : [rz| smap {B} f s ] = [rz| smap B ⬝ f ⬝ s ] := rfl

end

----------------------------------------------------------------------
-- Values: the same surface syntax, producing a `MVal` (a term + an `IsMValue`
-- proof) instead of a bare `Term`.
----------------------------------------------------------------------

/-- A value is in particular a term — coerce by forgetting the `IsMValue` proof.
This lets a value written with `[rzv| …]` mention other values (e.g. a stored
signal tail) in a term position; the dropped proof is recovered by `is_value`
(via `Subtype.property`).  `scoped`, so it is active only where the value notation
is in use. -/
scoped instance : Coe MVal _root_.Term := ⟨Subtype.val⟩

/-- Prove an `IsMValue` goal by walking the value constructors, using a sub-value's
own proof (`Subtype.property`) at a coerced `MVal`, and the standard value lemmas
for `smap`/`fmap`.  Shared by the runtime numerals (`n0..n3`) and the `[rzv| …]`
value notation. -/
macro "is_value" : tactic =>
  `(tactic|
    ((repeat' first
        | assumption
        | exact IsMValue.unit
        | exact IsMValue.loc
        | exact IsMValue.chan
        | exact IsMValue.lam
        | exact IsMValue.delay
        | exact IsMValue.never
        | exact IsMValue.smap
        | exact IsMValue.fmap₁
        | exact IsMValue.fmap
        | exact Subtype.property _
        | apply IsMValue.in1
        | apply IsMValue.in2
        | apply IsMValue.pair
        | apply IsMValue.wait
        | apply IsMValue.appE
        | apply IsMValue.tail
        | apply IsMValue.select
        | apply IsMValue.cons
        | apply IsMValue.watch);
      done))

-- `[rzv| e]` elaborates `e` (the very same surface syntax as `[rz| e]`) to a `MVal`:
-- the underlying term `[rz| e]` together with its `IsMValue` proof.
scoped syntax:max "[rzv|" rzt "]" : term
macro_rules
  | `([rzv| $e]) => do `((⟨$(← expandRzt [] e), by is_value⟩ : MVal))

/-- `valdef Term.foo … := e` ≡ `def foo … := [rzv| e]` — the `MVal` analogue of
`termdef`. -/
scoped syntax "valdef " ident (ppSpace bracketedBinder)* (" : " term)? " := " rzt : command
macro_rules
  | `(valdef $id $bs* : $t := $body) => `(def $id $bs* : $t := [rzv| $body])
  | `(valdef $id $bs* := $body)      => `(def $id $bs* := [rzv| $body])

----------------------------------------------------------------------
-- Regression checks for the value notation.
----------------------------------------------------------------------

section
open Term Typ

-- `[rzv| e]` packages `[rz| e]` with its value proof: the `.val` is unchanged
example : ([rzv| (unit, never) ]).val = [rz| (unit, never) ] := rfl
example : ([rzv| λ x . x x ]).val = lam (app (var 0) (var 0)) := rfl
example : ([rzv| in1 (wait (chan 0)) ]).val = in1 (wait (chan 0)) := rfl
example : ([rzv| cons {𝟭} unit ]).val = cons 𝟭 unit := rfl
example : ([rzv| delay (λ x . x x) ⧁ wait (chan 0) ]).val
        = appE (delay (lam (app (var 0) (var 0)))) (wait (chan 0)) := rfl

-- a value may reference another value in a term position (coerced via `.val`)
example (v : MVal) : ([rzv| (v, unit) ]).val = pair v.val unit := rfl
example (v : MVal) : ([rzv| delay unit ⧁ v ]).val = appE (delay unit) v.val := rfl

end
