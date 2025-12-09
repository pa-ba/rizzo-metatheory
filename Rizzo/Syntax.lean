import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff

inductive Typ : Type where
| unit : Typ
| prod : Typ → Typ → Typ
| sum : Typ → Typ → Typ
| arr : Typ → Typ → Typ
| var : Typ
| delayA : Typ → Typ
| delayE : Typ → Typ
| mu : Typ → Typ
| sig : Typ → Typ
| chan : Typ → Typ


@[match_pattern] notation "◯" => Typ.delayE
@[match_pattern] notation "□" => Typ.delayA
@[match_pattern] notation "μ" => Typ.mu
@[match_pattern] infixr : 90 " ↠ " => Typ.arr
@[match_pattern] infixr : 90 " ⊗ " => Typ.prod
@[match_pattern] infixr : 90 " ⊕ " => Typ.sum

open Typ

-- Well-formed types. The Boolean indicates whether there is a free
-- variable.

inductive Typ.Wf: Bool → Typ → Prop where
| unit : unit.Wf n
| prod : A.Wf n → B.Wf n → (A ⊗ B).Wf n
| sum {A B : Typ} : A.Wf n → B.Wf n → (A ⊕ B).Wf n
| arr : A.Wf false → B.Wf false → (A ↠ B).Wf n
| var : var.Wf true
| delayA : A.Wf false → (□ A).Wf n
| delayE : A.Wf false → (◯ A).Wf n
| mu : A.Wf true → (mu A).Wf n
| sig : A.Wf n → (sig A).Wf n
| chan : A.Wf false → (chan A).Wf n

abbrev Typ.Closed (A : Typ) := A.Wf false
abbrev Typ.Open (A : Typ) := A.Wf true

@[simp]
def Typ.sub (A B : Typ) : Typ :=
  match A with
  | unit => unit
  | A1 ⊗ A2 => A1.sub B ⊗ A2.sub B
  | sum A1 A2 => A1.sub B ⊕ A2.sub B
  | A1 ↠ A2 => A1.sub B ↠ A2.sub B
  | var => B
  | □ A' => □ (A'.sub B)
  | ◯ A' => ◯ (A'.sub B)
  | μ A' => μ A'
  | sig A' => sig (A'.sub B)
  | chan A' => chan (A'.sub B)



lemma Typ.Wf.arr' : (A ↠ B).Open ↔ (A ↠ B).Closed := by
  constructor<;>  (intro W;cases W;solve_by_elim)

@[simp]
lemma Typ.sub_var {A : Typ} : A.sub Typ.var = A := by
  induction A <;> simp <;> grind



@[simp]
lemma Typ.sub_sub {A B C : Typ} : (A.sub B).sub C = A.sub (B.sub C) := by
  induction A <;> simp <;> grind

lemma Typ.sub_closed {A : Typ} : A.Closed → A.sub B = A := by
  induction A <;> intros WF <;> simp <;> cases WF<;> grind


lemma Typ.Wf.sub {A B : Typ} : A.Wf b' → B.Wf b → (A.sub B).Wf b := by
  intros WA WB
  induction WA  <;> try (simp;solve_by_elim)
  case arr | delayA | delayE | chan =>
    simp; constructor<;> (rw[Typ.sub_closed (by assumption)]; assumption)

lemma Typ.Wf.weaken {A: Typ} : A.Wf b → A.Open := by
  intros W
  induction W <;> solve_by_elim




abbrev Chan := Nat
abbrev Loc := Nat

inductive Term : Type where
  | unit : Term
  | pair : Term → Term → Term
  | in1 : Term → Term
  | in2 : Term → Term
  | lam : Term → Term
  | app : Term → Term → Term
  | case : Term → Term → Term → Term
  | pr1 : Term → Term
  | pr2 : Term → Term
  | var : Nat → Term
  | delay : Term → Term
  | never : Term
  | wait : Term → Term
  | newchan : Typ → Term
  | chan : Chan → Term
  | sync : Term → Term → Term
  | appE : Term → Term → Term
  | appA : Term → Term → Term
  | head : Term → Term
  | tail : Term → Term
  | sig : Typ → Term → Term → Term
  | cons : Typ → Term → Term
  | recur : Typ → Term → Term → Term
  | loc : Loc → Term
  | trig : Term → Term
  | fix : Term → Term

def Subs := List Term
open Term

-- Signal map function
-- ```
-- smap B : (A → B) → Sig A → Sig B
-- smap B = \ f . fix r . \ s . f (head s) :: r.appE (tail s)
-- ```

def Term.smap (B : Typ) : Term :=
  lam (fix (lam (((var 2).app (var 0).head).sig B ((var 1).appE (var 0).tail))))

-- fmap A B : (B' -> B) -> A[B'] -> A[B]
def Term.fmap (A B : Typ) : Term :=
  lam (lam (match A with
      | .var => (var 1).app (var 0)
      | A1 ⊗ A2 => (((fmap A1 B).app (var 1)).app (var 0).pr1).pair (((fmap A2 B).app (var 1)).app (var 0).pr2)
      | .sum A1 A2 => (var 0).case (((fmap A1 B).app (var 2)).app (var 0)).in1 (((fmap A2 B).app (var 2)).app (var 0)).in2
      | .sig A' => ((Term.smap (A'.sub B)).app ((fmap A' B).app (var 1))).app (var 0)
      | _ => var 0
  ))

inductive IsValue : Term → Prop
| unit : IsValue .unit
| loc : IsValue (loc l)
| chan : IsValue (chan κ)
| lam : IsValue (lam t)
| in1 : IsValue t → IsValue (in1 t)
| in2 : IsValue t → IsValue (in2 t)
| pair : IsValue s → IsValue t → IsValue (pair s t)
| wait : IsValue t → IsValue (wait t)
| appE : IsValue s → IsValue t → IsValue (appE s t)
| delay : IsValue (delay t)
| never : IsValue never
| tail : IsValue t → IsValue (tail t)
| sync : IsValue s → IsValue t → IsValue (sync s t)
| cons : IsValue t → IsValue (cons A t)
| trig : IsValue t → IsValue (trig t)

@[simp]
lemma IsValue.fmap : IsValue (fmap A B) := by
  cases A <;> simp[Term.fmap] <;> constructor
@[simp]
lemma IsValue.smap : IsValue (smap B) := by
  simp[Term.smap]; constructor

abbrev Val := {t : Term // IsValue t}

namespace Val

def pair (u v : Val) : Val := ⟨ Term.pair (u.val) (v.val) , IsValue.pair u.property v.property⟩
def unit : Val := ⟨ Term.unit, IsValue.unit ⟩
def loc (l : Loc) : Val := ⟨ Term.loc l, IsValue.loc ⟩
def chan (κ : Chan) : Val := ⟨ Term.chan κ, IsValue.chan⟩
def lam (t : Term) : Val := ⟨ Term.lam t, IsValue.lam ⟩
def in1 (v : Val) : Val := ⟨ Term.in1 v.val, IsValue.in1 v.property ⟩
def in2 (v : Val) : Val := ⟨ Term.in2 v.val, IsValue.in2 v.property ⟩
def wait (v : Val) : Val := ⟨ Term.wait v.val, IsValue.wait v.property ⟩
def appE (u v : Val) : Val := ⟨ Term.appE (u.val) (v.val) , IsValue.appE u.property v.property⟩
def delay (t : Term) : Val := ⟨ Term.delay t, IsValue.delay ⟩
def never : Val := ⟨ Term.never, IsValue.never ⟩
def tail (v : Val) : Val := ⟨ Term.tail v.val, IsValue.tail v.property ⟩
def sync (u v : Val) : Val := ⟨ Term.sync (u.val) (v.val) , IsValue.sync u.property v.property⟩
def cons (A : Typ) (v : Val) : Val := ⟨ Term.cons A v.val, IsValue.cons v.property ⟩
def trig (v : Val) : Val := ⟨Term.trig v.val, IsValue.trig v.prop⟩
def fmap (A B : Typ) : Val := ⟨Term.fmap A B, IsValue.fmap⟩
def smap (B : Typ) : Val := ⟨Term.smap B, IsValue.smap⟩

end Val
