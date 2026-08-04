import Rizzo.TypeSubstitution

open Typ

abbrev Chan := Nat
abbrev Loc := Nat

-------------------------------
-- The syntax of Rizzo terms --
-- (s, t in Fig. 1)          --
-------------------------------


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
  | select : Term → Term → Term
  | appE : Term → Term → Term
  | appA : Term → Term → Term
  | head : Term → Term
  | tail : Term → Term
  | sig : Typ → Term → Term → Term
  | cons : Typ → Term → Term
  | recur : Typ → Term → Term → Term
  | loc : Loc → Term
  | watch : Term → Term
  | fix : Term → Term
deriving DecidableEq

def Subs := List Term


abbrev Term.x₀ : Term := var 0
abbrev Term.x₁ : Term := var 1
abbrev Term.x₂ : Term := var 2

open Term


-- Signal map function

def Term.smap (B : Typ) : Term :=
  lam (fix (lam ((x₂.app x₀.head).sig B (x₁.appE x₀.tail))))

-- `nlam n t` wraps `t` in `n` lambdas
def Term.nlam : Nat → Term → Term
  | 0, t => t
  | n+1, t => lam (Term.nlam n t)

def Term.apps (f : Term) : List Term → Term
  | [] => f
  | a :: as => Term.apps (f.app a) as

------------------------------------------------------------------
-- Machine values, i.e. values produced by evaluation semantics --
-- (p, q in the grammar in sect. 4)                           --
------------------------------------------------------------------

inductive IsMValue : Term → Prop
| unit : IsMValue .unit
| loc : IsMValue (loc l)
| chan : IsMValue (chan κ)
| lam : IsMValue (lam t)
| in1 : IsMValue t → IsMValue (in1 t)
| in2 : IsMValue t → IsMValue (in2 t)
| pair : IsMValue s → IsMValue t → IsMValue (pair s t)
| wait : IsMValue (wait (chan κ))
| appE : IsMValue s → IsMValue t → IsMValue (appE s t)
| delay : IsMValue (delay t)
| never : IsMValue never
| tail : IsMValue (tail (loc l))
| select : IsMValue s → IsMValue t → IsMValue (select s t)
| cons : IsMValue t → IsMValue (cons A t)
| watch : IsMValue (watch (loc l))

lemma IsMValue.nlam_lam : IsMValue (Term.nlam n (Term.lam t)) := by
  cases n <;> simp [Term.nlam] <;> exact IsMValue.lam
@[simp]
lemma IsMValue.smap : IsMValue (smap B) := by
  simp[Term.smap]; constructor

abbrev MVal := {t : Term // IsMValue t}

namespace MVal

def pair (u v : MVal) : MVal := ⟨ Term.pair (u.val) (v.val) , IsMValue.pair u.property v.property⟩
def unit : MVal := ⟨ Term.unit, IsMValue.unit ⟩
def loc (l : Loc) : MVal := ⟨ Term.loc l, IsMValue.loc ⟩
def chan (κ : Chan) : MVal := ⟨ Term.chan κ, IsMValue.chan⟩
def lam (t : Term) : MVal := ⟨ Term.lam t, IsMValue.lam ⟩
def in1 (v : MVal) : MVal := ⟨ Term.in1 v.val, IsMValue.in1 v.property ⟩
def in2 (v : MVal) : MVal := ⟨ Term.in2 v.val, IsMValue.in2 v.property ⟩
def wait (κ : Chan) : MVal := ⟨ Term.wait (Term.chan κ), IsMValue.wait ⟩
def appE (u v : MVal) : MVal := ⟨ Term.appE (u.val) (v.val) , IsMValue.appE u.property v.property⟩
def delay (t : Term) : MVal := ⟨ Term.delay t, IsMValue.delay ⟩
-- MVal.never is not used but let's keep it for completeness.
def never : MVal := ⟨ Term.never, IsMValue.never ⟩
def tail (l : Loc) : MVal := ⟨ Term.tail (Term.loc l), IsMValue.tail ⟩
def select (u v : MVal) : MVal := ⟨ Term.select (u.val) (v.val) , IsMValue.select u.property v.property⟩
def cons (A : Typ) (v : MVal) : MVal := ⟨ Term.cons A v.val, IsMValue.cons v.property ⟩
def watch (l : Loc) : MVal := ⟨Term.watch (Term.loc l), IsMValue.watch⟩
def smap (B : Typ) : MVal := ⟨Term.smap B, IsMValue.smap⟩

end MVal

------------------------
-- Definition of fmap --
-- (bottom of Fig. 7) --
------------------------

-- N-ary functorial map.  `fmap A Cs` is the action of the polynomial
-- functor `A` (free type variables `var 0 … var (m-1)`, `m =
-- Cs.length`) on a family of `m` functions, one per variable.
def Term.fmap (A : Typ) (Cs : List Typ) : Term :=
  let m := Cs.length
  let fns : List Term := (List.range m).map (fun i => var (m - i))
  let fns1 : List Term := (List.range m).map (fun i => var (m + 1 - i))
  let fns2 : List Term := lam (x₀.pr2) :: fns1
  nlam m (lam (match A with
    | Typ.var i => if i < m then (var (m - i)).app x₀ else x₀
    | 𝟭 => x₀
    | A1 ⨂ A2 =>
        (((fmap A1 Cs).apps fns).app x₀.pr1).pair
        (((fmap A2 Cs).apps fns).app x₀.pr2)
    | A1 ⨁ A2 =>
        x₀.case
          (((fmap A1 Cs).apps fns1).app x₀).in1
          (((fmap A2 Cs).apps fns1).app x₀).in2
    | _ ⟶ A2 =>
        lam (((fmap A2 Cs).apps fns1).app (x₁.app x₀))
    | □ _ => x₀
    | ◯ _ => x₀
    | Typ.sig A' =>
        ((smap (A'.substAll Cs)).app ((fmap A' Cs).apps fns)).app x₀
    | μ A' =>
        let Cs' := Cs.map (Typ.shift 0)
        let A'' := A'.substAll (α₀ :: Cs')
        recur (μ A'') (cons A'' (((fmap A' (μ A'' :: Cs')).apps fns2).app x₀))  x₀
    | _ => x₀
  ))

-- `fmap₁ A C : (B ⟶ C) ⟶ A[0 := B] ⟶ A[0 := C]` is the functorial action
-- of `A` in its variable `var 0`.
def Term.fmap₁ (A C : Typ) : Term := Term.fmap A [C]

@[simp]
lemma IsMValue.fmap : IsMValue (fmap A Cs) := by
  unfold Term.fmap; exact IsMValue.nlam_lam
@[simp]
lemma IsMValue.fmap₁ : IsMValue (fmap₁ A C) := by
  simp only [Term.fmap₁]; exact IsMValue.fmap

def MVal.fmap (A : Typ) (Cs : List Typ) : MVal := ⟨Term.fmap A Cs, IsMValue.fmap⟩
def MVal.fmap₁ (A C : Typ) : MVal := ⟨Term.fmap₁ A C, IsMValue.fmap₁⟩

----------------------------------------------------------------------
-- Values, i.e values produced by the reactive evaluation semantics --
-- (v, w in Fig. 1)
----------------------------------------------------------------------

inductive IsValue : Term → Prop
| unit : IsValue .unit
| chan : IsValue (chan κ)
| lam : IsValue (lam t)
| in1 : IsValue t → IsValue (in1 t)
| in2 : IsValue t → IsValue (in2 t)
| pair : IsValue s → IsValue t → IsValue (pair s t)
| wait : IsValue (wait (chan κ))
| appE : IsValue s → IsValue t → IsValue (appE s t)
| delay : IsValue (delay t)
| never : IsValue never
| select : IsValue s → IsValue t → IsValue (select s t)
| cons : IsValue t → IsValue (cons A t)
| watch : IsValue t → IsValue (watch t)
| sig : IsValue v → IsValue w → IsValue (sig A v w)
