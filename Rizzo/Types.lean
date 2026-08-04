import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff

-------------------------
-- The syntax of types --
-- (A,B,F,G in Fig. 1) --
-------------------------

inductive Typ : Type where
| unit : Typ
| prod : Typ → Typ → Typ
| sum : Typ → Typ → Typ
| arr : Typ → Typ → Typ
| var : Nat → Typ
| delayA : Typ → Typ
| delayE : Typ → Typ
| mu : Typ → Typ
| sig : Typ → Typ
| chan : Typ → Typ
deriving DecidableEq

abbrev Typ.α₀ := Typ.var 0
abbrev Typ.α₁ := Typ.var 1

@[match_pattern] notation "𝟭" => Typ.unit
@[match_pattern] notation "◯" => Typ.delayE
@[match_pattern] notation "□" => Typ.delayA
@[match_pattern] notation "μ" => Typ.mu
@[match_pattern] infixr : 90 " ⟶ " => Typ.arr
@[match_pattern] infixr : 90 " ⨂ " => Typ.prod
@[match_pattern] infixr:90 (priority := high) " ⨁ " => Typ.sum

open Typ

--------------------------------------------------
-- Well-formed types with n free type variables --
-- (Fig. 2)                                     --
--------------------------------------------------

inductive Typ.Wf: Nat → Typ → Prop where
| unit : 𝟭.Wf n
| prod : A.Wf n → B.Wf n → (A ⨂ B).Wf n
| sum {A B : Typ} : A.Wf n → B.Wf n → (A ⨁ B).Wf n
| arr : A.Wf 0 → B.Wf n → (A ⟶ B).Wf n
| var : i < n → (var i).Wf n
| delayA : A.Wf 0 → (□ A).Wf n
| delayE : A.Wf 0 → (◯ A).Wf n
| mu : A.Wf (n+1) → (μ A).Wf n
| sig : A.Wf n → (sig A).Wf n
| chan : A.Wf 0 → (chan A).Wf n

notation:50 Θ:51 " ⊢ " A:51 " ∷type" => Typ.Wf Θ A
notation:50 " ⊢ " A:51 " ∷type" => Typ.Wf 0 A

abbrev Typ.Closed (A : Typ) := ⊢ A ∷type

-- Monotonicity of well-formedness in the number of variables in scope.
lemma Typ.Wf.mono {A : Typ} : A.Wf n → ∀ {m}, n ≤ m → A.Wf m := by
  intro W
  induction W <;> intro m Le <;> constructor <;> try omega
  all_goals solve_by_elim [Nat.succ_le_succ]

lemma Typ.Wf.weaken {A : Typ} : A.Wf n → A.Wf (n+1) := fun W => W.mono (Nat.le_succ n)
