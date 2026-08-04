/-
Simple well-typed example terms
-/

import Examples.WellTyped.Notation

open Term Typ RizzoNotation

variable {Γ : Ctx} {Δ : ChanCtx} {H : HeapTy} {A : Typ}


----------------------------------------------------------------------
-- List A = μα. 1 + (A × α):  nil : List A  and  cons : A → List A → List A
----------------------------------------------------------------------

abbrev Term.nilL (A : Typ) : Term := cons (𝟭 ⨁ (A ⨂ α₀)) (in1 unit)
termabbrev Term.consL (A : Typ) : Term :=
  λ hd tl . cons {𝟭 ⨁ (A ⨂ α₀)} (in2 (hd, tl))

lemma HasType.nilL : A.Closed → Γ ⊢[Δ, H] nilL A ∷ ListTy A := by
  intro hA; type_check [Term.nilL]

lemma HasType.consL :
    A.Closed → Γ ⊢[Δ, H] consL A ∷ A ⟶ ListTy A ⟶ ListTy A := by
  intro hA; type_check [Term.consL]

----------------------------------------------------------------------
-- snoc : List A → A → List A
----------------------------------------------------------------------

termdef Term.snoc (A : Typ) : Term :=
  λ xs y . recur {ListTy A} (p .
    case p of
      in1 _ . consL {A} y (nilL A)
    | in2 (x, (_, rec)) . consL {A} x rec) xs

lemma HasType.snoc :
    A.Closed → Γ ⊢[Δ, H] snoc A ∷ ListTy A ⟶ A ⟶ ListTy A := by
  intro hA; type_check [Term.snoc]

----------------------------------------------------------------------
-- length : List A → Nat
----------------------------------------------------------------------

termdef Term.length : Term :=
  λ xs . recur {NatTy} (p .
    case p of in1 _ . zero | in2 q . succ (pr2 (pr2 q))) xs

lemma HasType.length :
    A.Closed → Γ ⊢[Δ, H] length ∷ ListTy A ⟶ NatTy := by
  intro hA; type_check [Term.length]

----------------------------------------------------------------------
-- isEven : Nat → Bool
----------------------------------------------------------------------

termdef Term.isEven : Term :=
  λ n . recur {BoolT} (p .
    case p of
      in1 _ . in1 unit
    | in2 q . case pr2 q of in1 _ . in2 unit | in2 _ . in1 unit) n

lemma HasType.isEven : Γ ⊢[Δ, H] isEven ∷ NatTy ⟶ BoolT := by
  type_check [Term.isEven]
