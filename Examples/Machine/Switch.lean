/-
The `switch` example machine execution.
-/

import Examples.Machine.Common

open Term

variable (Δ : ChanCtx)


---------------
-- init step --
---------------

abbrev n5 : MVal :=
  ⟨Term.succ (Term.succ (Term.succ (Term.succ (Term.succ Term.zero)))), by is_value⟩

open RizzoNotation in
valdef swTail : MVal :=
  delay ((λ r' y . case y of left z . r' z (~(sigTail NatTy κ₂).val)
                          | right d' . d'
                          | both _ d' . d')
          ⬝ (~(Term.switch NatTy)))
    ⧁ select (tail (loc 1)) (~(sigTail NatTy κ₂).val)

def η_switch₀ : Heap :=
  ((∅ : Heap).concat 2 (mksig NatTy n0 false swTail) (by fresh_loc)).concat
    1 (mksig NatTy n0 false (sigTail NatTy κ₁)) (by fresh_loc)

theorem switch_init :
    (Term.switchProg, Δ) init⟹ (MVal.loc 2, η_switch₀, Δ) := by
  apply InitStep.init
  eval_refl

------------
-- step 1 --
------------

def η_switch₁ : Heap :=
  ((((∅ : Heap).concat 2 (mksig NatTy n1 true swTail) (by fresh_loc)).concat
    4 (mksig NatTy n1 false swTail) (by fresh_loc)).concat
    1 (mksig NatTy n1 true (sigTail NatTy κ₁)) (by fresh_loc)).concat
    3 (mksig NatTy n1 false (sigTail NatTy κ₁)) (by fresh_loc)

theorem switch_react₁ :
    (MVal.loc 2, η_switch₀, Δ) [κ₁ ↦ n1]⟹ (MVal.loc 2, η_switch₁, Δ) := by
  apply ReactStep.react
  case D => side
  case D' => side
  simp only [η_switch₀]
  update_tac_refl

------------
-- step 2 --
------------

def η_switch₂ : Heap :=
  ((((((((∅ : Heap).concat 2 (mksig NatTy n2 true swTail) (by fresh_loc)).concat
    8 (mksig NatTy n2 false swTail) (by fresh_loc)).concat
    4 (mksig NatTy n2 true swTail) (by fresh_loc)).concat
    7 (mksig NatTy n2 false swTail) (by fresh_loc)).concat
    1 (mksig NatTy n2 true (sigTail NatTy κ₁)) (by fresh_loc)).concat
    6 (mksig NatTy n2 false (sigTail NatTy κ₁)) (by fresh_loc)).concat
    3 (mksig NatTy n2 true (sigTail NatTy κ₁)) (by fresh_loc)).concat
    5 (mksig NatTy n2 false (sigTail NatTy κ₁)) (by fresh_loc)

theorem switch_react₂ :
    (MVal.loc 2, η_switch₁, Δ) [κ₁ ↦ n2]⟹ (MVal.loc 2, η_switch₂, Δ) := by
  apply ReactStep.react
  case D => side
  case D' => side
  simp only [η_switch₁]
  update_tac_refl

------------
-- step 3 --
------------

def η_switch₃ : Heap :=
  ((((((((((((∅ : Heap).concat 2 (mksig NatTy n5 true (sigTail NatTy κ₂)) (by fresh_loc)).concat
    12 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    8 (mksig NatTy n5 true (sigTail NatTy κ₂)) (by fresh_loc)).concat
    11 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    4 (mksig NatTy n5 true (sigTail NatTy κ₂)) (by fresh_loc)).concat
    10 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    7 (mksig NatTy n5 true (sigTail NatTy κ₂)) (by fresh_loc)).concat
    9 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    1 (mksig NatTy n2 false (sigTail NatTy κ₁)) (by fresh_loc)).concat
    6 (mksig NatTy n2 false (sigTail NatTy κ₁)) (by fresh_loc)).concat
    3 (mksig NatTy n2 false (sigTail NatTy κ₁)) (by fresh_loc)).concat
    5 (mksig NatTy n2 false (sigTail NatTy κ₁)) (by fresh_loc)

theorem switch_react₃ :
    (MVal.loc 2, η_switch₂, Δ) [κ₂ ↦ n5]⟹ (MVal.loc 2, η_switch₃, Δ) := by
  apply ReactStep.react
  case D => side
  case D' => side
  simp only [η_switch₂]
  update_tac_refl

------------
-- step 4 --
------------

def η_switch₄ : Heap :=
  ((((((((((((((((∅ : Heap).concat 2 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    12 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    8 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    11 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    4 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    10 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    7 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    9 (mksig NatTy n5 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    1 (mksig NatTy n3 true (sigTail NatTy κ₁)) (by fresh_loc)).concat
    16 (mksig NatTy n3 false (sigTail NatTy κ₁)) (by fresh_loc)).concat
    6 (mksig NatTy n3 true (sigTail NatTy κ₁)) (by fresh_loc)).concat
    15 (mksig NatTy n3 false (sigTail NatTy κ₁)) (by fresh_loc)).concat
    3 (mksig NatTy n3 true (sigTail NatTy κ₁)) (by fresh_loc)).concat
    14 (mksig NatTy n3 false (sigTail NatTy κ₁)) (by fresh_loc)).concat
    5 (mksig NatTy n3 true (sigTail NatTy κ₁)) (by fresh_loc)).concat
    13 (mksig NatTy n3 false (sigTail NatTy κ₁)) (by fresh_loc)

theorem switch_react₄ :
    (MVal.loc 2, η_switch₃, Δ) [κ₁ ↦ n3]⟹ (MVal.loc 2, η_switch₄, Δ) := by
  apply ReactStep.react
  case D => side
  case D' => side
  simp only [η_switch₃]
  update_tac_refl

-----------------------------
-- full reactive execution --
-----------------------------

def Δ_switch : ChanCtx :=
  ((∅ : ChanCtx).concat κ₁ NatTy (by fresh_loc)).concat κ₂ NatTy (by fresh_loc)

example :
    (Term.switchProg, Δ_switch)
      [ [κ₁ ↦ n3, κ₂ ↦ n5, κ₁ ↦ n2, κ₁ ↦ n1] ]⟹+ (MVal.loc 2, η_switch₄, Δ_switch) := by
  have e1 : ⊢[Δ_switch] (κ₁ ↦ n1) ∷Event := ⟨NatTy, by rfl, by type_check⟩
  have e2 : ⊢[Δ_switch] (κ₁ ↦ n2) ∷Event := ⟨NatTy, by rfl, by type_check⟩
  have e3 : ⊢[Δ_switch] (κ₂ ↦ n5) ∷Event := ⟨NatTy, by rfl, by type_check⟩
  have e4 : ⊢[Δ_switch] (κ₁ ↦ n3) ∷Event := ⟨NatTy, by rfl, by type_check⟩
  exact Steps.react (Steps.react (Steps.react (Steps.react
      (Steps.init (switch_init Δ_switch))
      e1 (switch_react₁ Δ_switch))
      e2 (switch_react₂ Δ_switch))
      e3 (switch_react₃ Δ_switch))
      e4 (switch_react₄ Δ_switch)
