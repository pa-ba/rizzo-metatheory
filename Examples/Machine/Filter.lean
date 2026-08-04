/-
The `filter` example machine execution
-/

import Examples.Machine.Common

open Term

variable (Δ : ChanCtx)


---------------
-- init step --
---------------

open RizzoNotation in
valdef mapMaybeTail : MVal :=
  delay (map {MaybeT NatTy} (λ x . case isEven ⬝ x of in1 _ . in1 x | in2 _ . in2 unit))
    ⧁ sigTail NatTy κ₁

open RizzoNotation in
valdef mkSigWatch : MVal :=
  delay ((λ f a . a ::{NatTy} f (watch (loc 1))) (mkSig {NatTy})) ⧁ watch (loc 1)


def η_filter₀ : Heap :=
  ((∅ : Heap).concat 2 (mksig NatTy n0 false mkSigWatch)
      (by fresh_loc)).concat
    1 (mksig (MaybeT NatTy) (MVal.in2 MVal.unit) false mapMaybeTail)
      (by fresh_loc)

theorem filter_init :
    (Term.filterProg, Δ) init⟹ (MVal.loc 2, η_filter₀, Δ) := by
  apply InitStep.init
  eval_refl

------------
-- step 1 --
------------

open RizzoNotation in
valdef mapTailA : MVal :=
  delay ((λ g . g (λ x . case isEven ⬝ x of in1 _ . in1 x | in2 _ . in2 unit)) (map {MaybeT NatTy}))
    ⧁ tail (loc 3)

def η_filter₁ : Heap :=
  ((((∅ : Heap).concat 2 (mksig NatTy n0 false mkSigWatch) (by fresh_loc)).concat
      1 (mksig (MaybeT NatTy) (MVal.in2 MVal.unit) true mapTailA) (by fresh_loc)).concat
      4 (mksig (MaybeT NatTy) (MVal.in2 MVal.unit) false mapTailA) (by fresh_loc)).concat
      3 (mksig NatTy n1 false (sigTail NatTy κ₁)) (by fresh_loc)

theorem filter_react₁ :
    (MVal.loc 2, η_filter₀, Δ) [κ₁ ↦ n1]⟹ (MVal.loc 2, η_filter₁, Δ) := by
  apply ReactStep.react
  case D => side
  case D' => side
  simp only [η_filter₀]
  update_tac_refl

------------
-- step 2 --
------------

def η_filter₂ : Heap :=
  ((((((((∅ : Heap).concat 2 (mksig NatTy n2 true mkSigWatch) (by fresh_loc)).concat
      8 (mksig NatTy n2 false mkSigWatch) (by fresh_loc)).concat
      1 (mksig (MaybeT NatTy) (MVal.in1 n2) true mapTailA) (by fresh_loc)).concat
      7 (mksig (MaybeT NatTy) (MVal.in1 n2) false mapTailA) (by fresh_loc)).concat
      4 (mksig (MaybeT NatTy) (MVal.in1 n2) true mapTailA) (by fresh_loc)).concat
      6 (mksig (MaybeT NatTy) (MVal.in1 n2) false mapTailA) (by fresh_loc)).concat
      3 (mksig NatTy n2 true (sigTail NatTy κ₁)) (by fresh_loc)).concat
      5 (mksig NatTy n2 false (sigTail NatTy κ₁)) (by fresh_loc)

theorem filter_react₂ :
    (MVal.loc 2, η_filter₁, Δ) [κ₁ ↦ n2]⟹ (MVal.loc 2, η_filter₂, Δ) := by
  apply ReactStep.react
  case D => side
  case D' => side
  simp only [η_filter₁]
  update_tac_refl

-----------------------------
-- full reactive execution --
-----------------------------

def Δ_filter : ChanCtx := (∅ : ChanCtx).concat κ₁ NatTy (by fresh_loc)

example :
    (Term.filterProg, Δ_filter)
      [ [κ₁ ↦ n2, κ₁ ↦ n1] ]⟹+ (MVal.loc 2, η_filter₂, Δ_filter) := by
  have e1 : ⊢[Δ_filter] (κ₁ ↦ n1) ∷Event := ⟨NatTy, by rfl, by type_check⟩
  have e2 : ⊢[Δ_filter] (κ₁ ↦ n2) ∷Event := ⟨NatTy, by rfl, by type_check⟩
  exact Steps.react (Steps.react
      (Steps.init (filter_init (Δ := Δ_filter)))
      e1 (filter_react₁ Δ_filter))
      e2 (filter_react₂ Δ_filter)
