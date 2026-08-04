/-
The `sample` example machine execution.
-/

import Examples.Machine.Common

open Term

variable (Δ : ChanCtx)

---------------
-- init step --
---------------

open RizzoNotation in
valdef sampleTail : MVal :=
  delay ((λ g . g (λ b . (b, head (loc 2)))) (map {NatTy ⨂ NatTy})) ⧁ tail (loc 1)

def η_sample₀ : Heap :=
  (((∅ : Heap).concat 3 (mksig (NatTy ⨂ NatTy) (MVal.pair n0 n0) false sampleTail)
        (by fresh_loc)).concat
      2 (mksig NatTy n0 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
    1 (mksig NatTy n0 false (sigTail NatTy κ₁)) (by fresh_loc)

theorem sample_init :
    (Term.sampleProg, Δ) init⟹ (MVal.loc 3, η_sample₀, Δ) := by
  apply InitStep.init
  eval_refl

------------
-- step 1 --
------------

def η_sample₁ : Heap :=
  (((((∅ : Heap).concat 3 (mksig (NatTy ⨂ NatTy) (MVal.pair n1 n0) true sampleTail)
        (by fresh_loc)).concat
      5 (mksig (NatTy ⨂ NatTy) (MVal.pair n1 n0) false sampleTail) (by fresh_loc)).concat
      2 (mksig NatTy n0 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
      1 (mksig NatTy n1 true (sigTail NatTy κ₁)) (by fresh_loc)).concat
      4 (mksig NatTy n1 false (sigTail NatTy κ₁)) (by fresh_loc)

theorem sample_react₁ :
    (MVal.loc 3, η_sample₀, Δ) [κ₁ ↦ n1]⟹ (MVal.loc 3, η_sample₁, Δ) := by
  apply ReactStep.react
  case D => side
  case D' => side
  simp only [η_sample₀]
  update_tac_refl

------------
-- step 2 --
------------

def η_sample₂ : Heap :=
  ((((((∅ : Heap).concat 3 (mksig (NatTy ⨂ NatTy) (MVal.pair n1 n0) false sampleTail)
        (by fresh_loc)).concat
      5 (mksig (NatTy ⨂ NatTy) (MVal.pair n1 n0) false sampleTail) (by fresh_loc)).concat
      2 (mksig NatTy n3 true (sigTail NatTy κ₂)) (by fresh_loc)).concat
      6 (mksig NatTy n3 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
      1 (mksig NatTy n1 false (sigTail NatTy κ₁)) (by fresh_loc)).concat
      4 (mksig NatTy n1 false (sigTail NatTy κ₁)) (by fresh_loc)

theorem sample_react₂ :
    (MVal.loc 3, η_sample₁, Δ) [κ₂ ↦ n3]⟹ (MVal.loc 3, η_sample₂, Δ) := by
  apply ReactStep.react
  case D => side
  case D' => side
  simp only [η_sample₁]
  update_tac_refl


------------
-- step 3 --
------------

def η_sample₃ : Heap :=
  ((((((((((∅ : Heap).concat 3 (mksig (NatTy ⨂ NatTy) (MVal.pair n2 n3) true sampleTail)
        (by fresh_loc)).concat
      10 (mksig (NatTy ⨂ NatTy) (MVal.pair n2 n3) false sampleTail) (by fresh_loc)).concat
      5 (mksig (NatTy ⨂ NatTy) (MVal.pair n2 n3) true sampleTail) (by fresh_loc)).concat
      9 (mksig (NatTy ⨂ NatTy) (MVal.pair n2 n3) false sampleTail) (by fresh_loc)).concat
      2 (mksig NatTy n3 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
      6 (mksig NatTy n3 false (sigTail NatTy κ₂)) (by fresh_loc)).concat
      1 (mksig NatTy n2 true (sigTail NatTy κ₁)) (by fresh_loc)).concat
      8 (mksig NatTy n2 false (sigTail NatTy κ₁)) (by fresh_loc)).concat
      4 (mksig NatTy n2 true (sigTail NatTy κ₁)) (by fresh_loc)).concat
      7 (mksig NatTy n2 false (sigTail NatTy κ₁)) (by fresh_loc)

theorem sample_react₃ :
    (MVal.loc 3, η_sample₂, Δ) [κ₁ ↦ n2]⟹ (MVal.loc 3, η_sample₃, Δ) := by
  apply ReactStep.react
  case D => side
  case D' => side
  simp only [η_sample₂]
  update_tac_refl

-----------------------------
-- full reactive execution --
-----------------------------

def Δ_sample : ChanCtx :=
  ((∅ : ChanCtx).concat κ₁ NatTy (by fresh_loc)).concat κ₂ NatTy (by fresh_loc)


theorem isEvent_sample {v : MVal} {κ} :
    NatTy ∈ Δ_sample.lookup κ → ⊢[Δ_sample] v.val ∷ NatTy → ⊢[Δ_sample] (κ ↦ v) ∷Event :=
  fun hκ hv => ⟨NatTy, hκ, hv⟩

example :
    (Term.sampleProg, Δ_sample)
      [ [κ₁ ↦ n2, κ₂ ↦ n3, κ₁ ↦ n1] ]⟹+ (MVal.loc 3, η_sample₃, Δ_sample) := by
  have e1 : ⊢[Δ_sample] (κ₁ ↦ n1) ∷Event := isEvent_sample (by rfl) (by type_check)
  have e2 : ⊢[Δ_sample] (κ₂ ↦ n3) ∷Event := isEvent_sample (by rfl) (by type_check)
  have e3 : ⊢[Δ_sample] (κ₁ ↦ n2) ∷Event := isEvent_sample (by rfl) (by type_check)
  exact Steps.react (Steps.react (Steps.react
      (Steps.init (sample_init Δ_sample))
      e1 (sample_react₁ Δ_sample))
      e2 (sample_react₂ Δ_sample))
      e3 (sample_react₃ Δ_sample)
