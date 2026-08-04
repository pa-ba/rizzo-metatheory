/-
A small GUI program, well-typed in Rizzo's core calculus.
-/

import Examples.WellTyped.SignalCombinators
import Examples.WellTyped.Simple
import Examples.WellTyped.Notation

open Term Typ RizzoNotation

variable {Γ : Ctx} {Δ : ChanCtx} {H : HeapTy} {A B : Typ}


----------------------------------------------------------------------
-- Layout = horizontal | vertical
----------------------------------------------------------------------

abbrev LayoutTy : Typ := 𝟭 ⨁ 𝟭

abbrev Term.horizontal : Term := in1 unit
abbrev Term.vertical : Term := in2 unit

lemma HasType.horizontal : Γ ⊢[Δ, H] horizontal ∷ LayoutTy := by
  type_check [Term.horizontal]

lemma HasType.vertical : Γ ⊢[Δ, H] vertical ∷ LayoutTy := by
  type_check [Term.vertical]

----------------------------------------------------------------------
-- Button = mkButton (Sig String) (Sig Colour) (Chan 1)
-- TF     = mkTF     (Sig String) (Sig Colour) (Chan String)
--   where  String = List Nat,  Colour = Nat,  Black = 0
----------------------------------------------------------------------

abbrev StringTy : Typ := ListTy NatTy
abbrev ColourTy : Typ := NatTy

abbrev ButtonTy : Typ := Typ.sig StringTy ⨂ Typ.sig ColourTy ⨂ Typ.chan 𝟭
abbrev TFTy : Typ := Typ.sig StringTy ⨂ Typ.sig ColourTy ⨂ Typ.chan StringTy

-- simpleButton txt = mkButton (const txt) (const Black) chan
termdef Term.simpleButton : Term :=
  λ txt . (const {StringTy} txt,
           const {ColourTy} zero,
           newchan {𝟭})

lemma HasType.simpleButton : Γ ⊢[Δ, H] simpleButton ∷ StringTy ⟶ ButtonTy := by
  type_check [Term.simpleButton, HasType.const]

-- onClick (mkButton _ _ k) = mkSig (wait k)     (k = pr2 (pr2 btn))
termdef Term.onClick : Term :=
  λ (_, _, k) . mkSig {𝟭} (wait k)

lemma HasType.onClick : Γ ⊢[Δ, H] onClick ∷ ButtonTy ⟶ ◯ (Typ.sig 𝟭) := by
  type_check [Term.onClick, HasType.mkSig]

-- simpleTF txt = let k = chan in mkTF (txt :: mkSig (wait k)) (const Black) k
termdef Term.simpleTF : Term :=
  λ txt . let k = newchan {StringTy} in
    (txt ::{StringTy} (mkSig {StringTy} (wait k)),
     const {ColourTy} zero, k)

lemma HasType.simpleTF : Γ ⊢[Δ, H] simpleTF ∷ StringTy ⟶ TFTy := by
  type_check [Term.simpleTF, HasType.mkSig, HasType.const]

----------------------------------------------------------------------
-- colourButton : Button
--   colourButton = let c = chan in
--     mkButton (const "click me") (Black :: (const Red @ wait c)) c
----------------------------------------------------------------------

termdef Term.colourButton : Term :=
  let c = newchan {𝟭} in
    (const {StringTy} (consL {NatTy} zero (nilL NatTy)),
     zero ::{ColourTy}
       (atOp ⬝ (const {ColourTy} (succ zero)) ⬝ (wait c)),
     c)

lemma HasType.colourButton : Γ ⊢[Δ, H] colourButton ∷ ButtonTy := by
  type_check [Term.colourButton] using
    [HasType.atOp, HasType.const, HasType.consL, HasType.nilL]

----------------------------------------------------------------------
-- Widget = stack Layout (Sig (List Widget)) | button Button | textfield TF
----------------------------------------------------------------------

abbrev WidgetF : Typ :=
  (LayoutTy ⨂ Typ.sig (ListTy α₁)) ⨁ (ButtonTy ⨁ TFTy)

abbrev WidgetTy : Typ := μ WidgetF

termabbrev Term.stack : Term := λ layout children . cons {WidgetF} (in1 (layout, children))
termabbrev Term.button : Term := λ b . cons {WidgetF} (in2 (in1 b))
termabbrev Term.textfield : Term := λ tf . cons {WidgetF} (in2 (in2 tf))

lemma HasType.stack :
    Γ ⊢[Δ, H] stack ∷ LayoutTy ⟶ (ListTy WidgetTy).sig ⟶ WidgetTy := by
  type_check [Term.stack]

lemma HasType.button : Γ ⊢[Δ, H] button ∷ ButtonTy ⟶ WidgetTy := by
  type_check [Term.button]

lemma HasType.textfield : Γ ⊢[Δ, H] textfield ∷ TFTy ⟶ WidgetTy := by
  type_check [Term.textfield]

----------------------------------------------------------------------
-- newField : 1 → Widget
-- newField _ = textfield (simpleTF "")
----------------------------------------------------------------------

termdef Term.newField : Term := λ _ . textfield ⬝ (simpleTF ⬝ nilL NatTy)

lemma HasType.newField : Γ ⊢[Δ, H] newField ∷ 𝟭 ⟶ WidgetTy := by
  type_check [Term.newField, HasType.textfield, HasType.simpleTF, HasType.nilL]

----------------------------------------------------------------------
-- btn : Button
-- btn = simpleButton "Add"
----------------------------------------------------------------------

termdef Term.btn : Term := simpleButton ⬝ (consL {NatTy} zero (nilL NatTy))

lemma HasType.btn : Γ ⊢[Δ, H] btn ∷ ButtonTy := by
  type_check [Term.btn, HasType.simpleButton, HasType.consL, HasType.nilL]

----------------------------------------------------------------------
-- newWidgets : ◯ (Sig Widget)
-- newWidgets = map newField |> onClick btn
----------------------------------------------------------------------

termdef Term.newWidgets : Term :=
  map {WidgetTy} newField ▷ (onClick ⬝ btn)

lemma HasType.newWidgets : Γ ⊢[Δ, H] newWidgets ∷ ◯ (WidgetTy.sig) := by
  type_check [Term.newWidgets, HasType.fmapE, HasType.map, HasType.newField, HasType.onClick, HasType.btn]

----------------------------------------------------------------------
-- allWidgets : Sig (List Widget)
-- allWidgets = scanAwait snoc [button btn] newWidgets
----------------------------------------------------------------------

termdef Term.allWidgets : Term :=
  scanAwait {ListTy WidgetTy} (snoc WidgetTy)
    (consL {WidgetTy} (button ⬝ btn) (nilL WidgetTy)) newWidgets

lemma HasType.allWidgets : Γ ⊢[Δ, H] allWidgets ∷ (ListTy WidgetTy).sig := by
  type_check [Term.allWidgets] using
    [HasType.scanAwait, HasType.snoc, HasType.consL, HasType.button, HasType.btn,
     HasType.nilL, HasType.newWidgets]

----------------------------------------------------------------------
-- gui : Widget
-- gui = stack vertical allWidgets
----------------------------------------------------------------------

termdef Term.gui : Term :=
  stack ⬝ vertical ⬝ allWidgets

lemma HasType.gui : Γ ⊢[Δ, H] gui ∷ WidgetTy := by
  type_check [Term.gui] using
    [HasType.stack, HasType.vertical, HasType.allWidgets]

----------------------------------------------------------------------
-- Revised `newField`: a text field that can remove itself.
--   newField _ = let remove   = simpleButton "Remove" in
--                let tfAndBtn = [textfield (simpleTF ""), button remove]
--                in stack horizontal (tfAndBtn :: (const nil @ onClick remove))
----------------------------------------------------------------------

termdef Term.newField' : Term :=
  λ _ .
    let remove = simpleButton ⬝ (consL {NatTy} zero (nilL NatTy)) in
    let tfAndBtn =
      consL {WidgetTy} (textfield ⬝ (simpleTF ⬝ nilL NatTy))
        (consL {WidgetTy} (button ⬝ remove) (nilL WidgetTy)) in
    stack ⬝ horizontal ⬝
      (tfAndBtn ::{ListTy WidgetTy}
        (atOp ⬝ (const {ListTy WidgetTy} (nilL WidgetTy)) ⬝ (onClick ⬝ remove)))

lemma HasType.newField' : Γ ⊢[Δ, H] newField' ∷ 𝟭 ⟶ WidgetTy := by
  type_check [Term.newField'] using
    [HasType.stack, HasType.horizontal, HasType.button, HasType.textfield,
     HasType.simpleButton, HasType.simpleTF, HasType.onClick, HasType.atOp,
     HasType.const, HasType.consL, HasType.nilL]
