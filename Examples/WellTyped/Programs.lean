/-
The machine-example programs, used in `Examples.Machine`.
-/

import Examples.WellTyped.SignalCombinators
import Examples.WellTyped.Simple
import Examples.WellTyped.Notation

open Term Typ RizzoNotation

variable {Γ : Ctx} {Δ : ChanCtx} {H : HeapTy}

/-- The two input channels read by the example programs. -/
abbrev κ₁ : Chan := 0
abbrev κ₂ : Chan := 1

termdef Term.sampleProg : Term :=
  let xs = zero ::{NatTy} mkSig {NatTy} (wait (chan κ₁)) in
  let ys = zero ::{NatTy} mkSig {NatTy} (wait (chan κ₂)) in
  sample {NatTy} {NatTy} xs ys

lemma HasType.sampleProg (hκ₁ : NatTy ∈ Δ.lookup κ₁) (hκ₂ : NatTy ∈ Δ.lookup κ₂) :
    Γ ⊢[Δ, H] sampleProg ∷ (NatTy ⨂ NatTy).sig := by
  type_check [Term.sampleProg]

termdef Term.filterProg : Term :=
  let xs = mkSig {NatTy} (wait (chan κ₁)) in
  zero ::{NatTy} filter {NatTy} isEven xs

lemma HasType.filterProg (hκ : NatTy ∈ Δ.lookup κ₁) :
    Γ ⊢[Δ, H] filterProg ∷ NatTy.sig := by
  type_check [Term.filterProg] using [HasType.mkSig, HasType.filter, HasType.isEven]

termdef Term.switchProg : Term :=
  let xs = zero ::{NatTy} mkSig {NatTy} (wait (chan κ₁)) in
  let ys = mkSig {NatTy} (wait (chan κ₂)) in
  switch {NatTy} xs ys

lemma HasType.switchProg (hκ₁ : NatTy ∈ Δ.lookup κ₁) (hκ₂ : NatTy ∈ Δ.lookup κ₂) :
    Γ ⊢[Δ, H] switchProg ∷ NatTy.sig := by
  type_check [Term.switchProg] using [HasType.mkSig, HasType.switch]
