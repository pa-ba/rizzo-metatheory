/-
Well-typed signal combinators
-/

import Examples.WellTyped.Notation

open Term Typ RizzoNotation

variable {Γ : Ctx} {Δ : ChanCtx} {H : HeapTy} {A B : Typ}



----------------------------------------------------------------------
-- (▹) : (A → B) → ◯ A → ◯ B
----------------------------------------------------------------------
termdef Term.fmapE : Term := λ f a . delay f ⧁ a

lemma HasType.fmapE :
    A.Closed → B.Closed →
    Γ ⊢[Δ, H] fmapE ∷ (A ⟶ B) ⟶ ◯ A ⟶ ◯ B := by
  intro hA hB
  type_check [Term.fmapE]


----------------------------------------------------------------------
-- (@) : B → ◯ A → ◯ B
----------------------------------------------------------------------

termdef Term.atOp : Term := λ v d . (λ _ . v) ▷ d

lemma HasType.atOp :
    A.Closed → B.Closed →
    Γ ⊢[Δ, H] atOp ∷ B ⟶ ◯ A ⟶ ◯ B := by
  intro hA hB
  type_check [Term.atOp] using [HasType.fmapE]


----------------------------------------------------------------------
-- map : (A → B) → Sig A → Sig B
----------------------------------------------------------------------

termdef Term.map (B : Typ) : Term :=
  fix r . λ f (x :: xs) .
    f x ::{B} (delay (λ r' . r' f) ⊛ r ⧁ xs)

lemma HasType.map :
    A.Closed → B.Closed →
    Γ ⊢[Δ, H] map B ∷ (A ⟶ B) ⟶ A.sig ⟶ B.sig := by
  intro hA hB
  type_check [Term.map]

----------------------------------------------------------------------
-- scan : (B → A → B) → B → Sig A → Sig B
----------------------------------------------------------------------

termdef Term.scan (B : Typ) : Term :=
  fix r . λ f b (a :: as) .
    let b' = f b a in
    b' ::{B} (delay (λ r' . r' f b') ⊛ r ⧁ as)

lemma HasType.scan :
    A.Closed → B.Closed →
    Γ ⊢[Δ, H] scan B ∷ (B ⟶ A ⟶ B) ⟶ B ⟶ A.sig ⟶ B.sig := by
  intro hA hB
  type_check [Term.scan]

----------------------------------------------------------------------
-- scanAwait : (B → A → B) → B → ◯ (Sig A) → Sig B
----------------------------------------------------------------------

termdef Term.scanAwait (B : Typ) : Term :=
  λ f b s . b ::{B} (scan {B} f b ▷ s)

lemma HasType.scanAwait :
    A.Closed → B.Closed →
    Γ ⊢[Δ, H] scanAwait B ∷ (B ⟶ A ⟶ B) ⟶ B ⟶ ◯ (A.sig) ⟶ B.sig := by
  intro hA hB
  type_check [Term.scanAwait, HasType.fmapE, HasType.scan]

----------------------------------------------------------------------
-- zip : Sig A → Sig B → Sig (A × B)
----------------------------------------------------------------------

termdef Term.zip (A B : Typ) : Term :=
  fix r . λ as bs .
    let cont =
      (λ r' x .
        case x of
          left  as'     . r' as' bs
        | right bs'     . r' as bs'
        | both  as' bs' . r' as' bs') in
    (head as, head bs) ::{A ⨂ B} (delay cont ⊛ r ⧁ select (tail as) (tail bs))

lemma HasType.zip :
    A.Closed → B.Closed →
    Γ ⊢[Δ, H] zip A B ∷ A.sig ⟶ B.sig ⟶ (A ⨂ B).sig := by
  intro hA hB
  type_check [Term.zip]

----------------------------------------------------------------------
-- sample : Sig A → Sig B → Sig (A × B)
----------------------------------------------------------------------

-- sample = λxs. λys. map (λx. (x, head ys)) xs
termdef Term.sample (A B : Typ) : Term :=
  λ xs ys . map {A ⨂ B} (λ x . (x, head ys)) xs

lemma HasType.sample :
    A.Closed → B.Closed →
    Γ ⊢[Δ, H] sample A B ∷ A.sig ⟶ B.sig ⟶ (A ⨂ B).sig := by
  intro hA hB
  type_check [Term.sample, HasType.map]

----------------------------------------------------------------------
-- sample_beta : Sig A → Sig B → Sig (A × B)
-- (from section 2.4)
----------------------------------------------------------------------

-- sample_beta = λxs. λys. map ((λy x. (x, y)) (head ys)) xs
termdef Term.sample_beta (A B : Typ) : Term :=
  λ xs ys . map {A ⨂ B} ((λ y x . (x, y)) (head ys)) xs

lemma HasType.sample_beta :
    A.Closed → B.Closed →
    Γ ⊢[Δ, H] sample_beta A B ∷ A.sig ⟶ B.sig ⟶ (A ⨂ B).sig := by
  intro hA hB
  type_check [Term.sample_beta, HasType.map]

----------------------------------------------------------------------
-- interleave : (A → A → A) → ◯(Sig A) → ◯(Sig A) → ◯(Sig A)
----------------------------------------------------------------------

termdef Term.interleave (A : Typ) : Term :=
  fix r . λ f xs ys .
    let cont = (λ r' x .
        case x of
          left  (xhd :: xs') . xhd ::{A} (r' f xs' ys)
        | right (yhd :: ys') . yhd ::{A} (r' f xs ys')
        | both (xhd :: xs') (yhd :: ys') .
            (f xhd yhd) ::{A} (r' f xs' ys'))
    in delay cont ⊛ r ⧁ select xs ys

lemma HasType.interleave :
    A.Closed →
    Γ ⊢[Δ, H] interleave A ∷
      (A ⟶ A ⟶ A) ⟶ ◯ (A.sig) ⟶ ◯ (A.sig) ⟶ ◯ (A.sig) := by
  intro hA
  type_check [Term.interleave]

----------------------------------------------------------------------
-- switchS : Sig A → ◯(A → Sig A) → Sig A
----------------------------------------------------------------------

termdef Term.switchS (A : Typ) : Term :=
  fix r . λ (x :: xs) d .
    let cont = λ r' y .
      case y of
        left z   . r' z d
      | right f' . f' x
      | both _ f' . f' x
    in x ::{A} (delay cont ⊛ r ⧁ select xs d)

lemma HasType.switchS :
    A.Closed →
    Γ ⊢[Δ, H] switchS A ∷ A.sig ⟶ ◯ (A ⟶ A.sig) ⟶ A.sig := by
  intro hA
  type_check [Term.switchS]

----------------------------------------------------------------------
-- switchR : Sig A → ◯(Sig (A → Sig A)) → Sig A
----------------------------------------------------------------------

termdef Term.switchR (A : Typ) : Term :=
  fix r . λ (x :: xs) d .
    let cont = λ r' y .
      case y of
        left z          . r' z d
      | right (f :: d') . r' (f x) d'
      | both _ (f :: d') . r' (f x) d'
    in x ::{A} delay cont ⊛ r ⧁ select xs d

lemma HasType.switchR :
    A.Closed →
    Γ ⊢[Δ, H] switchR A ∷ A.sig ⟶ ◯ (A ⟶ A.sig).sig ⟶ A.sig := by
  intro hA
  type_check [Term.switchR]

----------------------------------------------------------------------
-- switch : Sig A → ◯(Sig A) → Sig A
----------------------------------------------------------------------

termdef Term.switch (A : Typ) : Term :=
  fix r . λ (x :: xs) d .
    let cont = λ r' y .
      case y of
        left z   . r' z d
      | right d' . d'
      | both _ d' . d'
    in x ::{A} delay cont ⊛ r ⧁ select xs d

lemma HasType.switch :
    A.Closed →
    Γ ⊢[Δ, H] switch A ∷ A.sig ⟶ ◯ (A.sig) ⟶ A.sig := by
  intro hA
  type_check [Term.switch]

----------------------------------------------------------------------
-- switchAt : Sig C → Sig C → ◯ 1 → Sig C
----------------------------------------------------------------------

termdef Term.switchAt (C : Typ) : Term :=
  λ xs ys d . switch {C} xs (atOp ⬝ ys ⬝ d)

lemma HasType.switchAt {C : Typ} :
    C.Closed →
    Γ ⊢[Δ, H] switchAt C ∷ C.sig ⟶ C.sig ⟶ ◯ 𝟭 ⟶ C.sig := by
  intro hC
  type_check [Term.switchAt] using [HasType.switch, HasType.atOp]

----------------------------------------------------------------------
-- const : A → Sig A
----------------------------------------------------------------------

termdef Term.const (A : Typ) : Term := λ x . x ::{A} never

lemma HasType.const :
    A.Closed →
    Γ ⊢[Δ, H] const A ∷ A ⟶ A.sig := by
  intro hA
  type_check [Term.const]

----------------------------------------------------------------------
-- mkSig : ◯ A → ◯ (Sig A)
----------------------------------------------------------------------

termdef Term.mkSig (A : Typ) : Term :=
  fix r . λ da . delay (λ r' a . a ::{A} r' da) ⊛ r ⧁ da

lemma HasType.mkSig :
    A.Closed →
    Γ ⊢[Δ, H] mkSig A ∷ ◯ A ⟶ ◯ A.sig := by
  intro hA
  type_check [Term.mkSig]

----------------------------------------------------------------------
-- mapMaybe : (A → Bool) → ◯ (Sig A) → ◯ (Sig (Maybe A))
----------------------------------------------------------------------

termdef Term.mapMaybe (A : Typ) : Term :=
  λ f d . delay (map {MaybeT A} (λ x . if f x then just x else nothing)) ⧁ d

lemma HasType.mapMaybe :
    A.Closed →
    Γ ⊢[Δ, H] mapMaybe A ∷ (A ⟶ BoolT) ⟶ ◯ A.sig ⟶ ◯ (MaybeT A).sig := by
  intro hA
  type_check [Term.mapMaybe, HasType.map]

----------------------------------------------------------------------
-- filter : (A → Bool) → ◯(Sig A) → ◯(Sig A)
----------------------------------------------------------------------

termdef Term.filter (A : Typ) : Term :=
  λ p s . mkSig {A} (watch (nothing ::{MaybeT A} (mapMaybe {A} p s)))

lemma HasType.filter :
    A.Closed →
    Γ ⊢[Δ, H] filter A ∷ (A ⟶ BoolT) ⟶ ◯ A.sig ⟶ ◯ A.sig := by
  intro hA
  type_check [Term.filter, HasType.mkSig, HasType.mapMaybe, HasType.map]
