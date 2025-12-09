import Rizzo.Semantics
import Rizzo.Preservation
import Rizzo.Progress

-----------------------------------
-- Theorem 4.1 (i): Productivity --
-----------------------------------

theorem InitStep.productivity : ∅ # δ ⊢ t ∷ A → ∃ v η δ' , (t, δ) init⟹ (v, η, δ') :=
  InitStep.progress

-- Finite step sequence, i.e. a finite sequence of steps with well-typed input.

inductive Steps : Term × ChanCtx → Val × Heap × ChanCtx → Type where
  | init : (t,δ) init⟹ (v,η,δ') → Steps (t,δ) (v,η,δ')
  | react :
    Steps (t,δ0) (v,η,δ) → δ ⊢ᵢ i → (v,η,δ) [i]⟹ (v',η',δ') → Steps (t,δ0) (v',η',δ')



notation : 80 x : 90 " ⟹+ " y : 90 => Steps x y

lemma Steps.preserve : ∅ # δ0 ⊢ t ∷ A → (steps: (t, δ0) ⟹+ (v, η, δ)) → δ ⊢ₕ η := by
  generalize X: (t,δ0) = x
  generalize Y: (v,η,δ) = y
  intros T R
  revert v η δ
  induction R<;> intros v η δ Y
  case init t δ0 v η δ R =>
    injections;subst_eqs
    apply InitStep.preserve_heap T R
  case react t δ0 v η δ i v' η' δ' Rs I R IH =>
    injections;subst_eqs
    apply R.preserve_heap <;> try assumption
    apply IH<;>rfl

------------------------------------
-- Theorem 4.1 (ii): Productivity --
------------------------------------

theorem Steps.productivity :
    ∅ # δ0 ⊢ t ∷ A → (steps : (t, δ0) ⟹+ (v, η, δ)) →
    δ ⊢ᵢ i → ∃ η' δ' , (v, η, δ) [i]⟹ (v, η', δ') := by
  intros T Rs I
  apply Rs.preserve at T
  apply ReactStep.progress I T

-----------------------------------------------
-- Step semantics produces well-typed output --
-----------------------------------------------

theorem Steps.welltyped : ∅ # δ0 ⊢ t ∷ A → (step : (t, δ0) ⟹+ (v, η, δ)) → η.type # δ ⊢ v ∷ A := by
  generalize X: (t,δ0) = x
  generalize Y: (v,η,δ) = y
  intros T R
  revert v η δ
  induction R<;> intros v η δ Y
  case init t δ0 v η δ R =>
    injections;subst_eqs
    apply R.preserve_term T
  case react Rs I R IH =>
    injections;subst_eqs
    have T' := IH (by rfl) (by rfl)
    apply R.preserve_term I T'
    apply Rs.preserve T


-- Infinite step sequence, i.e. an infinite sequence of steps with well-typed input.

structure Stepsω  (start : Term × ChanCtx) where
  state : Nat → Val × Heap × ChanCtx
  input : Nat → Inp
  wfinput : ∀ i, (state i).2.2 ⊢ᵢ input i
  init : start init⟹ state 0
  react : ∀ i, (state i) [input i]⟹ state (i+1)

notation : 80 x : 90 " ⟹ω"  => Stepsω x

def Stepsω.heap (S : (t, δ0) ⟹ω) (i : Nat) : Heap :=
  (S.state i).2.1
def Stepsω.chans (S : (t, δ0) ⟹ω) (i : Nat) : ChanCtx :=
  (S.state i).2.2
def Stepsω.val (S : (t, δ0) ⟹ω) (i : Nat) : Val :=
  (S.state i).1

def Stepsω.prefix (S : (t, δ) ⟹ω) (n : Nat) : (t,δ) ⟹+ (S.state n) :=
  match n with
  | 0 => Steps.init S.init
  | .succ m => Steps.react (S.prefix m) (S.wfinput m) (S.react m)


---------------------------------------------------------------------
-- Theorem 4.2 (part 1): Step semantics produces well-typed values --
---------------------------------------------------------------------

theorem Stepsω.welltyped_term : ∅ # δ ⊢ t ∷ A → (S : (t, δ) ⟹ω) →
    (S.heap n).type # S.chans n ⊢ S.val n ∷ A := by
  intro T S
  apply (S.prefix n).welltyped T

--------------------------------------------------------------------
-- Theorem 4.2 (part 2): Step semantics produces well-typed heaps --
--------------------------------------------------------------------

theorem Stepsω.welltyped_heap : ∅ # δ ⊢ t ∷ A → (S : (t, δ) ⟹ω) →
    S.chans n ⊢ₕ S.heap n := by
  intro T S
  apply (S.prefix n).preserve T


-----------------------------------------------
-- Theorem 4.4: The step semantics is causal --
-----------------------------------------------

theorem Stepsω.causal (S1 S2 : (t, δ0) ⟹ω) :
 (∀ i < n, S1.input i = S2.input i) → S1.state n = S2.state n := by
  suffices  H : (∀ i < n, S1.input i = S2.input i) → (i : Nat) → i ≤ n → S1.state i = S2.state i by
    intros E; apply H E; rfl
  intros E i
  induction i<;> intros L
  case zero =>
    apply S1.init.determ S2.init
  case succ i IH =>
    have R1 := S1.react i
    have R2 := S2.react i
    rw[IH (by omega)] at R1
    rw[E i (by omega)] at R1
    apply R1.determ R2
