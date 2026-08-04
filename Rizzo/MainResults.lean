/-
Top-level operational properties: productivity, causality, and type
preservation.
-/

import Rizzo.Semantics
import Rizzo.Preservation
import Rizzo.Progress


-----------------------------------
-- Theorem 4.1 (i): Productivity --
-----------------------------------

theorem InitStep.productivity : ⊢[Δ] t ∷ A → ∃ v η Δ' , (t, Δ) init⟹ (v, η, Δ') :=
  InitStep.progress


lemma Steps.preserve : ⊢[Δ0] t ∷ A → (steps: (t, Δ0) [τ]⟹+ (v, η, Δ)) → ⊢[Δ] η ∷now := by
  generalize X: (t,Δ0) = x
  generalize Y: (v,η,Δ) = y
  intros T R
  revert v η Δ
  induction R<;> intros v η Δ Y
  case init t Δ0 v η Δ R =>
    injections;subst_eqs
    apply InitStep.preserve_heap T R
  case react t Δ0 v η Δ i v' η' Δ' Rs I R IH =>
    injections;subst_eqs
    apply R.preserve_heap <;> try assumption
    apply IH<;>rfl

------------------------------------
-- Theorem 4.1 (ii): Productivity --
------------------------------------

theorem Steps.productivity :
    ⊢[Δ0] t ∷ A → (steps : (t, Δ0) [τ]⟹+ (v, η, Δ)) →
    ⊢[Δ] e ∷Event → ∃ η' Δ' , (v, η, Δ) [e]⟹ (v, η', Δ') := by
  intros T Rs I
  apply Rs.preserve at T
  apply ReactStep.progress I T

-----------------------------------------------
-- Step semantics produces well-typed output --
-----------------------------------------------

theorem Steps.welltyped : ⊢[Δ0] t ∷ A → (t, Δ0) [τ]⟹+ (v, η, Δ) → ⊢[Δ, η.type] v ∷ A := by
  generalize X: (t,Δ0) = x
  generalize Y: (v,η,Δ) = y
  intros T R
  revert v η Δ
  induction R<;> intros v η Δ Y
  case init t Δ0 v η Δ R =>
    injections;subst_eqs
    apply R.preserve_term T
  case react Rs I R IH =>
    injections;subst_eqs
    have T' := IH (by rfl) (by rfl)
    apply R.preserve_term I T'
    apply Rs.preserve T

lemma InitStep.incr_chans : (t, Δ) init⟹ (v, η, Δ') → Δ.le Δ' := by
  intro S
  cases S with | init R => exact (Eval.incr R).chans

lemma Steps.incr_chans : (t, Δ0) [τ]⟹+ (v, η, Δ) → Δ0.le Δ := by
  generalize X: (t, Δ0) = x
  generalize Y: (v, η, Δ) = y
  intro R
  revert v η Δ
  induction R <;> intros v η Δ Y
  case init R =>
    injections; subst_eqs
    exact R.incr_chans
  case react Rs I R IH =>
    injections; subst_eqs
    exact (IH (by rfl) (by rfl)).trans R.incr_chans

--------------------------------------------
-- Corollary 4.4: type preservation for ⤳ --
--------------------------------------------

theorem Reacts.preserve :
  ⊢[Δ] t ∷ A → (t, Δ) [τ]⤳ (v, Δ') → ⊢[Δ'] v ∷ A := by
  intros T R
  cases R with
  | reacts steps =>
    exact HasType.heapSub (Steps.welltyped T steps) (Steps.preserve T steps)

-- This lemma confirms that ⤳ indeed produces values

lemma Reacts.result_IsValue : ⊢[Δ] t ∷ A → (t, Δ) [ τ ]⤳ (t', Δ') → IsValue t' := by
  intros T R
  cases R with
  | @reacts t Δ τ v η Δ' steps =>
    exact IsValue.heapSub v.property.gvalue (Steps.welltyped T steps) (Steps.preserve T steps)

---------------------------------------
-- Corollary 4.3 (i): progress for ⤳ --
---------------------------------------

-- Note: The additional conclusion `IsValue v` makes explicit what is
-- implicit in the statement of Corollary 4.3 in the paper.
theorem Reacts.progress_nil : ⊢[Δ] t ∷ A → ∃ v Δ' , (t, Δ) [ [] ]⤳ (v, Δ') ∧ IsValue v := by
  intros T
  obtain ⟨v, η, Δ', R⟩ := InitStep.progress T
  have R := Reacts.reacts (Steps.init R)
  exact ⟨_, _, R , Reacts.result_IsValue T R⟩


----------------------------------------
-- Corollary 4.3 (ii): progress for ⤳ --
----------------------------------------

-- Note: The additional conclusion `IsValue v` makes explicit what is
-- implicit in the statement of Corollary 4.3 in the paper.
theorem Reacts.progress_cons
    : ⊢[Δ] t ∷ A → (t, Δ) [ τ ]⤳ (v, Δ') → ⊢[Δ'] e ∷Event
      → ∃ w Δ' , (t, Δ) [ (e :: τ) ]⤳ (w, Δ') ∧ IsValue w  := by
  intros T R I
  cases R with
  | reacts steps =>
    obtain ⟨η', Δ'', react⟩ := Steps.productivity T steps I
    have R := Reacts.reacts (Steps.react steps I react)
    exact ⟨_, _, R, Reacts.result_IsValue T R⟩


---------------------------------------------------------------------
-- Theorem 4.2 (part 1): Step semantics produces well-typed values --
---------------------------------------------------------------------

theorem Stepsω.welltyped_term : ⊢[Δ] t ∷ A → (S : (t, Δ) [τ]⟹ω) →
    ⊢[S.chans n, (S.heap n).type] S.val n ∷ A := by
  intro T S
  apply (S.prefix n).welltyped T

--------------------------------------------------------------------
-- Theorem 4.2 (part 2): Step semantics produces well-typed heaps --
--------------------------------------------------------------------

theorem Stepsω.welltyped_heap : ⊢[Δ] t ∷ A → (S : (t, Δ) [τ]⟹ω) →
    ⊢[S.chans n] S.heap n ∷now := by
  intro T S
  apply (S.prefix n).preserve T


-----------------------------------------------
-- Theorem 4.5: The step semantics is causal --
-----------------------------------------------

theorem Stepsω.causal (S1 : (t, Δ0) [τ1]⟹ω)  (S2 : (t, Δ0) [τ2]⟹ω) :
 (∀ i < n, τ1 i = τ2 i) → S1.state n = S2.state n := by
  suffices  H : (∀ i < n, τ1 i = τ2 i) → (i : Nat) → i ≤ n → S1.state i = S2.state i by
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
