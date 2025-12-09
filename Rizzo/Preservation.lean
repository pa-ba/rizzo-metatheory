import Rizzo.Typing
import Rizzo.Semantics
import Rizzo.Substitution



----------------------------------------------------
-- Auxiliary lemmas for proving subject reduction --
----------------------------------------------------

lemma HasType.Eval_aux :
  (s, ε) ⇓ (v, ε') → ε.now.type # ε.chans # Γ ⊢ t ∷ A → ε'.now.type # ε'.chans # Γ ⊢ t ∷ A := by
  intros R T
  apply Eval.incr at R
  grind


lemma EvalType.Eval_aux :
  ε # Γ ⊩ t ∷ A → (s, ε) ⇓ (v, ε') → ⊩ₑ ε' → ε' # Γ ⊩ t ∷ A := by
  intros T R E
  apply Eval.incr at R
  apply EvalType.Sub <;> assumption


lemma EvalType.Eval_aux' :
  ε' # Γ' ⊩ v.val ∷ B → (s, ε) ⇓ (v, ε') → ε # Γ ⊩ t ∷ A → ε' # Γ ⊩ t ∷ A := by
  intros E R T
  apply EvalType.Eval_aux T R E.env

lemma EvalType.Adv_aux :
  ε # Γ ⊩ t ∷ A → (s, ε) [i]⇘ (v, ε') → ⊩ₑ ε' → ε' # Γ ⊩ t ∷ A := by
  intros T R E
  apply Adv.incr at R
  apply EvalType.Sub <;> assumption

lemma EvalType.Adv_aux' :
  ε' # Γ ⊩ v.val ∷ B → (s, ε) [i]⇘ (v, ε') → ε # Γ ⊩ t ∷ A → ε' # Γ ⊩ t ∷ A := by
  intros E R T
  apply EvalType.Adv_aux T R E.env


open Val Typ



----------------------------------------------------
-- Subject reduction for the evaluation semantics --
----------------------------------------------------

open Term

--------------------------------------------
-- Proposition 5.1 (i): type preservation --
--------------------------------------------

theorem Eval.preserve :
  ε ⊩ t ∷ A → (t, ε) ⇓ (v, ε') → ε' ⊩ v ∷ A := by
  revert ε' v
  suffices H : ∀ {C C'}, C.2 ⊩ C.1 ∷ A → C ⇓ C' → C'.2 ⊩ C'.1 ∷ A by
    intros _ _ T R
    apply H at R <;>simp at * <;> assumption
  intros _ _ T R
  revert A
  induction R <;> intro A T <;> simp at *
  case recur C C' t' ε' B v ε1 A s w ε2 u ε3 R1 R2 R3 IH1 IH2 IH3 => cases T.term with | recur WF2 WF1 T2 T1 =>
    have WF3 := WF2
    cases WF2 with | mu WF2
    have U1 := EvalType.mk T1 T.env
    have U2 := EvalType.mk T2 T.env
    clear T T1 T2 C C'
    apply IH1 at U1
    apply EvalType.Eval_aux' U1 R1 at U2
    cases U1.term
    have T3 :  ε1.now.type # ε1.chans ⊢ ((Term.fmap B (μ B ⊗ A)).app ((var 0).pair (s.recur A (var 0))).lam).app v ∷ B.sub (μ B ⊗ A) := by
      apply HasType.app'; assumption
      apply HasType.app; apply HasType.fmap WF2
      constructor;constructor;constructor;rfl;constructor; assumption; assumption
      apply U2.term.weaken
      constructor;rfl
    have U3 := EvalType.mk T3 U2.env
    apply IH2 at U3
    apply EvalType.Eval_aux' U3 R2 at U2
    have T4 := EvalType.mk (U3.term.sub U2.term) U2.env
    apply IH3; assumption

  case value => assumption
  case pair R1 R2 IH1 IH2 => cases T.term with | pair T1 T2 =>
    have U1 := EvalType.mk T1 T.env
    have U2 := EvalType.mk T2 T.env
    clear T1 T2 T
    apply IH1 at U1
    apply EvalType.Eval_aux' U1 R1 at U2
    apply IH2 at U2
    apply EvalType.Eval_aux' U2 R2 at U1
    constructor
    constructor; apply U1.term; apply U2.term
    apply U1.env
  case appE R1 R2 IH1 IH2 => cases T.term with | appE T1 T2 =>
    have U1 := EvalType.mk T1 T.env
    have U2 := EvalType.mk T2 T.env
    clear T1 T2 T
    apply IH1 at U1
    apply EvalType.Eval_aux' U1 R1 at U2
    apply IH2 at U2
    apply EvalType.Eval_aux' U2 R2 at U1
    constructor
    constructor; apply U1.term; apply U2.term
    apply U1.env
  case sync R1 R2 IH1 IH2 => cases T.term with | sync T1 T2 =>
    have U1 := EvalType.mk T1 T.env
    have U2 := EvalType.mk T2 T.env
    clear T1 T2 T
    apply IH1 at U1
    apply EvalType.Eval_aux' U1 R1 at U2
    apply IH2 at U2
    apply EvalType.Eval_aux' U2 R2 at U1
    constructor
    constructor; apply U1.term; apply U2.term
    apply U1.env
  case appA R1 R2 IH1 IH2 =>
    cases T.term with | appA T1 T2
    have U1 := EvalType.mk T1 T.env
    have U2 := EvalType.mk T2 T.env
    clear T1 T2 T
    apply IH1 at U1
    apply EvalType.Eval_aux' U1 R1 at U2
    apply IH2 at U2
    apply EvalType.Eval_aux' U2 R2 at U1
    cases U1.term with | delay V1
    cases U2.term with | delay V2
    repeat constructor <;> try assumption
    apply U1.env
  case pr1 IH | pr2 IH =>
    cases T.term; rename HasType _ _ _ _ _ => T1
    have U1 := IH (EvalType.mk T1 T.env)
    cases U1.term
    constructor; assumption; apply U1.env
  case wait IH | trig IH | tail IH | in1 IH | in2 IH =>
    cases T.term; rename HasType _ _ _ _ _ => T1
    have U1 := IH (EvalType.mk T1 T.env)
    constructor; constructor; apply U1.term; apply U1.env
  case cons IH =>
    cases T.term; rename HasType _ _ _ _ _ => T1
    have U1 := IH (EvalType.mk T1 T.env)
    constructor; constructor; assumption; apply U1.term; apply U1.env
  case case1 R1 R2 IH1 IH2 =>
    cases T.term with | case T1 T2 T3
    have U1 := EvalType.mk T1 T.env
    apply IH1 at U1
    cases U1.term with | in1 V1
    apply HasType.Eval_aux R1 at T2
    apply V1.sub at T2
    have U2 := EvalType.mk T2 U1.env
    apply IH2 at U2; apply U2
  case case2 R1 R2 IH1 IH2 =>
    cases T.term with | case T1 T2 T3
    have U1 := EvalType.mk T1 T.env
    apply IH1 at U1
    cases U1.term with | in2 V1
    apply HasType.Eval_aux R1 at T3
    apply V1.sub at T3
    have U2 := EvalType.mk T3 U1.env
    apply IH2 at U2; apply U2
  case fix IH =>
    have T1 := T.term.delay
    cases T.term with | fix T2
    apply T1.sub at T2
    apply IH (EvalType.mk T2 T.env)
  case sig R1 R2 IH1 IH2 => cases T.term with | sig T1 T2 =>
    have U1 := EvalType.mk T1 T.env
    have U2 := EvalType.mk T2 T.env
    clear T1 T2 T
    apply IH1 at U1
    apply EvalType.Eval_aux' U1 R1 at U2
    apply IH2 at U2
    apply EvalType.Eval_aux' U2 R2 at U1
    apply HasType.insert U1 U2
  case newchan =>
    cases T.term
    constructor
    case term => constructor; simp [AList.lookup,AList.cons]
    case env =>
    apply IsHeap.Sub
    . apply AList.Sub.cons; simp
    . apply T.env
  case app R1 R2 R3 IH1 IH2 IH3 => cases T.term with | app T1 T2 =>
    have U1 := EvalType.mk T1 T.env
    have U2 := EvalType.mk T2 T.env
    clear T1 T2 T
    apply IH1 at U1
    apply EvalType.Eval_aux' U1 R1 at U2
    apply IH2 at U2
    apply EvalType.Eval_aux' U2 R2 at U1
    cases U1.term with | lam V1
    have V2 := U2.term
    apply V2.sub at V1
    have W1 := EvalType.mk V1 U2.env
    apply IH3 at W1; apply W1
  case head IH L =>
    cases T.term with | head T1
    have U1 := IH (EvalType.mk T1 T.env)
    cases U1.term with | loc S1
    constructor
    . rw[Heap.type_lookup] at S1
      simp at S1
      rcases S1 with ⟨s, S1, E⟩
      rw[S1] at L
      cases L
      subst E
      apply (U1.env.lookup_SigType S1).head
    . apply U1.env

-----------------------------------------------------
-- Auxiliary lemmas for the subject recution proof --
-----------------------------------------------------

lemma IsInp.Sub : δ.Sub δ' → δ ⊢ᵢ i → δ' ⊢ᵢ i := by
  intros Sd I
  simp [IsInp] at *
  rcases I with ⟨ A, L, T⟩
  use A;constructor
  apply AList.Sub.lookup Sd L
  apply HasType.Sub T
  . rfl
  . assumption



------------------------------------------------
-- Subject reduction of the advance semantics --
------------------------------------------------


---------------------------------------------
-- Proposition 5.1 (ii): type preservation --
---------------------------------------------

theorem Adv.preserve {v : Val} :
  ε.chans ⊢ᵢ i → ε ⊩ v ∷ ◯ A → (v, ε) [i]⇘  (v', ε') → ε' ⊩ v' ∷ A := by
  suffices H : ∀ (C C' : Val × Env),
    C.2.chans ⊢ᵢ i → C.2 ⊩ C.1 ∷ ◯ A → C [i]⇘  C' → C'.2 ⊩ C'.1 ∷ A
    by apply H (v, ε) (v', ε')
  intros C C' I T R; revert A
  induction R <;> intro A T <;> simp at * <;> clear C C'
  case tail =>
    cases T.term with | tail T1
    constructor; assumption; apply T.env
  case wait =>
    simp [IsInp] at I
    cases T.term with | wait T'
    cases T' with | chan T'
    cases I with | intro A L
    rw[L.1] at T'
    cases T'
    constructor; apply L.2.Sub; simp; rfl; apply T.env
  case trig E1 L =>
    cases T.term with | trig T'
    cases T' with | loc T'
    constructor;
    . rw[Heap.type_lookup] at T'
      simp at T'
      rcases T' with ⟨s, T', E2⟩
      rw[T'] at L
      cases L
      have T1 := (T.env.lookup_SigType T').head
      rw[E1,E2] at T1
      cases T1; assumption
    . apply T.env
  case appE R1 R2 IH =>
    cases T.term with | appE T1 T2
    cases T1 with | delay T1
    have U2 := EvalType.mk T2 T.env
    have U1 := EvalType.mk T1 T.env
    have V2 := IH I U2
    apply EvalType.Adv_aux' V2 R1 at U1
    have W := EvalType.mk (HasType.app U1.term V2.term) U1.env
    apply Eval.preserve W R2
  case sync1 IH _ =>
    cases T.term with | sync T1 T2
    have U1 := IH I (EvalType.mk T1 T.env)
    constructor; constructor; constructor; apply U1.term; apply U1.env
  case sync2 IH _ =>
    cases T.term with | sync T1 T2
    have U1 := IH I (EvalType.mk T2 T.env)
    constructor; constructor; constructor; apply U1.term; apply U1.env
  case sync3 R1 R2 IH1 IH2  =>
    cases T.term with | sync T1 T2
    have U1 := IH1 I (EvalType.mk T1 T.env)
    have U2 := EvalType.Adv_aux' U1 R1 (EvalType.mk T2 T.env)
    have I' := I.Sub R1.incr.chans
    apply IH2 I' at U2
    apply EvalType.Adv_aux' U2 R2 at U1
    constructor; constructor; constructor; apply U1.term; apply U2.term
    apply U1.env

-----------------------------------------------------
-- Auxiliary lemmas for the subject redution proof --
-----------------------------------------------------


-- A couple of 'move' lemmas for the proof of the type preservation of
-- the intermediate step semantics.

lemma IsHeap.move :
    δ ⊢ₕ ηN →
    SigType ηN δ s →
    δ ⊢ₕ AList.cons l s ηN p := by
  intros T ST
  cases s; cases ST; simp at *
  constructor<;>try assumption


lemma IsEarlierHeap.move :
    H # δ ⊩ₕ η.concat l s p →
    A = s.type →
    H.cons l A p' # δ ⊩ₕ η := by
  intros T E
  apply IsEarlierHeap.cons_inv at T
  rcases T with ⟨p', T, Hd, Tl⟩
  rw[E]
  apply T


lemma IsEnv.move :
    ⊢ₑ (ηN ✓[D'] AList.concat ηE l' s p ⧸ δ) →
    SigType ηN δ s' →
    s'.type = s.type →
    ⊢ₑ (AList.cons l' s' ηN p' ✓[D''] ηE ⧸ δ) := by
  intros T ST
  cases T with | intro T1 T2
  intros Teq
  split_ands <;>simp[Env.earlier,Env.now] at *
  . apply IsHeap.move <;> assumption
  . rw[Heap.type_cons]
    apply IsEarlierHeap.move T2 Teq
    rw[Heap.type_fresh]; assumption


----------------------------------------------
-- Proposition 5.1 (iii): type preservation --
----------------------------------------------

theorem Update.preserve : ε.chans ⊢ᵢ i → ⊢ₑ ε →  ε [ i ]⇒ ε' → ⊢ₑ ε' := by
  intros I T R
  cases R
  case skip D' p D Cl Ch =>
    simp [IsEnv,Env.now,Env.earlier] at *
    cases T with | intro T1 T2
    apply IsEarlierHeap.cons_inv at T2
    simp [AList.concat, AList.cons] at *
    rcases T2 with ⟨⟨p' , T2⟩, Hd, Tl⟩
    split_ands
    . apply IsHeap.move <;> try assumption
      constructor <;> grind
    . apply T2
  case adv ηN δ l ηN' δ' s' l' p' ηE D'' s p D D' L Ch R =>
    have T' := R.preserve I T.tail_type
    have T'' := T'.term; simp[Env.now] at T''
    apply HasType.loc_inv at T''
    rcases T'' with ⟨A, L', Q⟩
    have H' := IsEnv.step T (R.incr) T'.env
    apply H'.move <;> try assumption
    apply (IsHeap.lookup_SigType H'.1 L).tick
    rw[Heap.type_lookup,L] at L'
    simp at L'
    cases Q
    assumption

theorem Updates.preserve : ε.chans ⊢ᵢ i → ⊢ₑ ε →  ε [ i ]⇒* ε' → ⊢ₑ ε' := by
  intros I T Rs
  induction Rs
  case nil => assumption
  case cons ε1 ε2 R Rs IH =>
    apply IH (I.Sub R.incr_chans) (R.preserve I T)


theorem ReactStep.preserve_heap : δ ⊢ᵢ i → δ ⊢ₕ η → (step : (v, η, δ) [ i ]⟹ (v', η', δ')) →  δ' ⊢ₕ η' := by
  intros I T R
  cases R
  case react Rs =>
  apply Updates.preserve at Rs
  apply Rs.left
  assumption
  constructor
  . constructor
  . simp[Env.earlier,Env.now]
    apply IsHeap.end_step' at T
    apply T

lemma Update.incr_heap_type :  ε.chans ⊢ᵢ i → ⊢ₑ ε → ε [ i ]⇒ ε' → ε.store.type.Sub ε'.store.type := by
  intros I T R
  cases R
  case skip =>
    apply AList.refl'
    simp[Store.type,AList.append,AList.cons,AList.concat,Heap.type,List.entryMap,List.map_append]
  case adv ηN δ l' ηN' δ' s' l p ηE D'' s L D D' I' C R =>
    have s_s' : s.type = s'.type := by
      have T' := R.preserve I T.tail_type
      have T'' := T'.term; simp[Env.now] at T''
      apply HasType.loc_inv at T''
      rcases T'' with ⟨A, L', Q⟩
      rw[Heap.type_lookup,I'] at L'
      simp at L'; grind
    have S := Store.Sub_type R.incr.store
    have E : (ηN' ✓[D'] AList.concat ηE l s L ⧸ δ').σ.type
          = (AList.cons l s'.tick ηN' p ✓[D''] ηE ⧸ δ').σ.type := by
      simp[Store.type,AList.append,AList.cons,AList.concat,Heap.type,List.entryMap,List.map_append, Sig.tick]
      assumption
    rw[<- E]
    apply S

lemma Updates.incr_heap_type :
    ε.chans ⊢ᵢ i → ⊢ₑ ε → ε [ i ]⇒* ε' → ε.store.type.Sub ε'.store.type := by
  intros I T R
  induction R
  case nil =>
    rfl
  case cons R Rs IH =>
    trans
    apply R.incr_heap_type I T
    apply IH
    . apply I.Sub R.incr_chans
    . apply R.preserve I T


------------------------
-- Lemma 5.3 (part 1) --
------------------------

lemma ReactStep.incr_heap_type :
    δ ⊢ᵢ i → δ ⊢ₕ η → (v, η, δ) [ i ]⟹ (v', η', δ') → η.type.Sub η'.type := by
  intros I T R
  cases R with | react R
  apply Updates.incr_heap_type at R
  . have N : (Heap.type ∅).entries = [] := by
      simp[Heap.type,List.entryMap]
    simp[Store.type, AList.append,List.append_nil,N] at R
    assumption
  . assumption
  . constructor
    constructor
    simp[Env.earlier,Env.now,];
    apply T.end_step'

------------------------
-- Lemma 5.3 (part 2) --
------------------------

lemma ReactStep.incr_chans :
    (v, η, δ) [ i ]⟹ (v', η', δ') → δ.Sub δ' := by
  intros R
  cases R with | react R
  apply R.incr_chans


--------------------------------------------
-- Proposition 5.1 (v): type preservation --
--------------------------------------------

theorem ReactStep.preserve_term {v v' : Val} :
    δ ⊢ᵢ i → η.type # δ ⊢ v ∷ A → δ ⊢ₕ η →  (step : (v, η, δ) [ i ]⟹ (v', η', δ')) →
    η'.type # δ' ⊢ v' ∷ A := by
  intros I T1 T2 R
  have E := ReactStep.constValue R
  subst E
  apply T1.Sub
  . apply R.incr_heap_type I T2
  . apply R.incr_chans


----------------------------------------------------
-- Proposition 5.1 (iv) part 1: type preservation --
----------------------------------------------------

theorem InitStep.preserve_heap : ∅ # δ ⊢ t ∷ A → (t, δ) init⟹ (v, η,  δ') →  δ' ⊢ₕ η := by
  intros T R
  cases R with | init R
  apply Eval.preserve at R <;> try assumption
  cases R; simp[Env.now] at *
  assumption
  simp[*]

----------------------------------------------------
-- Proposition 5.1 (iv) part 2: type preservation --
----------------------------------------------------

theorem InitStep.preserve_term : ∅ # δ ⊢ t ∷ A → (t, δ) init⟹ (v, η,  δ') →  η.type # δ' ⊢ v ∷ A := by
  intros T R
  cases R with | init R
  apply Eval.preserve at R <;> try assumption
  cases R; simp[Env.now] at *
  assumption
  simp[*]
