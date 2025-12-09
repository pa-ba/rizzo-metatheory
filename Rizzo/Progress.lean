import Rizzo.FundamentalProperty


open Term
open Typ


-----------------------------------
-- Proposition 5.4 (i): Progress --
-----------------------------------

theorem Eval.progress : ε ⊩ t ∷ A → ∃ v ε', (t,ε) ⇓ (v, ε') := by
  -- follows immediately from the fundamental property
  intros T
  apply fund_prop_closed at T
  unfold TRel at T;grind

lemma sync_cases {b1 b2 : Bool} : b1 ∨ b2 → (b1 ∧ ¬ b2) ∨ (b2 ∧ ¬ b1) ∨ (b1 ∧ b2) := by
  intros B
  cases B <;> grind


------------------------------------
-- Proposition 5.4 (ii): Progress --
------------------------------------

theorem Adv.progress {v : Val} : v.ticked ε.now i.chan →  ε.chans ⊢ᵢ i → ε ⊩ v ∷ delayE A → ∃ v' ε', (v, ε) [i]⇘  (v', ε') := by
  intros C I T
  rcases v with ⟨t,p⟩
  simp at *
  revert A ε
  induction p <;> intros ε A I C T <;> try {solve | cases T.term}
  case wait V IH =>
    let ⟨κ, w⟩ := i
    cases T.term with | wait T
    apply HasType.chan_value T at V
    let ⟨κ, E⟩ := V
    subst E
    simp[Val.ticked,Term.ticked] at C
    subst C
    exists w, w.2, ε
    constructor
  case never => simp[Val.ticked,Term.ticked] at C
  case tail s V IH =>
    exists s, V , ε
    apply Adv.tail' <;> rfl
  case appE t1 t2 V1 V2 IH1 IH2 =>
    cases T.term with | appE T1 T2
    apply HasType.delayA_value' T1 at V1
    let ⟨s, E⟩ := V1
    subst E
    have T2' := EvalType.mk T2 T.env
    have R2 := IH2 I C T2'
    rcases R2 with ⟨ v, V, ε', R2⟩
    have T2'' := Adv.preserve I T2' R2
    cases T1 with | delay T1
    have T1' := T1.Sub' R2.incr
    have T := T1'.app T2''.term
    have R1 := Eval.progress ⟨T,T2''.env⟩
    rcases R1 with ⟨ w , ε'', R1⟩
    exists w, w.2, ε''
    apply Adv.appE R2 R1
  case sync t1 t2 V1 V2 IH1 IH2 =>
    cases T.term with | sync T1 T2
    simp[Val.ticked,Term.ticked] at C
    apply sync_cases at C
    rcases C with C | C | C
    . have T1' := EvalType.mk T1 T.env
      have R1 := IH1 I C.1 T1'
      rcases R1 with ⟨ w1, W1, ε', R1⟩
      exists in1 (in1 w1), .in1 (.in1 W1), ε'
      apply Adv.sync1 (v2:=⟨t2,V2⟩) C.1 C.2 R1
    . have T2' := EvalType.mk T2 T.env
      have R2 := IH2 I C.1 T2'
      rcases R2 with ⟨ w2, W2, ε', R2⟩
      exists in1 (in2 w2), .in1 (.in2 W2), ε'
      apply Adv.sync2 (v1:=⟨t1,V1⟩) C.1 C.2 R2
    . have T1' := EvalType.mk T1 T.env
      have R1 := IH1 I C.1 T1'
      rcases R1 with ⟨ w1, W1, ε', R1⟩
      have T3 := Adv.preserve I T1' R1
      have T2' := EvalType.mk T2 T.env
      have S := (R1.incr)
      have T2'' := T2'.Sub S T3.env
      have C' := C.2
      rw [T2.ticked_Sub S.store.now] at C'
      have R2 := IH2 (I.Sub S.chans) C' T2''
      rcases R2 with ⟨ w2, W2, ε'', R2⟩
      exists in2 (pair w1 w2), .in2 (.pair W1 W2), ε''
      apply Adv.sync3 C.1 C.2 R1 R2
  case trig s Vs IH =>
    cases T.term with | trig T
    apply HasType.sig_value' T at Vs
    simp[Val.loc] at Vs
    rcases Vs with ⟨l,rfl⟩
    simp[Val.ticked,Term.ticked] at C
    cases T with | loc T
    rw[Heap.type_lookup] at T
    simp at T
    rcases T with ⟨s,E1,E2⟩
    rw[E1] at C
    simp at C
    rcases s with ⟨B,⟨hd,Vh⟩,b,tl⟩
    simp at C
    have Hd := Term.isSome_ex C.2
    rcases Hd with ⟨v,rfl⟩
    constructor;constructor
    constructor
    constructor <;> try assumption
    . simp; apply C.1
    . rfl
    . cases Vh;assumption


-------------------------------------
-- Proposition 5.4 (iii): Progress --
-------------------------------------

theorem Update.progress : ε.chans ⊢ᵢ i → ⊢ₑ ε → ε.earlier ≠ ∅ → ∃ ε', ε [ i ]⇒ ε' := by
  intros I T E
  rcases ε with ⟨⟨ηN,ηL,N⟩,δ⟩
  simp[Env.earlier] at E
  apply AList.nonempty_decompose at E
  rcases E with ⟨ ηE, l, s, p, rfl⟩
  if H : s.tail.ticked ηN i.chan
  then
    have Tl := T.tail_type
    have R := Adv.progress H I Tl
    rcases R with ⟨v', ⟨⟨ηN',ηL',N'⟩,δ'⟩, R⟩
    have S := R.incr.store.earlier
    simp at S
    subst S
    have Tl' := Adv.preserve I Tl R
    have V := HasType.sig_value Tl'.term
    rcases V with ⟨l', rfl⟩
    have Loc := HasType.loc_lookup Tl'.term
    rcases Loc with ⟨s',M⟩
    simp[Env.now] at M
    have p' : l ∉ ηN' := by
      apply AList.concat_cons_Disjoint_nin
      symm; assumption
    have N'' : (ηN'.cons l s' p').Disjoint ηE := by
      symm
      apply AList.concat_cons_Disjoint_keys
      symm; assumption
    apply Update.adv (p' := p') (D'' := N'') H R at M
    constructor; apply M
  else
    cases s with | mk A hd θ tl
    have p' : l ∉ ηN := by
      apply AList.concat_cons_Disjoint_nin
      symm; assumption
    have N' : (ηN.cons l ⟨A,hd,false,tl⟩ p').Disjoint ηE := by
      symm
      apply AList.concat_cons_Disjoint_keys
      symm; assumption
    exists ηN.cons l ⟨A,hd,false,tl⟩ p' ✓[N'] ηE ⧸ δ
    apply Update.skip
    simp at H
    simp
    assumption


theorem Updates.progress : ε.chans ⊢ᵢ i → ⊢ₑ ε → ∃ ε', ε [ i ]⇒* ε' /\ ε'.earlier = ∅ := by
  intros I T
  generalize N : ε.earlier.entries.length = n
  revert ε
  induction n <;> intros ε I T N
  case zero =>
    apply AList.length_empty at N
    solve_by_elim
  case succ n IH =>
    have NE : ε.earlier ≠ ∅ := by
      apply AList.length_nonempty; omega
    have R := Update.progress I T NE
    rcases R with ⟨ε', R⟩
    have N' : ε'.earlier.entries.length = n := by
      apply Update.decrease at R
      omega
    have S := R.incr_chans
    have T' := R.preserve I T
    have IH' := IH (I.Sub S) T' N'
    rcases IH' with ⟨ε'', Rs , Q⟩
    exists ε''; split_ands
    . apply Updates.cons<;>assumption
    . assumption



-----------------------------------
-- Proposition 5.4 (v): Progress --
-----------------------------------

theorem ReactStep.progress : δ ⊢ᵢ i → δ ⊢ₕ η → ∃ η' δ' , (v, η, δ) [ i ]⟹ (v, η', δ') := by
  intros I T
  have D : AList.Disjoint ∅ η := by simp[AList.Disjoint]
  have E : ⊢ₑ (⟨ ∅, η, D⟩ ⧸ δ ) := by
    constructor
    . constructor
    . simp[Env.earlier]; apply IsHeap.end_step' T
  have R := Updates.progress I E
  rcases R with ⟨⟨⟨η',ηL,D'⟩,δ'⟩, R, rfl⟩
  apply ReactStep.react at R
  solve_by_elim

------------------------------------
-- Proposition 5.4 (iv): Progress --
------------------------------------

theorem InitStep.progress : ∅ # δ ⊢ t ∷ A → ∃ v η δ' , (t, δ) init⟹ (v, η, δ') := by
  intros T
  have T' : ∅ ⧸ δ ⊩ t ∷ A := by simp[T]
  apply Eval.progress at T'
  rcases  T' with ⟨v,⟨⟨ηN,ηL,D⟩,δ'⟩,R⟩
  exists v, ηN, δ'
  constructor<;> try simp[AList.Disjoint]
  have R' := R
  apply Eval.incr at R'
  have E := R'.store.earlier
  simp at E
  subst E
  assumption
