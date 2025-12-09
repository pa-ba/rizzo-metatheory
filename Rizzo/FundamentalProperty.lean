import Rizzo.LogicalRelation
import Rizzo.Preservation

open Term
open Val
open Typ

---------------------
-- Proposition 5.6 --
---------------------

theorem fund_prop {σ : Store} : σ.now.type # δ # Γ ⊢ t ∷ A → (σ ⧸ δ).Sub ε → HRel ε σ.now  → γ ∈ C⟦Γ⟧ε → t.subs γ 0 ∈ T⟦A⟧ε  := by
  intros T
  revert γ ε
  induction T <;> intros ε1 γ S EN G <;> simp
  case unit => apply TRel.VRel; simp; rfl
  case lam t' _ T IH =>
    apply TRel.VRel; simp;
    constructor
    . have T' := HasType.lam (T.Sub' S); apply CRel.SubsType at G
      have G' := HasType.subs_top G T'; simp at G'
      apply G'
    . exists t'.subs γ 1; constructor
      . congr
      . intros ε1 S' s p V
        simp[Term.sub]
        rw[Term.subs_subs (G.SubsType)]
        apply IH (S.trans S') (EN.Sub S')
        constructor; assumption; apply G.Sub' S'
    . constructor
  case var x B E =>
    split
    . apply TRel.VRel'
      apply CRel.VRel'; assumption; apply getElem?_pos; assumption
    . apply CRel.length at G; grind
  case never =>
    apply TRel.VRel; simp
    constructor; constructor
  case chan L =>
    apply TRel.VRel; simp; constructor;
    apply AList.Sub.lookup S.chans L; constructor
  case loc l A Γ L =>
    rw[Heap.type_lookup] at L
    simp at L
    rcases L with ⟨ s , L , rfl⟩
    apply TRel.VRel; simp; exists l; split_ands
    . rfl
    . exists s; split_ands
      . apply AList.Sub.lookup S.store.now L
      . rfl
      . apply HRel.lookup_VRel EN at L; assumption
  case app Γ s A B t T1 T2 IH1 IH2 =>
    have U1 := IH1 S EN G
    unfold TRel at U1
    rcases U1 with ⟨ v, ε2 , R1 , U1 ⟩
    simp at U1
    rcases U1 with ⟨ U1 , s' , rfl , V1  ⟩
    have S1 := Eval.incr R1
    have U2 := IH2 (S.trans S1) (EN.Sub S1) (G.Sub' S1)
    unfold TRel at U2
    rcases U2 with ⟨ w, ε3 , R2 , U2 ⟩
    have S3 := Eval.incr R2
    have U3 := V1 ε3 S3 w.1 w.2 U2
    unfold TRel at U3
    rcases U3 with ⟨ w, ε4 , R3 , U3 ⟩
    unfold TRel
    exists w, ε4; constructor
    . constructor; apply R1; apply R2; apply R3
    . assumption
  case appE Γ s A B t T1 T2 IH1 IH2 =>
    have U1 := IH1 S EN G
    unfold TRel at U1
    rcases U1 with ⟨ v, ε2 , R1 , U1 ⟩
    simp at U1
    have S1 := Eval.incr R1
    have U2 := IH2 (S.trans S1) (EN.Sub S1) (G.Sub' S1)
    unfold TRel at U2
    rcases U2 with ⟨ w, ε3 , R2 , U2 ⟩
    simp at U2
    have S3 := Eval.incr R2
    have U1' := U1.Sub' S3
    unfold TRel
    exists (v.appE w), ε3; constructor
    . constructor<;> assumption
    . simp; constructor; apply U1'; apply U2
  case appA Γ s A B t T1 T2 IH1 IH2 =>
    have U1 := IH1 S EN G
    unfold TRel at U1
    rcases U1 with ⟨ v, ε2 , R1 , U1 ⟩
    simp at U1
    rcases HasType.delayA_value U1 with ⟨s1, rfl⟩
    have S1 := Eval.incr R1
    have U2 := IH2 (S.trans S1) (EN.Sub S1) (G.Sub' S1)
    unfold TRel at U2
    rcases U2 with ⟨ w, ε3 , R2 , U2 ⟩
    simp at U2
    rcases HasType.delayA_value U2 with ⟨s2, rfl⟩
    have S3 := Eval.incr R2
    have U1' := U1.Sub' S3
    cases U1'; cases U2
    unfold TRel
    exists (delay (Term.app s1 s2)), ε3; constructor
    . constructor<;>assumption
    . simp; constructor; constructor; assumption
      assumption
  case sig Γ s A t T1 T2 IH1 IH2 =>
    have U1 := IH1 S EN G
    unfold TRel at U1
    rcases U1 with ⟨ v, ε2 , R1 , U1 ⟩
    have S1 := Eval.incr R1
    have U2 := IH2 (S.trans S1) (EN.Sub S1) (G.Sub' S1)
    unfold TRel at U2
    rcases U2 with ⟨ w, ε3 , R2 , U2 ⟩
    simp at U2
    unfold TRel
    rcases ε3 with ⟨σ , δ⟩
    let s : Sig := ⟨ A , v , false, w ⟩
    let ε4 := σ.insert σ.alloc s σ.alloc_fresh ⧸ δ
    have S3 := Eval.incr R2
    exists .loc σ.alloc, ε4; constructor
    . constructor; apply R1; apply R2
    . simp; exists σ.alloc; split_ands
      . rfl
      . exists s; split_ands
        . unfold ε4; simp[Store.insert,Env.now]
          apply AList.lookup_cons
        . unfold s; simp
        . unfold s; simp; apply VRel.Sub'; apply U1
          apply S3.trans; constructor<;> simp[ε4]
  case newchan A =>
    unfold TRel
    rcases ε1 with ⟨σ , δ⟩
    exists chan δ.alloc, σ ⧸ δ.cons δ.alloc A δ.alloc_fresh
    constructor
    . constructor
    . simp; constructor; apply AList.lookup_cons
  case tail Γ t A T IH =>
    have U := IH S EN G
    unfold TRel at U
    rcases U with ⟨ v, ε2 , R , U ⟩
    simp at U
    rcases U with ⟨l, rfl, s, L, Q, U⟩
    unfold TRel
    exists tail (loc l), ε2; constructor
    . constructor; apply R
    . simp; constructor; constructor
      rw[Heap.type_lookup]; simp
      exists s
  case wait Γ t A T IH =>
    have U := IH S EN G
    unfold TRel at U
    rcases U with ⟨ v, ε2 , R , U ⟩
    simp at U
    unfold TRel
    exists wait v, ε2; split_ands
    . constructor; apply R
    . simp; constructor; apply U
  case trig Γ t A T IH =>
    have U := IH S EN G
    unfold TRel at U
    rcases U with ⟨ v, ε2 , R , U ⟩
    simp at U
    rcases U with ⟨l, rfl, s, L, Q, U⟩
    unfold TRel
    exists trig (loc l), ε2; constructor
    . constructor; apply R
    . simp; constructor; constructor
      rw[Heap.type_lookup]; simp
      exists s
  case in1 Γ t A B T IH =>
    have U := IH S EN G
    unfold TRel at U
    rcases U with ⟨ v, ε2 , R , U ⟩
    unfold TRel
    exists in1 v, ε2; constructor
    . constructor; apply R
    . simp; left; exists v, v.property
  case in2 Γ t A B T IH =>
    have U := IH S EN G
    unfold TRel at U
    rcases U with ⟨ v, ε2 , R , U ⟩
    unfold TRel
    exists in2 v, ε2; constructor
    . constructor; apply R
    . simp; right; exists v, v.property
  case pair Γ s A t B T1 T2 IH1 IH2 =>
    have U1 := IH1 S EN G
    unfold TRel at U1
    rcases U1 with ⟨ v1, ε2 , R1 , U1 ⟩
    have S1 := Eval.incr R1
    have U2 := IH2 (S.trans S1) (EN.Sub S1) (G.Sub' S1)
    unfold TRel at U2
    rcases U2 with ⟨ v2, ε3 , R2 , U2 ⟩
    have S3 := Eval.incr R2
    unfold TRel
    exists pair v1 v2, ε3; constructor
    . constructor; apply R1; apply R2
    . simp; exists v1, v1.2, v2, v2.2; split_ands
      . rfl
      . apply U1.Sub' S3
      . apply U2
  case pr1 Γ t A T IH =>
    have U := IH S EN G
    unfold TRel at U
    rcases U with ⟨ v, ε2 , R , U ⟩
    simp at U
    rcases U with ⟨t1,V1,t2,V2, rfl, U1 , U2⟩
    unfold TRel
    exists ⟨t1, V1⟩, ε2; constructor
    . constructor; apply R
    . apply U1
  case pr2 Γ t A T IH =>
    have U := IH S EN G
    unfold TRel at U
    rcases U with ⟨ v, ε2 , R , U ⟩
    simp at U
    rcases U with ⟨t1,V1,t2,V2, rfl, U1 , U2⟩
    unfold TRel
    exists ⟨t2, V2⟩, ε2; constructor
    . constructor; apply R
    . apply U2
  case delay Γ t A T IH =>
    have T := T.Sub' S
    have T' := HasType.subs_CRel G T
    unfold TRel
    exists delay (t.subs γ 0), ε1; split_ands
    . constructor
    . simp; constructor; assumption
  case sync Γ s A B t T1 T2 IH1 IH2 =>
    have U1 := IH1 S EN G
    unfold TRel at U1
    rcases U1 with ⟨ v, ε2 , R1 , U1 ⟩
    simp at U1
    have S1 := Eval.incr R1
    have U2 := IH2 (S.trans S1) (EN.Sub S1) (G.Sub' S1)
    unfold TRel at U2
    rcases U2 with ⟨ w, ε3 , R2 , U2 ⟩
    simp at U2
    have S3 := Eval.incr R2
    have U1' := U1.Sub' S3
    unfold TRel
    exists (v.sync w), ε3; constructor
    . constructor<;> assumption
    . simp; constructor; apply U1'; apply U2
  case head Γ t A T IH =>
    have U := IH S EN G
    unfold TRel at U
    rcases U with ⟨ v, ε2 , R , U ⟩
    simp at U
    rcases U with ⟨ l , rfl , s , L , rfl , U ⟩
    unfold TRel
    exists s.head, ε2; split_ands
    . constructor; apply R; apply L
    . apply U
  case fix A Γ t T IH =>
    let v : Val := delay (t.subs γ 1).fix
    have V : v ∈ V⟦□ A⟧(ε1)  := by
      simp[v]; constructor; constructor
      apply HasType.subs
      . apply CRel.SubsType G
      . simp; apply T.Sub' S
    have G' : (v :: γ) ∈ C⟦(□ A :: Γ)⟧ε1 := by
      constructor<;> assumption
    apply IH S at G'
    simp[TRel] at G'
    rcases G' with ⟨ u , p , ε2, R, U ⟩
    unfold TRel
    exists ⟨u,p⟩, ε2;split_ands
    . unfold v at *; constructor; simp[Term.sub]
      rw[Term.subs_subs  (G.SubsType)]; apply R
    . assumption
    . assumption
  case case Γ t A1 A2 t1 A t2 T T1 T2 IH IH1 IH2 =>
    have U := IH S EN G
    unfold TRel at U
    rcases U with ⟨ v, ε2 , R , U ⟩
    have S' := R.incr
    simp at U
    rcases U with ⟨ v , p , rfl , U ⟩ |  ⟨ v , p , rfl , U ⟩
    . have G' : (v :: γ) ∈ C⟦(A1 :: Γ)⟧ε2 := by
        constructor
        . assumption
        . apply G.Sub' S'
      have U1 := IH1 (S.trans S') (EN.Sub S') G'
      unfold TRel at U1
      rcases U1 with ⟨ v, ε3 , R1 , U1 ⟩
      unfold TRel; exists v, ε3; split_ands
      . apply Eval.case1; apply R;
        simp[Term.sub]
        rw[Term.subs_subs (G.SubsType)]
        apply R1
      . assumption
    . have G' : (v :: γ) ∈ C⟦(A2 :: Γ)⟧ε2 := by
        constructor
        . assumption
        . apply G.Sub' S'
      have U2 := IH2 (S.trans S') (EN.Sub S') G'
      unfold TRel at U2
      rcases U2 with ⟨ v, ε3 , R2 , U2 ⟩
      unfold TRel; exists v, ε3; split_ands
      . apply Eval.case2; apply R;
        simp[Term.sub]
        rw[Term.subs_subs (G.SubsType)]
        apply R2
      . assumption
  case cons A _ _ WF T IH =>
    cases WF with | mu WF
    have U := IH S EN G
    unfold TRel at U
    rcases U with ⟨ v, ε2 , R , U ⟩
    unfold TRel
    exists cons A v, ε2; constructor
    . constructor; apply R
    . apply VRel.sub_mu WF U
  case recur A B Γ' s t WFA WFB T1 T2 IH1 IH2 =>
    have U := IH2 S EN G
    unfold TRel at U
    rcases U with ⟨ v, ε2 , R , U ⟩
    have Tv := U.HasType
    have S1 := R.incr
    simp at U
    rcases U with ⟨WF_, ⟨i,U⟩⟩
    have TT : (s.subs γ 1).recur B v ∈ T⟦B⟧ε2 := by
      apply TRel.type_closed WFB
      apply TRel.fromTRel'
      apply TRel.recur
      . assumption
      . assumption
      . apply HasType.subs;apply CRel.SubsType (G.Sub' S1); simp; apply T1.Sub' (S.trans S1)
      . intros ε3 S2;apply TRel.VRel;simp
        split_ands
        . apply Tv.Sub' S2
        . apply U.Sub S2
      . intros w ε3 j S3 W
        apply VRel.VRelMu_sub WF_ at W
        . simp at W
          rw[Typ.sub_closed WFB] at W
          unfold Term.sub
          rw[Term.subs_subs G.SubsType];
          apply TRel.type_closed WFB
          apply IH1
          apply S.trans (S1.trans S3)
          apply EN.Sub (S1.trans S3)
          constructor; assumption
          apply G.Sub' (S1.trans S3)
        . apply WF_.sub; constructor; constructor; apply WFB.weaken
    apply TRel.recur_val <;> assumption






/- Two auxiliary lemmas to prove the final version of the fundamental
property for closed terms. -/

lemma fund_prop_aux {σ : Store} : η = σ.now → η.type # δ  ⊢ t ∷ A →  HRel ε η →  (σ ⧸ δ).Sub ε → t ∈ T⟦A⟧ε  := by
  intros E H T S
  rw[E] at *
  suffices H : t.subs [] 0 ∈ T⟦A⟧ε by
    rw[Subs.empty] at H; apply H
  apply fund_prop <;> try assumption
  constructor



lemma IsHeap.HRel_Sub : δ ⊢ₕ η → η.Sub σ.now → HRel (σ ⧸ δ) η := by
  intros T
  revert σ
  induction T <;> intro σ S
  case nil => constructor
  case cons η N' A l hd a tl N T Hd Tl IH =>
    simp at *
    have N : l ∉ ⟪ η, N' ⟫ := by
      intro L
      cases N with | cons N1 N2
      apply N1 at L; contradiction
    have D : ⟪ η, N' ⟫.Disjoint σ.earlier :=by
      apply AList.Sub_Disjoint
      apply Heap.Sub.trans'; apply S
      apply AList.Sub.cons
      apply N
      apply σ.disjoint

    let σ' := Store.mk ⟪η, N'⟫ σ.earlier D
    have T' : HRel (σ ⧸ δ) ⟨ η , N' ⟩ := by
      apply HRel.Sub
      apply IH
      apply Heap.Sub.trans'; apply S
      apply AList.Sub.cons
      apply N
      rfl
    constructor
    . apply T'
    . apply VRel.IsValue_TRel
      apply fund_prop_aux (η:=⟪η, N'⟫) (σ := σ')
      rfl
      apply Hd
      apply T'
      constructor
      simp
      constructor
      apply Heap.Sub.trans'; apply S
      apply AList.Sub.cons
      simp[σ']; apply N
      rfl
      simp

----------------------------------------------------------
-- Corollary 5.8: Fundamental property for closed terms --
----------------------------------------------------------

theorem fund_prop_closed : ε ⊩ t ∷ A →  t ∈ T⟦A⟧ε  := by
  intros T
  apply fund_prop_aux (η := ε.now) (σ := ε.store) (δ := ε.chans)
  . simp
  . apply T.term
  . apply IsHeap.HRel_Sub; apply T.env; rfl
  . rfl
