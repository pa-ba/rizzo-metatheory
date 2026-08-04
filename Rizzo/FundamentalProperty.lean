/-
  Proof of the fundamental property (and its corollary for closed
  terms).
-/

import Rizzo.LogicalRelation
import Rizzo.Preservation

open Term
open MVal
open Typ

---------------------
-- Proposition 5.7 --
---------------------

theorem fund_prop {σ : Store} : Γ ⊢[Δ, σ.now.type] t ∷ A → (∀ B ∈ Γ, B.Closed) →
    (σ ⧸ Δ).le ε → HRel ε σ.now  → γ ∈ C⟦Γ⟧ε → t.subs γ 0 ∈ T⟦A⟧ε  := by
  intros T
  revert γ ε
  induction T <;> intros ε1 γ hΓ S EN G <;> simp
  case unit =>
    apply TRel.VRel (p := .unit)
    vrel; rfl
  case lam A Γ' t' B W T IH =>
    apply TRel.VRel (p := .lam)
    vrel
    refine ⟨?_, t'.subs γ 1, rfl, ?_⟩
    . have T' := HasType.lam W (T.le' S)
      have G' := HasType.subs_top (CRel.SubsType G hΓ) T'
      simpa using G'
    . intro ε2 S' v1 V1
      have hsub : (t'.subs γ 1).sub v1.val = t'.subs (v1.val :: γ) 0 := by
        simpa [Term.sub] using Term.subs_subs (s := v1.val) (i := 0) (CRel.SubsType G hΓ)
      rw [hsub]
      have hΓ' : ∀ B' ∈ A :: Γ', B'.Closed := List.forall_mem_cons.mpr ⟨W, hΓ⟩
      have G2 : (v1.val :: γ) ∈ C⟦(A :: Γ')⟧ε2 := CRel.cons V1 (G.le' S')
      exact IH hΓ' (S.trans S') (EN.le S') G2
  case var x B E =>
    split
    . apply TRel.VRel'
      apply CRel.VRel'; assumption; apply getElem?_pos; assumption
    . apply CRel.length at G; grind
  case never W =>
    apply TRel.VRel (p := .never)
    vrel; simpa using HasType.never W
  case chan L =>
    apply TRel.VRel (p := .chan)
    vrel
    simpa using HasType.chan (AList.le.lookup S.chans L)
  case loc l A Γ' L =>
    rw[Heap.type_lookup] at L
    simp at L
    rcases L with ⟨ s , L , rfl⟩
    apply TRel.VRel (p := .loc)
    have V := HRel.lookup_VRel EN L
    vrel
    exact ⟨l, rfl, s, AList.le.lookup S.store.now L, by simp, V⟩
  case app Γ' s A B t T1 T2 IH1 IH2 =>
    obtain ⟨ v, ε2 , R1 , U1 ⟩ := (IH1 hΓ S EN G).elim
    vrel at U1
    rcases U1 with ⟨ U1 , s' , rfl , V1  ⟩
    have S1 := Eval.incr R1
    obtain ⟨ w, ε3 , R2 , U2 ⟩ := (IH2 hΓ (S.trans S1) (EN.le S1) (G.le' S1)).elim
    have S3 := Eval.incr R2
    have V3 := V1 ε3 S3 w U2
    simp only [TRel] at V3
    obtain ⟨ u, ε4 , R3 , U3 ⟩ := V3
    exact TRel.intro (.app R1 R2 R3) U3
  case appE Γ' s A B t T1 T2 IH1 IH2 =>
    obtain ⟨ v, ε2 , R1 , U1 ⟩ := (IH1 hΓ S EN G).elim
    have S1 := Eval.incr R1
    obtain ⟨ w, ε3 , R2 , U2 ⟩ := (IH2 hΓ (S.trans S1) (EN.le S1) (G.le' S1)).elim
    have S3 := Eval.incr R2
    exact TRel.intro (.appE R1 R2) (VRel.appE (by simp) (VRel.kripke (by simp) U1 S3) U2)
  case appA Γ' s A B t T1 T2 IH1 IH2 =>
    obtain ⟨ v, ε2 , R1 , U1 ⟩ := (IH1 hΓ S EN G).elim
    vrel at U1
    simp only [Typ.substAll_nil, LRelSubs.types_nil] at U1
    rcases HasType.delayA_value U1 with ⟨s1, rfl⟩
    have S1 := Eval.incr R1
    obtain ⟨ w, ε3 , R2 , U2 ⟩ := (IH2 hΓ (S.trans S1) (EN.le S1) (G.le' S1)).elim
    vrel at U2
    simp only [Typ.substAll_nil, LRelSubs.types_nil] at U2
    rcases HasType.delayA_value U2 with ⟨s2, rfl⟩
    have S3 := Eval.incr R2
    have U1' := U1.le' S3
    cases U1'; cases U2
    refine TRel.intro (.appA R1 R2) ?_
    vrel
    simp only [Typ.substAll_nil, LRelSubs.types_nil]
    constructor; constructor <;> assumption
  case sig Γ' s A t T1 T2 IH1 IH2 =>
    obtain ⟨ v, ε2 , R1 , U1 ⟩ := (IH1 hΓ S EN G).elim
    have S1 := Eval.incr R1
    obtain ⟨ w, ε3 , R2 , U2 ⟩ := (IH2 hΓ (S.trans S1) (EN.le S1) (G.le' S1)).elim
    rcases ε3 with ⟨σ , Δ'⟩
    let sg : Sig := ⟨ A , v , false, w ⟩
    let ε4 := σ.insert σ.alloc sg σ.alloc_fresh ⧸ Δ'
    have S3 := Eval.incr R2
    refine TRel.intro (v := MVal.loc σ.alloc) (ε' := ε4) (Eval.sig R1 R2) ?_
    vrel
    exists σ.alloc; split_ands
    . rfl
    . exists sg; split_ands
      . unfold ε4; simp[Store.insert,Env.now]
        apply AList.lookup_cons
      . unfold sg; simp
      . unfold sg; simp
        refine VRel.kripke (by simp) U1 ?_
        apply S3.trans; constructor<;> simp[ε4]
  case newchan A W =>
    rcases ε1 with ⟨σ , Δ'⟩
    refine TRel.intro (v := MVal.chan Δ'.alloc)
      (ε' := σ ⧸ Δ'.cons Δ'.alloc A Δ'.alloc_fresh) Eval.newchan ?_
    vrel
    simpa using HasType.chan (A := A) (by apply AList.lookup_cons)
  case tail Γ' t A T IH =>
    obtain ⟨ v, ε2 , R , U ⟩ := (IH hΓ S EN G).elim
    have U' := U
    vrel at U'
    rcases U' with ⟨l, rfl, s, L, Q, U'⟩
    exact TRel.intro (.tail R) (VRel.tail (by simp) U)
  case wait Γ' t A T IH =>
    obtain ⟨ v, ε2 , R , U ⟩ := (IH hΓ S EN G).elim
    vrel at U
    obtain ⟨κ, hκ⟩ := HasType.chan_value U v.property
    have hv : v = MVal.chan κ := Subtype.ext hκ
    subst hv
    refine TRel.intro (.wait R) ?_
    vrel
    simp only [Typ.substAll_nil, LRelSubs.types_nil] at U ⊢
    constructor; apply U
  case watch Γ' t A T IH =>
    obtain ⟨ v, ε2 , R , U ⟩ := (IH hΓ S EN G).elim
    vrel at U
    rcases U with ⟨l, rfl, s, L, Q, U⟩
    refine TRel.intro (.watch R) ?_
    vrel
    simp only [Typ.substAll_nil, LRelSubs.types_nil]
    constructor; constructor; rw[Heap.type_lookup]; simp
    exact ⟨s, L, by simpa using Q⟩
  case in1 Γ' t A B W T IH =>
    obtain ⟨ v, ε2 , R , U ⟩ := (IH hΓ S EN G).elim
    refine TRel.intro (v := MVal.in1 v) (Eval.in1 R) ?_
    vrel
    exact Or.inl ⟨v, by simp, U⟩
  case in2 Γ' t A B W T IH =>
    obtain ⟨ v, ε2 , R , U ⟩ := (IH hΓ S EN G).elim
    refine TRel.intro (v := MVal.in2 v) (Eval.in2 R) ?_
    vrel
    exact Or.inr ⟨v, by simp, U⟩
  case pair Γ' s A t B T1 T2 IH1 IH2 =>
    obtain ⟨ v1, ε2 , R1 , U1 ⟩ := (IH1 hΓ S EN G).elim
    have S1 := Eval.incr R1
    obtain ⟨ v2, ε3 , R2 , U2 ⟩ := (IH2 hΓ (S.trans S1) (EN.le S1) (G.le' S1)).elim
    have S3 := Eval.incr R2
    refine TRel.intro (.pair R1 R2) ?_
    vrel
    exact ⟨v1, v2, rfl, VRel.kripke (by simp) U1 S3, U2⟩
  case pr1 Γ' t A T IH =>
    exact TRel.pr1 (IH hΓ S EN G)
  case pr2 Γ' t A T IH =>
    exact TRel.pr2 (IH hΓ S EN G)
  case delay Γ' t A T IH =>
    have T := T.le' S
    have T' := HasType.subs_CRel G hΓ T
    refine TRel.intro (.value .delay) ?_
    vrel
    simp only [Typ.substAll_nil, LRelSubs.types_nil]
    constructor; assumption
  case select Γ' s A B t W1 W2 T1 T2 IH1 IH2 =>
    obtain ⟨ v, ε2 , R1 , U1 ⟩ := (IH1 hΓ S EN G).elim
    vrel at U1
    have S1 := Eval.incr R1
    obtain ⟨ w, ε3 , R2 , U2 ⟩ := (IH2 hΓ (S.trans S1) (EN.le S1) (G.le' S1)).elim
    vrel at U2
    have S3 := Eval.incr R2
    have U1' := U1.le' S3
    refine TRel.intro (.select R1 R2) ?_
    vrel
    simp only [Typ.substAll_nil, LRelSubs.types_nil] at U1' U2 ⊢
    exact HasType.select W1 W2 U1' U2
  case head Γ' t A T IH =>
    exact TRel.head (IH hΓ S EN G)
  case fix A Γ' t W T IH =>
    refine TRel.fix ?_ rfl ?_
    · simp only [Typ.substAll_nil, LRelSubs.types_nil]
      apply HasType.fix W
      apply HasType.subs
      · apply CRel.SubsType G hΓ
      · simp; apply T.le' S
    · intro v p Vv
      have hΓ' : ∀ B' ∈ □ A :: Γ', B'.Closed := List.forall_mem_cons.mpr ⟨Typ.Wf.delayA W, hΓ⟩
      have G' : (v :: γ) ∈ C⟦(□ A :: Γ')⟧ε1 := CRel.cons Vv G
      simp only [Term.sub]
      rw [Term.subs_subs (CRel.SubsType G hΓ)]
      exact IH hΓ' S EN G'
  case case Γ' t A1 A2 t1 A t2 W1 W2 T T1 T2 IH IH1 IH2 =>
    refine TRel.case (IH hΓ S EN G) ?_ ?_
    · intro v ε' S' U
      have hΓ' : ∀ B' ∈ A1 :: Γ', B'.Closed := List.forall_mem_cons.mpr ⟨W1, hΓ⟩
      have G' : (v.val :: γ) ∈ C⟦(A1 :: Γ')⟧ε' := by
        constructor
        · exact U
        · exact G.le' S'
      simp only [Term.sub]
      rw [Term.subs_subs (CRel.SubsType G hΓ)]
      exact IH1 hΓ' (S.trans S') (EN.le S') G'
    · intro v ε' S' U
      have hΓ' : ∀ B' ∈ A2 :: Γ', B'.Closed := List.forall_mem_cons.mpr ⟨W2, hΓ⟩
      have G' : (v.val :: γ) ∈ C⟦(A2 :: Γ')⟧ε' := by
        constructor
        · exact U
        · exact G.le' S'
      simp only [Term.sub]
      rw [Term.subs_subs (CRel.SubsType G hΓ)]
      exact IH2 hΓ' (S.trans S') (EN.le S') G'
  case cons A _ _ WF T IH =>
    cases WF with | mu WF
    obtain ⟨ v, ε2 , R , U ⟩ := (IH hΓ S EN G).elim
    exact TRel.intro (.cons R) (VRel.sub_mu WF U)
  case recur A B Γ' s t WFmu WFB T1 T2 IH1 IH2 =>
    obtain ⟨ v, ε2 , R , U ⟩ := (IH2 hΓ S EN G).elim
    have WFA : 1 ⊢ A ∷type := by cases WFmu with | mu W => exact W
    have Tv : ⊢{ε2} v.val ∷ μ A := VRel.HasType WFmu U
    have S1 := R.incr
    have Tssub : [A.sub (μ A ⨂ B)] ⊢{ε2} s.subs γ 1 ∷ B := by
      have h := HasType.subs (Γ := [A.sub (μ A ⨂ B)])
        (CRel.SubsType (G.le' S1) hΓ) (by simpa using (T1.le' (S.trans S1)))
      simpa using h
    have hWopen : 1 ⊢ (A.sub (α₀ ⨂ B)) ∷type :=
      WFA.weaken.sub (Typ.Wf.prod (Typ.Wf.var (n := 1) (by omega)) (WFB.mono (by omega)))
    have TT : Term.recur B (s.subs γ 1) v.val ∈ T⟦B⟧ε2 := by
      have hrec : Term.recur B (s.subs γ 1) v.val ∈ T'⟦B⟧(LRelOf.mu A ρ0 :: ρ0)#ε2 := by
        refine TRel.recur WFA WFB Tssub ?_ ?_
        · -- the scrutinee value, at the var-0 relation over the µ-entry
          intro ε3 S2
          refine TRel.intro (Eval.value v.prop) ?_
          vrel
          refine ⟨LRelOf.mu A ρ0, rfl, ?_, ?_⟩
          · simpa using (Tv.le' S2)
          · simp only [LRelOf.mu_rel]
            exact VRel.kripke (by simp) U S2
        · -- the step substitution
          intro w ε3 S3 W
          have W' := VRel.VRelMu_sub WFA hWopen W
          have heq : (A.sub (Typ.var 0 ⨂ B)).sub (μ A) = A.sub (μ A ⨂ B) := by
            have hinner : (Typ.var 0 ⨂ B).substAll [μ A] = μ A ⨂ B := by
              show (Typ.var 0).substAll [μ A] ⨂ B.substAll [μ A] = μ A ⨂ B
              rw [Typ.substAll_closed WFB]
              simp [Typ.substAll]
            rw [← Typ.substAll_singleton hWopen, ← Typ.substAll_singleton WFA,
                Typ.substAll_substAll (by simpa using WFA), List.map_cons, List.map_nil,
                hinner, Typ.substAll_singleton WFA]
          rw [heq] at W'
          have G' : (w.val :: γ) ∈ C⟦(A.sub (μ A ⨂ B) :: Γ')⟧ε3 := by
            constructor
            . exact W'
            . apply G.le' (S1.trans S3)
          have hΓ' : ∀ B' ∈ A.sub (μ A ⨂ B) :: Γ', B'.Closed :=
            List.forall_mem_cons.mpr ⟨WFA.sub (Typ.Wf.prod WFmu WFB), hΓ⟩
          have h := IH1 hΓ' (S.trans (S1.trans S3)) (EN.le (S1.trans S3)) G'
          have hsub : (s.subs γ 1).sub w.val = s.subs (w.val :: γ) 0 := by
            simpa [Term.sub] using Term.subs_subs (s := w.val) (i := 0)
              (CRel.SubsType (G.le' (S1.trans S3)) hΓ)
          rw [hsub]
          exact h.type_closed WFB
      exact (hrec (Env.refl ε2)).type_closed WFB
    exact TRel.recur_val R U TT




/- Two auxiliary lemmas to prove the final version of the fundamental
property for closed terms. -/

lemma fund_prop_aux {σ : Store} : η = σ.now → ⊢[Δ, η.type] t ∷ A →  HRel ε η →  (σ ⧸ Δ).le ε → t ∈ T⟦A⟧ε  := by
  intros E H T S
  rw[E] at *
  suffices H : t.subs [] 0 ∈ T⟦A⟧ε by
    rw[Subs.empty] at H; apply H
  apply fund_prop <;> try assumption
  . simp
  . constructor



lemma IsHeap.HRel_Sub : ⊢[Δ] η ∷now → η.le σ.now → HRel (σ ⧸ Δ) η := by
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
      apply AList.le_Disjoint
      apply Heap.le.trans'; apply S
      apply AList.le.cons
      apply N
      apply σ.disjoint

    let σ' := Store.mk ⟪η, N'⟫ σ.earlier D
    have T' : HRel (σ ⧸ Δ) ⟨ η , N' ⟩ := by
      apply HRel.le
      apply IH
      apply Heap.le.trans'; apply S
      apply AList.le.cons
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
      apply Heap.le.trans'; apply S
      apply AList.le.cons
      simp[σ']; apply N
      rfl
      simp

----------------------------------------------------------
-- Corollary 5.9: Fundamental property for closed terms --
----------------------------------------------------------

theorem fund_prop_closed : ⊩{ε} t ∷ A →  t ∈ T⟦A⟧ε  := by
  intros T
  apply fund_prop_aux (η := ε.now) (σ := ε.store) (Δ := ε.chans)
  . simp
  . apply T.term
  . apply IsHeap.HRel_Sub; apply T.env; rfl
  . rfl
