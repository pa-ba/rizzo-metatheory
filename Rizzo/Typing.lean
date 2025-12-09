/-
Definition of the typing relation
-/

import Rizzo.Env
import Rizzo.Syntax


open Term
open Typ

---------------------
-- Typing of Terms --
---------------------

abbrev Ctx : Type := List Typ

inductive HasType (H : HeapTy) (δ : ChanCtx) : Ctx → Term → Typ → Prop where
| unit : HasType H δ Γ unit unit
| lam : HasType H δ (A :: Γ) t B → HasType H δ Γ (lam t) (A ↠ B)
| var : A ∈ Γ[x]? → HasType H δ Γ (var x) A
| loc : A ∈ H.lookup l → HasType H δ Γ (.loc l) (sig A)
| chan : A ∈ δ.lookup κ → HasType H δ Γ (.chan κ) (chan A)
| sig : HasType H δ Γ s A → HasType H δ Γ t (◯ (sig A)) → HasType H δ Γ (sig A s t) (sig A)
| app : HasType H δ Γ s (A ↠ B) → HasType H δ Γ t A → HasType H δ Γ (app s t) B
| appA : HasType H δ Γ s (□ (A ↠ B)) → HasType H δ Γ t (□ A) → HasType H δ Γ (appA s t) (□ B)
| appE : HasType H δ Γ s (□ (A ↠ B)) → HasType H δ Γ t (◯ A) → HasType H δ Γ (appE s t) (◯ B)
| in1 : HasType H δ Γ t A → HasType H δ Γ (in1 t) (A ⊕ B)
| in2 : HasType H δ Γ t B → HasType H δ Γ (in2 t) (A ⊕ B)
| case : HasType H δ Γ t (A1 ⊕ A2) → HasType H δ (A1 :: Γ) t1 B → HasType H δ (A2 :: Γ) t2 B
       → HasType H δ Γ (Term.case t t1 t2) B
| pair : HasType H δ Γ s A → HasType H δ Γ t B → HasType H δ Γ (pair s t) (A ⊗ B)
| pr1 : HasType H δ Γ t (A ⊗ B) → HasType H δ Γ (pr1 t) A
| pr2 : HasType H δ Γ t (A ⊗ B) → HasType H δ Γ (pr2 t) B
| delay : HasType H δ Γ t A → HasType H δ Γ (delay t) (□ A)
| never : HasType H δ Γ never (◯ A)
| newchan : HasType H δ Γ (newchan A) (chan A)
| wait : HasType H δ Γ t (chan A) → HasType H δ Γ (wait t) (◯ A)
| sync : HasType H δ Γ s (◯ A) → HasType H δ Γ t (◯ B) → HasType H δ Γ (sync s t) (◯ ((A ⊕ B) ⊕ (A ⊗ B)))
| cons : (μ A).Closed → HasType H δ Γ t (A.sub (μ A)) → HasType H δ Γ (cons A t) (μ A)
| recur : (μ A).Closed → B.Closed → HasType H δ (A.sub ((μ A) ⊗ B) :: Γ) s B → HasType H δ Γ t (μ A) → HasType H δ Γ (recur B s t) B
| fix : HasType H δ (□ A :: Γ) t A → HasType H δ Γ (fix t) A
| head : HasType H δ Γ t (sig A) → HasType H δ Γ (head t) A
| tail : HasType H δ Γ t (sig A) → HasType H δ Γ (tail t) (◯ (sig A))
| trig : HasType H δ Γ t (sig (A ⊕ unit)) → HasType H δ Γ (trig t) (◯ A)

notation:50 (name := has_type_notation) H : 100 " # " δ : 100 " # " Γ : 60 " ⊢ " t : 60 " ∷ " A : 60 => HasType H δ Γ t A
notation:50 (name := has_type_notation') H : 100 " # " δ : 100" ⊢ " t : 60 " ∷ " A : 60 => HasType H δ [] t A
notation: 50 (name := has_type_notation'') ε : 100 " ## " Γ : 100 " ⊢ " t : 60 " ∷ " A : 60 => HasType (Heap.type (Env.now ε)) (Env.chans ε) Γ t A
notation: 50 (name := has_type_notation''') ε : 60 " ⊢ " t : 60 " ∷ " A : 60 => HasType (Heap.type (Env.now ε)) (Env.chans ε) [] t A

inductive IsHeap : ChanCtx → Heap → Prop where
| nil : IsHeap δ ∅
| cons :
  IsHeap δ ⟨ η , M ⟩ →
  HasType (Heap.type ⟨ η, M⟩) δ [] hd.val A →
  HasType (Heap.type ⟨ η, M⟩) δ [] tl.val (◯ (sig A)) →
  IsHeap δ ⟨ ⟨ l, ⟨ A , hd , a , tl⟩ ⟩ :: η , N ⟩


notation : 80 (name := is_heap_notation) δ : 90" ⊢ₕ " η : 90 => IsHeap δ η

@[grind]
structure EvalType (ε : Env) (Γ : Ctx) (t : Term)  (A : Typ) : Prop where
  mk ::
  term : ε ## Γ ⊢ t ∷  A
  env : ε.chans ⊢ₕ ε.now

notation : 80 (name := eval_type_notation') ε : 91 " # " Γ : 91 " ⊩ " t : 90 " ∷ " A : 90 => EvalType ε Γ t A
notation : 80 (name := eval_type_notation) ε : 91 " ⊩ " t : 90 " ∷ " A : 90 => EvalType ε [] t A

def IsNowEnv (ε : Env) := ε.chans ⊢ₕ ε.store.now

notation "⊩ₑ"  => IsNowEnv

def IsInp δ (i : Inp) := ∃ A ∈ δ.lookup i.chan, ∅ # δ ⊢ i.val ∷ A

notation : 80 (name := is_inp_notation) δ : 90 " ⊢ᵢ " i : 90 => IsInp δ i

--- Well-typed earlier heap

inductive IsEarlierHeap (δ : ChanCtx) : HeapTy → Heap → Prop where
| nil : IsEarlierHeap δ H ∅
| cons :
  IsEarlierHeap δ (H.cons l s.type p) η →
  H # δ ⊢ s.head ∷ s.type →
  H # δ ⊢ s.tail ∷ ◯ (.sig s.type) →
  IsEarlierHeap δ H (η.concat l s p')

notation : 80 (name := is_earlier_heap_notation') H : 91 " # " δ : 91 " ⊩ₕ " η : 90  => IsEarlierHeap δ H η



-- Well-typed environment

def IsEnv (ε : Env) := ⊩ₑ ε /\ ε.now.type # ε.chans ⊩ₕ ε.earlier
notation "⊢ₑ"  => IsEnv

-- well-typed signals stored on the heap

structure SigType (η : Heap) (δ : ChanCtx) (s : Sig) : Prop where
  head : η.type # δ ⊢ s.head ∷ s.type
  tail : η.type # δ ⊢ s.tail ∷ ◯ (.sig s.type)

---------------------------------------
-- Lemmas about the typing relations --
---------------------------------------
@[simp]
lemma SigType.tick : SigType η δ s → SigType η δ s.tick := by
  intro T; cases T; solve_by_elim

lemma HasType.lam_inv  : H # δ # Γ ⊢ t.lam ∷ A ↠ B → H # δ # (A :: Γ) ⊢ t ∷ B := by
  intro T
  cases T
  assumption


lemma HasType.app' {s : Term} : HasType H δ Γ t A → HasType H δ Γ s (A ↠ B) → HasType H δ Γ (s.app t) B := by
  intros; solve_by_elim

@[simp]
lemma HasType.smap {A B : Typ} : H # δ # Γ ⊢ smap B ∷ (A ↠ B) ↠ A.sig ↠ B.sig := by
  simp[Term.smap];repeat constructor


lemma HasType.fmap : A.Open → H # δ # Γ ⊢ fmap A C ∷ (B ↠ C) ↠ A.sub B ↠ A.sub C := by
  intros WF
  revert Γ
  induction A<;>intros Γ <;>simp[Term.fmap]
  case unit => solve_by_elim
  case prod A1 A2 IH1 IH2 =>
    cases WF with | prod WF1 WF2
    constructor;constructor;constructor
    . apply HasType.app'
      . constructor;constructor; rfl
      . apply HasType.app'
        . constructor;rfl
        . apply IH1 WF1
    . apply HasType.app'
      . constructor;constructor; simp;constructor<;> rfl
      . apply HasType.app'
        . constructor;rfl
        . apply IH2 WF2
  case sum A1 A2 IH1 IH2 =>
    cases WF with | sum WF1 WF2
    constructor;constructor;constructor
    . constructor; simp;constructor<;>rfl
    . constructor;apply HasType.app'
      . constructor;simp;rfl
      . apply HasType.app'
        . constructor;rfl
        . apply IH1 WF1
    . constructor;apply HasType.app'
      . constructor;simp;rfl
      . apply HasType.app'
        . constructor;rfl
        . apply IH2 WF2
  case arr | delayA | delayE | chan =>
    constructor; constructor;constructor;simp;
    cases WF
    (repeat rewrite[Typ.sub_closed])<;>  grind
  case var => repeat constructor;constructor;constructor<;>(constructor; rfl)
  case mu => solve_by_elim
  case sig A IH =>
    cases WF
    constructor; constructor;apply HasType.app';
    constructor;rfl;apply HasType.app';apply HasType.app'
    constructor;rfl;apply IH;assumption
    apply HasType.smap




------------------------------------------------
-- The order on environments preserves typing --
------------------------------------------------

--------------------------
-- Lemma 5.2: weakening --
--------------------------

@[grind .]
lemma HasType.Sub :
  H # δ # Γ ⊢ t ∷ A → H.Sub H' → δ.Sub δ' → H' # δ' # Γ ⊢ t ∷ A := by
    intros T SH Sδ
    induction T <;> try {constructor <;> assumption}
    case loc M => constructor; apply SH.lookup at M; apply M
    case chan M => constructor; apply Sδ.lookup at M; apply M


@[grind .]
lemma HasType.Sub' {ε ε' : Env} :
  ε ## Γ ⊢ t ∷ A → ε.Sub ε' → ε' ##  Γ ⊢ t ∷ A := by
    intros T S
    apply T.Sub S.store.now.type S.chans


lemma IsHeap.Sub : δ.Sub δ' → δ ⊢ₕ η → δ' ⊢ₕ η := by
  intros D T
  induction T
  case nil => constructor
  case cons H1 H2 H3 H4 IH =>
    constructor <;> try assumption
    . apply HasType.Sub H3 <;> simp[D]
    . apply HasType.Sub H4 <;> simp[D]



lemma EvalType.Sub :
   ε # Γ ⊩ t ∷ A → ε.Sub ε' → ⊩ₑ ε' → ε' #Γ ⊩ t ∷ A := by
   intros T S E
   constructor
   case term => apply T.term.Sub <;> try grind
   case env => apply E

/--
On well-typed terms, clocks are closed under expansion of heaps.
-/

lemma HasType.ticked_Sub {t : Term} : η.type # δ ⊢ t ∷ ◯ A → η.Sub η' → t.ticked η κ = t.ticked η' κ := by
  intros T S
  revert A
  induction t <;> intros A T <;> try simp[Term.ticked]
  case wait t E => cases t  <;> try simp[Term.ticked]
  case trig t E =>
    cases t  <;> try simp[Term.ticked]
    case loc l =>
      cases T with | trig T
      cases T with | loc M
      rw[Heap.type_lookup] at M
      simp at M
      rcases M with ⟨s, M, R⟩
      have M' := AList.Sub.lookup S M
      rw[M,M']
  case sync t1 t2 E1 E2 =>
    cases T with | sync T1 T2
    rw[E1 T1,E2 T2]
  case appE E1 E2 =>
    cases T with | appE T1 T2
    rw[E2 T2]
  case tail t E =>
    cases t  <;> try simp[Term.ticked]
    case loc l =>
      cases T with | tail T
      cases T with | loc M
      rw[Heap.type_lookup] at M
      simp at M
      rcases M with ⟨s, M, R⟩
      have M' := AList.Sub.lookup S M
      rw[M,M']


lemma SigType.Sub : SigType η δ s → η.Sub η' → δ.Sub δ' → SigType η' δ' s := by
  intros T S1 S2
  constructor
  . apply T.head.Sub <;> grind
  . apply T.tail.Sub <;> grind


-- Inversion lemma for IsEarlierHeap --


lemma IsEarlierHeap.cons_inv : H # δ ⊩ₕ η.concat l s p
    → ∃ p', H.cons l s.type p' # δ ⊩ₕ η /\
    H # δ ⊢ s.head ∷ s.type /\
    H # δ ⊢ s.tail ∷ ◯ (.sig s.type) := by
  generalize E: η.concat l s p = η'
  intros T
  cases T
  case nil =>
    simp[AList.concat] at E;
    have E' : AList.entries ∅ = η.entries ++ [⟨l, s⟩] := by
      rw [<- E]
    apply List.concat_non_empty at E'
    contradiction
  case cons η' =>
    simp[AList.concat] at E
    rewrite[<- List.concat_eq_append] at E
    rewrite[<- List.concat_eq_append] at E
    apply List.of_concat_eq_concat at E
    rcases E with ⟨E1, E2⟩
    rw [<- AList.ext_iff] at E1
    subst E1
    cases E2
    constructor;split_ands<;>assumption

lemma IsEnv.tail_type : ⊢ₑ (ηN ✓[D] AList.concat  ηE l' s p ⧸ δ) →
    ηN ✓[D] AList.concat ηE l' s p ⧸ δ ⊩ s.tail ∷ ◯ (.sig s.type) := by
  intros T
  have T' := T.2
  simp[Env.now,Env.earlier] at T'
  have T'' := T'.cons_inv
  rcases T'' with ⟨p', T'', Hd, Tl⟩
  constructor
  . simp[Env.now]; apply Tl
  . apply T.1





lemma IsEarlierHeap.Sub : H # δ ⊩ₕ η → H.Sub H' → δ.Sub δ' → H'.keys.Disjoint η.keys → H' # δ' ⊩ₕ η := by
  intros E SH Sd D
  revert H' δ'
  induction E <;> intros H' δ' SH Sd D
  case nil => constructor
  case cons l _ _ _ _ Hd Tl IH =>
    have p : l ∉ H' := by
      symm at D
      apply AList.concat_cons_Disjoint_nin_keys D
    constructor
    . apply IH
      . apply AList.Sub.cons_both SH; assumption
      . assumption
      . symm; apply AList.concat_cons_Disjoint_keys;symm; assumption
    . apply Hd.Sub SH Sd
    . apply Tl.Sub SH Sd

lemma IsEarlierHeap.Sub' {ε ε' : Env} :
    ε.now.type # ε.chans ⊩ₕ ε.earlier → ε.Sub ε' → ε'.now.type  # ε'.chans ⊩ₕ ε'.earlier  := by
  intros E S
  simp[Env.earlier] at *
  rw[S.store.earlier] at E
  apply E.Sub S.store.now.type S.chans
  have D := ε'.store.disjoint
  rw[Heap.type_keys]
  apply D


lemma IsEnv.step : ⊢ₑ ε → ε.Sub ε' → ⊩ₑ ε' →  ⊢ₑ ε' := by
  intro E S N
  cases E with | intro E1 E2
  unfold IsNowEnv at N
  constructor; assumption
  apply E2.Sub' S

lemma IsHeap.append_sub {η η' : Heap} {D : η.Disjoint η' }: δ ⊢ₕ η.append η' D → δ ⊢ₕ η' := by
  intros T
  generalize N : η.entries.length = n
  revert N
  revert η η'
  induction n <;> intros η η' D T E
  case zero =>
    apply AList.length_empty at E
    subst E
    apply T
  case succ m IH =>
    apply AList.cons_decompose at E
    rcases E with ⟨ η'', l, s, p, E, L⟩
    subst E
    cases T with | cons T Hd Tl =>
    apply IH<;>try assumption
    apply  AList.Disjoint_cons D



lemma IsHeap.end_step {η η' : Heap} {D : AList.Disjoint η η'} :
    δ ⊢ₕ η.append η' D → η'.type # δ ⊩ₕ η := by
  intros T
  generalize N : η.entries.length = n
  revert N
  revert η η'
  induction n<;>intro η η' D T N
  case zero =>
    apply AList.length_empty at N
    subst N
    constructor
  case succ n IH =>
    apply AList.concat_decompose at N ; try assumption
    rcases N with ⟨ η'', l, s, p, E, N⟩
    subst E
    have T' : ∃ p D, δ ⊢ₕ η''.append (AList.cons l s η' p) D := by
      constructor; constructor
      rw[<- AList.concat_append] <;> try assumption
      apply  AList.concat_cons_Disjoint_nin D
      apply AList.concat_cons_Disjoint_keys<;>assumption
    rcases T' with ⟨p', D', T'⟩
    constructor
    suffices H : Heap.type (AList.cons l s η' p') # δ ⊩ₕ η'' by
      simp[Heap.type] at *
      apply H
    apply IH <;> try assumption
    . apply IsHeap.append_sub at T'; cases T'; assumption
    . apply IsHeap.append_sub at T'; cases T'; assumption
    . rw[Heap.type_fresh]; assumption


lemma IsHeap.end_step' {η : Heap} : δ ⊢ₕ η → ∅ # δ ⊩ₕ η := by
  intros T
  have E : ∅ = Heap.type ∅ := by
    simp[Heap.type]; rfl
  rw[E]
  apply IsHeap.end_step
  . simp[AList.append]; apply T
  . apply List.disjoint_nil_right


lemma IsEnv.end_step : ⊢ₑ (η ✓[N] ∅ ⧸ δ) → ⊢ₑ (∅ ✓[M] η ⧸ δ) := by
  intros T
  cases T with | intro T1 T2
  unfold IsEnv;
  split_ands
  . constructor
  . simp[Env.earlier,Env.now] at *
    apply T1.end_step'


lemma HasType.loc_inv  : HasType H δ Γ (.loc l) A → ∃ B, B ∈ H.lookup l /\ A = Typ.sig B := by
  intros T
  cases T
  grind


lemma IsEnv.now : ⊢ₑ ε → ⊩ₑ ε := by
  unfold IsEnv IsNowEnv
  intros H; apply H.1





-----------------------------------------------
-- Decomposition lemmas for typing of values --
-----------------------------------------------


lemma HasType.delayA_value' : H # δ ⊢ t ∷ □ A → IsValue t → ∃ s : Term , t = Term.delay s := by
  intros T V
  cases T<;> try {solve | contradiction | cases V}
  case delay t T => exists t

lemma HasType.delayA_value {v : Val} : H # δ ⊢ v ∷ □ A → ∃ s : Term , v = Val.delay s := by
  intros T
  rcases v with ⟨t,V⟩
  cases T<;> try {solve | contradiction | cases V}
  case delay t T => exists t


lemma HasType.chan_value: H # δ ⊢ t ∷ .chan A → IsValue t → ∃ κ , t = Term.chan κ := by
  intros T V
  cases T<;> try {solve | contradiction | cases V}
  case chan κ T => exists κ

lemma HasType.sig_value' : H # δ ⊢ v ∷ Typ.sig A → IsValue v → ∃ l , v = Val.loc l := by
  intros T V
  cases T<;> try {solve | contradiction | cases V}
  case loc l T => exists l

lemma HasType.sig_value {v : Val} : H # δ ⊢ v ∷ Typ.sig A → ∃ l , v = Val.loc l := by
  intros T
  rcases v with ⟨t,V⟩
  simp at T
  apply T.sig_value' at V
  grind


-- TODO: unused lemma?
lemma HasType.prod_value {v : Val} : H # δ ⊢ v ∷ A ⊗ B → ∃ v1 v2 , v = Val.pair v1 v2 := by
  intros T
  rcases v with ⟨t,V⟩
  cases T<;> try {solve | contradiction | cases V}
  case pair s t T1 T2 =>
    cases V with | pair V1  V2
    exists ⟨s,V1⟩ , ⟨t,V2⟩


---------------------------------------
-- Weakening of the typing judgement --
---------------------------------------


lemma HasType.weaken : H # δ # Γ ⊢ t ∷ A → H # δ # Γ ++ Γ' ⊢ t ∷ A := by
  intro T
  cases T
  case var V => constructor;  rw [Γ.getElem?_append_left]; assumption; apply Γ.getElem?_some_length; assumption
  case unit | loc | chan | never | newchan => constructor <;> assumption
  case lam T' | in1 T' | in2 T' | pr1 T' | pr2 T' | delay T' | wait T' | trig T' | fix T' | head T' | tail T'
     => constructor; apply T'.weaken
  case sig T1 T2 | app T2 T1 | appA T1 T2 | appE T1 T2 | pair T1 T2 | sync T1 T2
     => constructor; apply T1.weaken; apply T2.weaken
  case recur T2 _ T1
     => constructor; assumption; assumption; apply T1.weaken; apply T2.weaken
  case  cons T' => constructor; assumption; apply T'.weaken
  case case T1 T2 T3 => constructor; apply T1.weaken; apply T2.weaken; apply T3.weaken;




lemma HasType.weaken_closed: H # δ ⊢ t ∷ A → H # δ # Γ ⊢ t ∷ A := by
  intros T
  apply weaken at T
  simp at T
  apply T



----------------------
-- Auxiliary lemmas --
----------------------

open Val Typ

lemma HasType.insert :
  σ ⧸ δ  ⊩ v.val ∷ A → σ ⧸ δ ⊩ w.val ∷ ◯ (.sig A) →
  σ.insert l ⟨A, v, b, w ⟩ p ⧸ δ  ⊩ .loc l ∷ .sig A := by
  intros T1 T2
  constructor
  case term => constructor; rw[Heap.type_lookup,Store.lookup_insert];simp
  case env =>
    simp; constructor
    . apply T1.env
    . apply T1.term
    . apply T2.term


lemma IsHeap.append{η η' : Heap} {D : η'.Disjoint η} :
  δ  ⊢ₕ η'.append η D → δ  ⊢ₕ η  := by
  intros H
  cases η' with | mk η' N
  induction η' <;> simp[AList.append] at H;
  case nil => apply H
  case cons IH =>
    cases H with | cons H Hd Tl
    apply IH; simp[AList.append]
    . assumption
    . apply List.nodupKeys_of_nodupKeys_cons; assumption
    . apply List.disjoint_of_disjoint_cons_left; assumption



lemma IsHeap.lookup_SigType : δ ⊢ₕ η →
  s ∈ η.lookup l → SigType η δ s := by
    intros HT L1
    simp[AList.lookup] at L1
    have L2 : s ∈ List.dlookup l η.entries := by apply L1
    rewrite [List.mem_dlookup_iff η.nodupKeys] at L2
    simp [Membership.mem] at L2
    clear L1
    induction HT
    case nil => cases L2
    case cons H1 H2 H3 H4 IH =>
      cases L2
      case head  =>
        simp at *
        constructor
        . apply H3.Sub <;> simp [AList.Sub]
        . apply H4.Sub <;> simp [AList.Sub]
      case tail H6 =>
        apply IH at H6
        apply H6.Sub <;> simp [AList.Sub]

-- TODO: unused?
lemma EvalType.weaken_closed: ε ⊩ t ∷ A → ε # Γ ⊩ t ∷ A := by
  intros T
  constructor
  apply T.term.weaken_closed
  apply T.env

lemma HasType.loc_lookup {η : Heap}: η.type # δ ⊢ ↑(Val.loc l) ∷ A → ∃ s, s ∈ η.lookup l :=  by
  intros T
  cases T
  case loc A T =>
    rw[Heap.type_lookup] at T
    simp at T
    rcases T with ⟨s, T, E⟩
    exists s



@[simp,grind .]
lemma EvalType.empty : ∅ # δ ⊢ t ∷ A →  ∅ ⧸ δ ⊩ t ∷ A := by
  intros
  constructor
  simp[Env.now]
  assumption
  constructor
