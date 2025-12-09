import Rizzo.Preservation
import Rizzo.Deterministic


open Term
open Val
open Typ
open List

instance : EmptyCollection (Env → Val → Prop) where
  emptyCollection := fun _ _ => False

structure SemSub : Type where
  mk ::
  type : Typ
  rel : Env → Val → Prop


abbrev ρ0  : SemSub := ⟨Typ.var, ∅⟩

mutual
  @[simp]
  def VRel (A : Typ) (ρ : SemSub) (ε : Env) (v : Val) : Prop :=
    match A with
    | .unit => v = .unit
    | A1 ⊗ A2 => ∃ v1 v2, v = .pair v1 v2 /\ VRel A1 ρ ε v1 /\ VRel A2 ρ ε v2
    | .sum A1 A2 => (∃ v1, v = .in1 v1 /\ VRel A1 ρ ε v1) \/ (∃ v2, v = .in2 v2 /\ VRel A2 ρ ε v2)
    | A1 ↠ A2 => ε ⊢ v ∷ A.sub ρ.type /\ ∃ t, v = .lam t /\ ∀ ε', ε.Sub ε' → ∀ v1, VRel A1 ρ ε' v1 → TRel A2 ρ ε' (t.sub v1)
    | ◯ B => ε ⊢ v ∷ ◯ (B.sub ρ.type)
    | □ B => ε ⊢ v ∷ □ (B.sub ρ.type)
    | .sig B => ∃ l , v = .loc l /\ ∃ s : Sig, s ∈ ε.now.lookup l /\ s.type = B.sub ρ.type /\ VRel B ρ ε s.head
    | .chan B => ε ⊢ v ∷ .chan (B.sub ρ.type)
    | .var  => ε ⊢ v ∷ ρ.1 /\ ρ.2 ε v
    | μ B => B.Open /\ ∃ i, VRelMu i B ε v
  @[simp]
  def VRelMu (i : Nat) (B : Typ) (ε : Env) (v : Val) : Prop :=
    match i with
    | 0 => False
    | .succ j => ∃ (v' : Val) , v = Val.cons B v' /\ VRel B ⟨μ B, VRelMu j B⟩ ε v'
  def TRel (A : Typ) (ρ : SemSub)  (ε : Env) (t : Term) : Prop :=
    ∃ v ε', (t, ε) ⇓ (v, ε') /\ VRel A ρ ε' v
end


inductive CRel : Ctx → Env → Subs → Prop where
  | nil : CRel [] ε []
  | cons : VRel A ρ0 ε ⟨ v, p ⟩  → CRel Γ ε γ → CRel (A :: Γ) ε (v :: γ)

notation : 80 v : 90 " ∈ " "V⟦" A : 90 "⟧" ρ : 90 "#" ε : 90 => VRel A ρ ε v
notation : 80 v : 90 " ∈ " "V⟦" A : 90 "⟧" ε : 90 => VRel A ρ0 ε v
notation : 80 v : 90 " ∈ " "T⟦" A : 90 "⟧" ρ : 90 "#" ε : 90 => TRel A ρ ε v
notation : 80 v : 90 " ∈ " "T⟦" A : 90 "⟧" ε : 90 => TRel A ρ0 ε v

notation : 80 γ : 90 " ∈ " "C⟦" Γ : 90 "⟧" ε : 90 => CRel Γ ε γ

lemma TRel.VRel  :  ⟨t, p⟩  ∈ V⟦A⟧ρ#ε → t ∈ T⟦A⟧ρ#ε := by
  intros V
  simp[TRel]
  exists t, p, ε
  constructor; constructor
  assumption



lemma VRel.IsValue_TRel {v : Val} : v ∈ T⟦A⟧ρ#ε → v ∈ V⟦A⟧ρ#ε  := by
  intros T
  let ⟨t,p⟩ := v
  simp[TRel] at T
  rcases T with ⟨t',p', ε', R, V⟩
  apply Eval.IsValue_rfl p at R
  let ⟨R1,R2⟩ := R
  subst R1 R2
  simp
  assumption

lemma TRel.VRel'  :  (∃ p , ⟨t, p⟩  ∈ V⟦A⟧ρ# ε) → t ∈ T⟦A⟧ρ#ε := by
  intros E;  cases E
  apply TRel.VRel <;> assumption

lemma VRel.type_closed : A.Closed → v ∈ V⟦A⟧ρ # ε → v ∈ V⟦A⟧ρ' # ε := by
  revert v ε ρ ρ'
  induction A <;> intros ρ ε v ρ' WF <;> simp
  case prod IH1 IH2 =>
    intros t1 v1 t2 v2 E V1 V2
    cases WF with | prod WF1 WF2
    apply IH1 WF1 at V1; apply IH2 WF2 at V2
    exists t1, v1,t2,v2
  case sum IH1 IH2 =>
    cases WF with | sum WF1 WF2
    intros V
    rcases V with ⟨t,v,rfl, V⟩ | ⟨t,v,rfl, V⟩
    . left;apply IH1 WF1 at V; exists t,v
    . right;apply IH2 WF2 at V; exists t,v
  case arr IH1 IH2 =>
    cases WF with | arr WF1 WF2
    intros T t E V
    (repeat rewrite[Typ.sub_closed] at ⊢ T)<;>  try grind
    split_ands <;> try assumption
    exists t; split_ands <;> try assumption
    intros ε' S t' v' V'
    apply IH1 WF1 at V'
    apply V ε' S at V'
    unfold TRel at *
    rcases V' with ⟨v,ε',R,V'⟩
    exists v,ε',R
    solve_by_elim
  case var => contradiction
  case delayA | delayE | chan =>
    rcases WF
    intros T
    rw[Typ.sub_closed] at * <;> grind
  case sig A IH =>
    cases WF with | sig WF
    intros l E s L T V
    exists l; split_ands; assumption
    exists s; split_ands;assumption
    rw[T,Typ.sub_closed,Typ.sub_closed]<;> grind
    apply IH;grind; assumption

lemma TRel.type_closed : A.Closed → t ∈ T⟦A⟧ρ # ε → t ∈ T⟦A⟧ρ' # ε := by
  unfold TRel; intros WF TR
  rcases TR with ⟨v,ε',R,V⟩
  exists v,ε',R
  apply VRel.type_closed <;> assumption




lemma VRel.VRelMu_sub : A.Open →  B.Open → (V : v ∈ V⟦B⟧ ⟨μ A, VRelMu i A⟩ # ε) → v ∈ V⟦B.sub (μ A)⟧ ε := by
  intros WFA WFB V
  revert v
  induction B <;> intros v V
  case var => simp at *; split_ands; assumption; exists i; grind
  case unit => simp at *; assumption
  case prod A1 A2 IH1 IH2 =>
    cases WFB
    simp at *;
    rcases V with ⟨v1, p1, v2, p2, rfl, V1 , V2⟩
    exists v1, p1,v2,p2
    split_ands<;> solve_by_elim
  case sum A1 A2 IH1 IH2 =>
    cases WFB
    simp at *;
    rcases V with ⟨v1, p1, rfl, V ⟩ | ⟨v1, p1, rfl, V ⟩
    . left; exists v1, p1; split_ands<;> solve_by_elim
    . right; exists v1, p1; split_ands<;> solve_by_elim
  case arr =>
    rw[Typ.Wf.arr'] at WFB
    rw[Typ.sub_closed] <;> try assumption
    solve_by_elim[VRel.type_closed]
  case delayA | delayE | mu | chan => simp at *; assumption
  case sig B IH =>
    cases WFB
    simp at ⊢ V
    rcases V with ⟨l,rfl,s,L,T,V⟩
    exists l; split_ands;rfl
    exists s; split_ands<;> solve_by_elim


lemma TRel.VRelMu_sub : A.Open →  B.Open → v ∈ T⟦B⟧ ⟨μ A, VRelMu i A⟩ # ε → v ∈ T⟦B.sub (μ A)⟧ ε := by
  intros WFA WFB V
  unfold TRel at *
  rcases V with ⟨w,ε',R,V⟩
  exists w, ε'; split_ands; apply R; apply V.VRelMu_sub<;> assumption



lemma VRel.mu_incl :  B.Open → (∀ ε v, ρ ε v → ρ' ε v) → v ∈ V⟦B⟧⟨A, ρ⟩#ε → v ∈ V⟦B⟧⟨A, ρ'⟩#ε := by
  intro WF I V
  revert v
  induction B <;> intro v V
  case unit => simp at *; assumption
  case prod IH1 IH2 =>
    cases WF with | prod WF1 WF2
    simp at *
    rcases V with ⟨v1,p1,v2,p2,rfl,V1, V2⟩
    constructor;constructor;constructor;constructor;constructor;rfl
    constructor
    apply IH1 WF1 v1 p1 V1
    apply IH2 WF2 v2 p2 V2
  case sum IH1 IH2 =>
    cases WF with | sum WF1 WF2
    simp at *
    rcases V with ⟨v1,p1,rfl,V1⟩ | ⟨v1,p1,rfl,V1⟩
    . left; constructor;constructor;constructor;rfl
      apply IH1 WF1 v1 p1 V1
    . right; constructor;constructor;constructor;rfl
      apply IH2 WF2 v1 p1 V1
  case var =>
    simp at *
    rcases V with ⟨T,V⟩
    grind
  case arr =>
    rw[Typ.Wf.arr'] at WF
    solve_by_elim[VRel.type_closed]
  case delayA | delayE | chan | mu => simp at *; grind
  case sig IH =>
    cases WF with | sig WF
    simp at *
    rcases V with ⟨l,rfl,s,L,T,V⟩
    exists l;split_ands;rfl;
    exists s;split_ands;assumption;assumption
    apply IH WF
    apply V


lemma VRelMu.succ : A.Open → VRelMu i A ε v → VRelMu i.succ A ε v := by
  revert v ε
  induction i <;> intros ε v WF V
  case zero =>  try simp at *
  case succ i IH =>
    simp at V
    rcases V with ⟨w,W,rfl,V⟩
    apply VRel.mu_incl at V
    simp;constructor;constructor;constructor; rfl; assumption; assumption
    solve_by_elim


lemma VRelMu.up : i ≤ j → A.Open → VRelMu i A ε v → VRelMu j A ε v := by
  intros V WF L
  induction j
  case zero =>
    have E : i = 0 := by omega
    subst E
    simp at V
    assumption
  case succ j IH =>
    if i = j + 1
    then subst_eqs; assumption
    else
    have L' : i ≤ j := by omega
    clear L
    apply IH at L'
    solve_by_elim[VRelMu.succ]


lemma VRel.mu_up :  i ≤ j → B.Open → A.Open → (V : v ∈ V⟦B⟧⟨μ A,  VRelMu i A⟩#ε) → v ∈ V⟦B⟧⟨μ A, VRelMu j A⟩#ε := by
  intros L WF1 WF2 V
  apply VRel.mu_incl WF1
  . intros; apply VRelMu.up L WF2; assumption
  . assumption



-- TODO not used?
lemma VRel.mu_sub : A.Open → v ∈ V⟦μ A⟧ ε → ∃ (w : Val) , v = w.cons A /\ w ∈ V⟦A.sub (μ A)⟧ ε := by
  intros WF V
  simp at V
  rcases V with ⟨WFA, i , V⟩
  cases i <;> simp at V
  case succ i =>
    rcases V with ⟨v , p, rfl, V⟩
    exists ⟨v, p⟩
    split_ands; rfl
    apply VRel.VRelMu_sub
    assumption
    assumption
    assumption



lemma VRel.mu_rho : v ∈ V⟦μ A⟧ ρ # ε → v ∈ V⟦μ A⟧ ρ # ε := by
  intros V
  simp at *; assumption



lemma VRel.mu_rho0 : v ∈ V⟦μ A⟧ ρ # ε → v ∈ V⟦μ A⟧ ε := by
  intros V
  simp at *; assumption


lemma VRel.HasType_open : v ∈ V⟦A⟧ ρ # ε → ε ⊢ v ∷ A.sub ρ.1 := by
  intros V
  revert v ρ
  induction A <;> intros ρ v V
  case mu A IH =>
    simp at V
    rcases V with ⟨WF,i,V⟩
    cases i <;> simp at V
    case succ i =>
    rcases V with ⟨v', V', rfl, V⟩
    constructor
    apply IH at V; solve_by_elim; grind

  case var => simp at *; grind
  case unit => simp at V;subst V; constructor
  case prod A B IH1 IH2 =>
    simp at V
    rcases V with ⟨v1,p1,v2,p2, rfl, V1, V2⟩
    constructor; apply IH1 V1; apply IH2 V2
  case sum IH1 IH2 =>
    simp at V
    rcases V with ⟨v,p,rfl, V⟩ | ⟨v,p,rfl, V⟩ <;> constructor
    . apply IH1 V
    . apply IH2 V
  case arr =>
    simp at V
    cases V; assumption
  case delayA | delayE | chan => simp at V;assumption
  case sig =>
    simp at V
    rcases V with ⟨l, rfl, s, L, T, V⟩
    constructor
    rw[Heap.type_lookup]
    simp
    exists s

lemma VRel.sub_VRelMu : B.Open → A.Open → v ∈ V⟦B.sub (μ A)⟧ ε → ∃ i, v ∈ V⟦B⟧ ⟨μ A, VRelMu i A⟩ # ε := by
  intros WF WF' V
  revert v
  induction B <;> intros v V
  case var =>
    have T := VRel.HasType_open V
    simp at *;
    rcases V with ⟨i, V⟩
    grind
  case unit => simp at *; assumption
  case prod A1 A2 IH1 IH2 =>
    cases WF with | prod WF1 WF2
    simp at *;
    rcases V with ⟨v1, p1, v2, p2, rfl, V1 , V2⟩
    have U1 := IH1 WF1 v1 p1 V1
    have U2 := IH2 WF2 v2 p2 V2
    rcases U1 with ⟨i1,U1⟩
    rcases U2 with ⟨i2,U2⟩
    exists (max i1 i2),v1, p1,v2,p2
    split_ands
    . rfl
    . apply U1.mu_up;omega;assumption;assumption
    . apply U2.mu_up;omega;assumption;assumption
  case sum A1 A2 IH1 IH2 =>
    cases WF with | sum WF1 WF2
    simp at *;
    rcases V with ⟨v1, p1, rfl, V ⟩ | ⟨v1, p1, rfl, V ⟩
    . have U1 := IH1 WF1 v1 p1 V
      rcases U1 with ⟨i,U1⟩
      exists i
      left; exists v1, p1
    . have U1 := IH2 WF2 v1 p1 V
      rcases U1 with ⟨i,U1⟩
      exists i
      right; exists v1, p1
  case delayA | delayE | mu | chan => simp at *; assumption
  case arr =>
    rw[Typ.Wf.arr'] at WF
    exists 0
    apply VRel.type_closed; assumption
    rw[Typ.sub_closed] at V<;> assumption
  case sig IH =>
    cases WF with | sig WF
    simp at *
    rcases V with ⟨l,rfl,s,L,T,V⟩
    have U := IH WF s.head.val s.head.prop V
    rcases U with ⟨i,U⟩
    exists i, l;split_ands;rfl
    exists s


lemma VRel.sub_mu : A.Open → v ∈ V⟦A.sub (μ A)⟧ ε → cons A v ∈ V⟦μ A⟧ ε := by
  intros WF V
  apply VRel.sub_VRelMu at V <;> try assumption
  rcases V with ⟨i,V⟩
  simp
  split_ands; assumption
  exists i.succ; simp; grind



lemma VRel.HasType : v ∈ V⟦A⟧ ε → ε ⊢ v ∷ A := by
  intros V
  apply VRel.HasType_open at V
  simp at V
  assumption

lemma CRel.SubsType : γ ∈ C⟦Γ⟧ε → SubsType ε.now.type ε.chans γ Γ := by
  intros G
  induction G
  case nil => constructor
  case cons V G IH =>
    constructor
    . apply VRel.HasType V
    . apply IH


def WfSemSub (ρ : SemSub) := ∀ v ε ε', ε.Sub ε' → ρ.rel ε v → ρ.rel ε' v

@[simp,grind .]
lemma WfSemSub.empty : WfSemSub ρ0 := by
  simp[WfSemSub]
  intros
  contradiction

lemma VRel.Sub_open' : (∀ v, ρ.rel ε v → ρ.rel ε' v) → (V : v ∈ V⟦A⟧ ρ # ε) → ε.Sub ε' → v ∈ V⟦A⟧ ρ # ε' := by
  intros C V S
  revert v ρ
  induction A <;> intros ρ v C V <;> simp at *
  case var => grind
  case unit => assumption
  case prod IH1 IH2 =>
    rcases V with ⟨v1,p1,v2,p2, rfl, V1, V2⟩
    apply IH1 at V1 <;> try assumption
    apply IH2 at V2 <;> try assumption
    grind
  case sum IH1 IH2 =>
    rcases V with ⟨v,p,rfl, V⟩ | ⟨v,p,rfl, V⟩
    . apply IH1 at V<;>grind;
    . apply IH2 at V<;>grind
  case arr IH =>
    rcases V with ⟨T, t, E, V ⟩
    split_ands
    . apply T.Sub' S
    . exists t; split_ands
      . assumption
      . intros ε'' S' v p V'
        apply V ε'' (S.trans S') <;> try assumption
  case delayA | delayE | chan => apply V.Sub' S
  case sig IH =>
    rcases V with ⟨l, rfl, s, L, T, V⟩
    exists l; split_ands
    . rfl
    . exists s; split_ands
      . apply AList.Sub.lookup S.store.now L
      . assumption
      . solve_by_elim
  case mu A IH =>
    rcases V with ⟨WF,i, V⟩
    split_ands; assumption
    exists i
    revert v
    induction i <;> intros v V
    case zero => simp at *
    case succ IHi =>
      simp at *
      rcases V with ⟨w, p, rfl, V⟩
      exists w, p
      split_ands;rfl
      apply IH
      . intros; apply IHi; assumption
      . assumption


lemma VRelMu.Sub : ε.Sub ε' → VRelMu i A ε v → VRelMu i A ε' v := by
    intros S
    revert v
    induction i <;> intros v V
    case zero => simp at *
    case succ IHi =>
      simp at *
      rcases V with ⟨w, p, rfl, V⟩
      exists w, p
      split_ands;rfl
      apply V.Sub_open' <;> try assumption
      intros;simp at *
      apply IHi; assumption


@[simp,grind .]
lemma WfSemSub.mu : WfSemSub ⟨B, VRelMu i A⟩ := by
  simp[WfSemSub]
  intros
  solve_by_elim[VRelMu.Sub]


lemma VRel.Sub_open : WfSemSub ρ → v ∈ V⟦A⟧ ρ # ε → ε.Sub ε' → v ∈ V⟦A⟧ ρ # ε' := by
  simp[WfSemSub];intros W V S; apply VRel.Sub_open' <;> try assumption
  intros; apply W <;> assumption

------------------------
-- Lemma 5.7 (part 1) --
------------------------

lemma VRel.Sub' : v ∈ V⟦A⟧ ε → ε.Sub ε' → v ∈ V⟦A⟧ ε' := by
  intro V
  apply VRel.Sub_open <;> try assumption
  simp

------------------------
-- Lemma 5.7 (part 2) --
------------------------

lemma CRel.Sub' : γ ∈ C⟦Γ⟧ε → ε.Sub ε' → γ ∈ C⟦Γ⟧ε' := by
  intros G S
  induction G
  case nil => constructor
  case cons V G IH =>
    constructor
    . apply VRel.Sub' V S
    . apply IH ; assumption




lemma CRel.VRel {t : Term} {γ : List Term} {Γ : Ctx} {i : Nat} :
   γ ∈ C⟦Γ⟧ε → t ∈ γ[i]? → ∃ A : Typ, ∃  p , A ∈ Γ[i]? /\ ⟨ t, p ⟩ ∈ V⟦A⟧ε := by
  intros G L
  revert i
  induction G <;> intro i L
  case nil => simp at *
  case cons IH =>
    cases i
    case zero => simp at L;grind
    case succ => simp at *; apply IH L;

lemma CRel.VRel' {t : Term} {γ : List Term} {Γ : Ctx} {i : Nat}:
  γ ∈ C⟦Γ⟧ε → t ∈ γ[i]? → A ∈ Γ[i]? → ∃ p, ⟨ t, p ⟩ ∈ V⟦A⟧ε := by
  intros G L L'
  apply CRel.VRel G at L
  rcases L with ⟨ A, V, E, T ⟩
  rw [E] at L'
  cases L'
  constructor; assumption



lemma CRel.length : γ ∈ C⟦Γ⟧ε → γ.length = Γ.length := by
  intros G
  induction G <;> simp
  assumption



lemma HasType.subs_CRel : γ ∈ C⟦Γ⟧ε →
  ε ## Γ ⊢ t ∷ A → ε ⊢ t.subs γ 0 ∷  A := by
  intros G T
  apply CRel.SubsType at G
  apply HasType.subs_top <;> assumption




inductive HRel : Env → Heap → Prop where
| nil : HRel ε ∅
| cons :
  HRel ε ⟨ η , M ⟩ →
  hd ∈ V⟦A⟧ε →
  HRel ε ⟨ ⟨ l, ⟨ A , hd , cl , tl⟩ ⟩ :: η , N ⟩

lemma HRel.lookup_VRel : HRel ε η → s ∈ AList.lookup l η → s.head ∈ V⟦s.type⟧ε := by
  intros H L'
  simp[AList.lookup] at L'
  have L : s ∈ List.dlookup l η.entries := by apply L';
  rewrite [List.mem_dlookup_iff η.nodupKeys] at L
  clear L'
  induction H
  case nil => contradiction
  case cons η M A hd l θ tl N H V IH =>
    cases L
    case head => apply V
    case tail L =>
      apply IH; apply L


------------------------
-- Lemma 5.7 (part 3) --
------------------------

lemma HRel.Sub : HRel ε η → ε.Sub ε' → HRel ε' η := by
  intros H S
  revert ε'
  induction H <;> intros ε' S
  case nil => constructor
  case cons V IH =>
    constructor
    . apply IH; assumption
    . apply V.Sub' S

---------------------------------------------
-- lemmas for proving fundamental property --
---------------------------------------------


lemma VRel.lam {s : Val} {t : Term}: ε ⊢ s ∷ (A ↠ B ↠ C).sub ρ.type →
  s = Val.lam (Val.lam t) →
  WfSemSub ρ →
  (∀ v1 v2 p1 p2 ε', ε.Sub ε' → ⟨v1,p1⟩ ∈ V⟦A⟧ρ#ε' → ⟨v2,p2⟩ ∈ V⟦B⟧ρ#ε' → t.subs [v2,v1] 0 ∈ T⟦C⟧ ρ # ε')
  → s ∈ V⟦A ↠ B ↠ C⟧ρ # ε := by
  intros T E Cl P
  subst E
  simp;constructor;assumption
  exists t.lam;split_ands;rfl;
  intros ε' S t1 v1 V1
  apply TRel.VRel'
  constructor
  apply HasType.lam_inv at T
  simp;constructor;
  apply HasType.sub;
  apply V1.HasType_open
  simp[Val.lam] at *;
  apply HasType.Sub'<;> assumption
  exists t.subs [t1] 1;constructor;simp[Val.lam,Term.sub]
  intros ε'' S' t2 v2 V2
  unfold Term.sub
  rw[Term.subs_subs]
  apply P;trans;assumption;assumption
  apply VRel.Sub_open at V1
  apply V1; assumption
  intros w W
  apply Cl;assumption
  constructor;
  apply V1.HasType_open
  constructor
  constructor

def TRel' (A : Typ) (ρ : SemSub)  (ε : Env) (t : Term) : Prop := ∀ {ε'}, ε.Sub ε' → t ∈ T⟦A⟧ ρ # ε'

notation : 80 v : 90 " ∈ " "T'⟦" A : 90 "⟧" ρ : 90 "#" ε : 90 => TRel' A ρ ε v
notation : 80 v : 90 " ∈ " "T'⟦" A : 90 "⟧" ε : 90 => TRel' A ρ0 ε v

lemma TRel'.Sub : v ∈ T'⟦A⟧ ρ # ε → ε.Sub ε' → v ∈ T'⟦A⟧ ρ # ε' := by
  intros V S ε'' S'
  apply V; trans<;> assumption

lemma TRel'.VRel  :  WfSemSub ρ → ⟨t, p⟩  ∈ V⟦A⟧ρ#ε → t ∈ T'⟦A⟧ρ#ε := by
  intro WS V ε' S
  apply TRel.VRel
  apply V.Sub_open WS S

lemma TRel.fromTRel'  :  t ∈ T'⟦A⟧ρ#ε → t ∈ T⟦A⟧ρ#ε := by
  intro T; apply T; rfl

lemma TRel.app : s ∈ T'⟦A ↠ B⟧ ρ # ε → t ∈ T'⟦A⟧ ρ # ε → s.app  t ∈ T'⟦B⟧ ρ # ε := by
    intros IH1 IH2 ε1 S
    unfold TRel' TRel at IH1
    have U1 := IH1 S
    rcases U1 with ⟨ v, ε2 , R1 , U1 ⟩
    simp at U1
    rcases U1 with ⟨ U1 , s' , rfl , V1  ⟩
    have S1 := Eval.incr R1
    unfold TRel' TRel at IH2
    have U2 := IH2 (by trans<;> assumption)
    rcases U2 with ⟨ w, ε3 , R2 , U2 ⟩
    have S3 := Eval.incr R2
    have U3 := V1 ε3 S3 w.1 w.2 U2
    unfold TRel at U3
    rcases U3 with ⟨ w, ε4 , R3 , U3 ⟩
    unfold TRel
    exists w, ε4; constructor
    . constructor; apply R1; apply R2; apply R3
    . assumption

lemma TRel.pair : WfSemSub ρ → s ∈ T'⟦A⟧ ρ # ε → t ∈ T'⟦B⟧ ρ # ε → s.pair t ∈ T'⟦A ⊗ B⟧ ρ # ε := by
  intros WS IH1 IH2 ε1 S
  have U1 := IH1 S
  unfold TRel' TRel at U1
  rcases U1 with ⟨ v1, ε2 , R1 , U1 ⟩
  have S1 := Eval.incr R1
  have U2 := IH2 (S.trans S1)
  unfold TRel' TRel at U2
  rcases U2 with ⟨ v2, ε3 , R2 , U2 ⟩
  have S3 := Eval.incr R2
  unfold TRel
  exists Val.pair v1 v2, ε3; constructor
  . constructor; apply R1; apply R2
  . simp; exists v1, v1.2, v2, v2.2; split_ands
    . rfl
    . apply U1.Sub_open WS S3
    . apply U2


lemma TRel.in1 : t ∈ T'⟦A⟧ ρ # ε → t.in1 ∈ T'⟦A ⊕ B⟧ ρ # ε := by
  intros IH ε1 S
  have U := IH S
  unfold TRel at U
  rcases U with ⟨ v, ε2 , R , U ⟩
  unfold TRel
  exists Val.in1 v, ε2; constructor
  . constructor; apply R
  . simp; left; exists v, v.property


lemma TRel.in2 : t ∈ T'⟦B⟧ ρ # ε → t.in2 ∈ T'⟦A ⊕ B⟧ ρ # ε := by
  intros IH ε1 S
  have U := IH S
  unfold TRel at U
  rcases U with ⟨ v, ε2 , R , U ⟩
  unfold TRel
  exists Val.in2 v, ε2; constructor
  . constructor; apply R
  . simp; right; exists v, v.property


lemma TRel.pr1 : t ∈ T'⟦A ⊗ B⟧ ρ # ε → t.pr1 ∈ T'⟦A⟧ ρ # ε := by
  intros IH ε1 S
  have U := IH S
  unfold TRel at U
  rcases U with ⟨ v, ε2 , R , U ⟩
  simp at U
  rcases U with ⟨t1,V1,t2,V2, rfl, U1 , U2⟩
  unfold TRel
  exists ⟨t1, V1⟩, ε2; constructor
  . constructor; apply R
  . apply U1

lemma TRel.pr2 : t ∈ T'⟦A ⊗ B⟧ ρ # ε → t.pr2 ∈ T'⟦B⟧ ρ # ε := by
  intros IH ε1 S
  have U := IH S
  unfold TRel at U
  rcases U with ⟨ v, ε2 , R , U ⟩
  simp at U
  rcases U with ⟨t1,V1,t2,V2, rfl, U1 , U2⟩
  unfold TRel
  exists ⟨t2, V2⟩, ε2; constructor
  . constructor; apply R
  . apply U2


lemma TRel.case {t : Term}:
  t ∈ T'⟦A1 ⊕ A2⟧ρ # ε →
  (∀ {v ε'}, ε.Sub ε' → v ∈ V⟦A1⟧ρ # ε' → t1.sub v ∈ T⟦B⟧ρ # ε') →
  (∀ {v ε'}, ε.Sub ε' → v ∈ V⟦A2⟧ρ # ε' → t2.sub v ∈ T⟦B⟧ρ # ε') →
  Term.case t t1 t2 ∈ T'⟦B⟧ρ # ε := by
  intros IH IH1 IH2 ε1 S
  have U := IH S
  unfold TRel at U
  rcases U with ⟨ v, ε2 , R , U ⟩
  have S' := R.incr
  simp at U
  rcases U with ⟨ v , p , rfl , U ⟩ |  ⟨ v , p , rfl , U ⟩
  .
    have U1 := IH1 (S.trans S') U
    unfold TRel' TRel at U1
    rcases U1 with ⟨ v, ε3 , R1 , U1 ⟩
    unfold TRel; exists v, ε3; split_ands
    . apply Eval.case1; apply R;
      simp[Term.sub]
      apply R1
    . assumption
  .
    have U2 := IH2 (S.trans S') U
    unfold TRel' TRel at U2
    rcases U2 with ⟨ v, ε3 , R2 , U2 ⟩
    unfold TRel; exists v, ε3; split_ands
    . apply Eval.case2; apply R;
      simp[Term.sub]
      apply R2
    . assumption

lemma VRel.sub : ⟨v,p⟩ ∈ V⟦A⟧ ρ # ε → v.subs s n = v := by
  intro V
  apply VRel.HasType_open at V
  apply HasType.closed V



lemma TRel.fix' :
    ε ⊢ s ∷ A.sub ρ.type →
    s = fix t →
    (∀ v p ε', ε.Sub ε' → ⟨v,p⟩ ∈ V⟦□ A⟧ρ#ε' → t.sub v ∈ T⟦A⟧ ρ # ε') →
    fix t ∈ T'⟦A⟧ρ # ε := by

  unfold TRel'
  intros T E P ε1 S
  subst E
  cases T with | fix T
  let v : Val := delay t.fix
  have V : v ∈ V⟦□ A⟧ ρ # ε1 := by
      simp[v]; constructor; constructor
      apply T.Sub' S
  have U := P v.val v.prop ε1 S  V
  simp[TRel] at U
  rcases U with ⟨ u , q , ε2, R, U ⟩
  unfold TRel
  exists ⟨u,q⟩, ε2;split_ands
  . unfold v at *; constructor; simp[Term.sub]
    apply R
  . assumption


lemma TRel.fix :
    ε ⊢ s ∷ A.sub ρ.type →
    s = fix t →
    (∀ v p , ⟨v,p⟩ ∈ V⟦□ A⟧ρ#ε → t.sub v ∈ T⟦A⟧ ρ # ε) →
    s ∈ T⟦A⟧ρ # ε := by

  intros T E P
  subst E
  cases T with | fix T
  let v : Val := delay t.fix
  have V : v ∈ V⟦□ A⟧ ρ # ε := by
      simp[v]; constructor; constructor
      apply T
  have U := P v.val v.prop  V
  simp[TRel] at U
  rcases U with ⟨ u , q , ε2, R, U ⟩
  unfold TRel
  exists ⟨u,q⟩, ε2;split_ands
  . unfold v at *; constructor; simp[Term.sub]
    apply R
  . assumption

lemma TRel.sig : WfSemSub ρ → t ∈ T'⟦A⟧ρ#ε → t' ∈ T'⟦◯ A.sig⟧ρ#ε →  Term.sig (A.sub ρ.type) t t' ∈ T'⟦A.sig⟧ρ#ε := by
  unfold TRel'
  intros WS IH1 IH2
  intro ε1 S
  have U1 := IH1 S
  unfold TRel at U1
  rcases U1 with ⟨ v, ε2 , R1 , U1 ⟩
  have S1 := Eval.incr R1
  have U2 := (S.trans S1)
  apply IH2 at U2
  unfold TRel at U2
  rcases U2 with ⟨ w, ε3 , R2 , U2 ⟩
  simp at U2
  unfold TRel
  rcases ε3 with ⟨σ , δ⟩
  let s : Sig := ⟨ A.sub ρ.type , v , false, w ⟩
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
      . unfold s; simp; apply VRel.Sub_open WS; apply U1
        apply S3.trans; constructor<;> simp[ε4]



lemma TRel.head : t ∈ T'⟦A.sig⟧ρ#ε → t.head ∈ T'⟦A⟧ρ#ε := by
  intros IH ε1 S
  have U := IH S
  unfold TRel at U
  rcases U with ⟨ v, ε2 , R , U ⟩
  simp at U
  rcases U with ⟨ l , rfl , s , L , E , U ⟩
  unfold TRel
  exists s.head, ε2; split_ands
  . constructor; apply R; apply L
  . apply U

lemma TRel.appE : t ∈ T'⟦□ (A ↠ B)⟧ρ#ε → t' ∈ T'⟦◯ A⟧ρ#ε → t.appE t' ∈ T'⟦◯ B⟧ρ#ε := by
  intros IH1 IH2 ε1 S
  have U1 := IH1 S
  unfold TRel at U1
  rcases U1 with ⟨ v, ε2 , R1 , U1 ⟩
  simp at U1
  have S1 := Eval.incr R1
  have U2 := IH2 (S.trans S1)
  unfold TRel at U2
  rcases U2 with ⟨ w, ε3 , R2 , U2 ⟩
  simp at U2
  have S3 := Eval.incr R2
  have U1' := U1.Sub' S3
  unfold TRel
  exists (v.appE w), ε3; constructor
  . constructor<;> assumption
  . simp; constructor; apply U1'; apply U2


lemma VRel.appE :  WfSemSub ρ → ⟨v,p⟩ ∈ V⟦□ (A ↠ B)⟧ρ#ε → ⟨w,q⟩ ∈ V⟦◯ A⟧ρ#ε → ⟨v.appE w, r⟩ ∈ V⟦◯ B⟧ρ#ε := by
  intros WS IH1 IH2
  apply TRel'.VRel WS at IH1
  apply TRel'.VRel WS at IH2
  apply TRel.appE IH1 at IH2
  apply TRel.fromTRel' at IH2
  apply VRel.IsValue_TRel IH2



lemma TRel.tail {A : Typ} : t ∈ T'⟦A.sig⟧ρ#ε → t.tail ∈ T'⟦◯ A.sig⟧ρ#ε := by
  intros IH ε1 S
  have U := IH S
  unfold TRel at U
  rcases U with ⟨ v, ε2 , R , U ⟩
  simp at U
  rcases U with ⟨l, rfl, s, L, Q, U⟩
  unfold TRel
  exists Val.tail (.loc l), ε2; constructor
  . constructor; apply R
  . simp; constructor; constructor
    rw[Heap.type_lookup]; simp
    exists s

lemma VRel.tail {A : Typ} : WfSemSub ρ → ⟨v,p⟩ ∈ V⟦A.sig⟧ρ#ε → ⟨v.tail, q⟩ ∈ V⟦◯ A.sig⟧ρ#ε := by
  intros WS IH
  apply TRel'.VRel WS at IH
  apply TRel.tail at IH
  apply TRel.fromTRel' at IH
  apply VRel.IsValue_TRel IH

lemma VRel.smap : WfSemSub ρ → B.sub ρ.type = B' → Val.smap B' ∈ V⟦(A ↠ B) ↠ A.sig ↠ B.sig⟧ ρ #ε := by
  intros WS E
  subst E

  have Tmap : ε ⊢ Term.smap (B.sub ρ.type) ∷ ((A ↠ B) ↠ A.sig ↠ B.sig).sub ρ.type := by apply HasType.smap
  unfold Term.smap at Tmap
  cases Tmap with | lam Tmap
  unfold VRel
  split_ands
  . apply HasType.smap
  . constructor;split_ands
    . simp[Val.smap,Term.smap];rfl
    . intros ε1 S1 v V
      have T := V.HasType_open
      have Tlam := Tmap.Sub' S1
      apply HasType.sub T at Tlam
      simp[Term.sub] at Tlam;
      simp[Term.sub]; apply TRel.fix
      . apply Tlam
      . rfl
      . intros w' q W; apply TRel.VRel <;> try constructor
        unfold VRel; split_ands
        . cases Tlam with | fix Tlam
          apply HasType.sub W.HasType_open at Tlam
          apply Tlam
        . constructor;split_ands
          . rfl
          . intros ε2 S2 u U
            simp[Term.sub]
            apply TRel.fromTRel'
            repeat rw[HasType.closed T]
            rw[HasType.closed W.HasType_open]
            apply TRel.sig WS
            . apply TRel.app
              . have V' := (V.Sub_open WS S2)
                apply TRel'.VRel WS; assumption
              . apply TRel.head; apply TRel'.VRel WS; apply U
            . apply TRel'.VRel WS; apply VRel.appE WS; apply W.Sub_open WS S2
              apply VRel.tail WS; assumption;constructor; grind
              repeat constructor;grind;




lemma VRel.fmap : A.Open → Val.fmap A (μ A' ⊗ B.sub (μ A')) ∈ V⟦(var ↠ var ⊗ B) ↠ A ↠ A.sub (var ⊗ B)⟧ ⟨μ A', VRelMu i A'⟩  #ε := by
  intro WF
  have WS : WfSemSub { type := μ A', rel := VRelMu i A' } := by simp
  apply VRel.lam
  . simp; apply HasType.fmap; assumption
  . unfold Val.fmap Term.fmap; rfl
  . intro v ε ε' S V; apply V.Sub S
  . intros t1 t2 p1 p2 ε' S V1 V2
    cases A
    case a.unit | a.mu =>
      simp; apply TRel.VRel; assumption
    case a.prod A1 A2 =>
      cases WF with | prod WF1 WF2
      simp; repeat rw[Term.fmap_subs (by assumption)]
      apply TRel.fromTRel'
      apply TRel.pair WS
      . apply TRel.app; apply TRel.app; apply TRel'.VRel WS; apply VRel.fmap WF1
        apply TRel'.VRel WS at V1; apply V1; apply TRel.pr1; apply TRel'.VRel WS at V2; apply V2
      . apply TRel.app; apply TRel.app; apply TRel'.VRel WS; apply VRel.fmap WF2
        apply TRel'.VRel WS at V1; apply V1; apply TRel.pr2; apply TRel'.VRel WS at V2; apply V2
    case a.sum A1 A2 =>
      cases WF with | sum WF1 WF2
      simp; rw[Term.fmap_subs WF1,Term.fmap_subs WF2]
      apply TRel.fromTRel'
      apply TRel.case
      . apply TRel'.VRel WS at V2; apply V2
      . intros v ε2 S' V; simp[Term.sub]; rw[Term.fmap_subs WF1];apply TRel.in1; apply TRel.app
        apply TRel.app; apply TRel'.VRel WS; apply VRel.fmap WF1;assumption
        rw[ VRel.sub V1]; apply TRel'.VRel WS; apply VRel.Sub_open
        simp
        apply V1; assumption;apply TRel'.VRel WS at V; apply V; rfl
      . intros v ε2 S' V; simp[Term.sub];rw[Term.fmap_subs WF2]; apply TRel.in2; apply TRel.app
        apply TRel.app; apply TRel'.VRel WS; apply VRel.fmap WF2; assumption
        rw[ VRel.sub V1]; apply TRel'.VRel WS; apply VRel.Sub_open;
        simp
        apply V1; assumption;apply TRel'.VRel WS at V; apply V; rfl
    case a.arr =>
      cases WF with | arr WF1 WF2
      simp; apply TRel.VRel; rewrite[Typ.sub_closed WF1,Typ.sub_closed WF2]; assumption
    case a.chan =>
      cases WF with | chan WF
      simp; apply TRel.VRel; rewrite[Typ.sub_closed WF]; assumption
    case a.delayE =>
      cases WF with | delayE WF
      simp; apply TRel.VRel; rewrite[Typ.sub_closed WF]; assumption
    case a.delayA =>
      cases WF with | delayA WF
      simp; apply TRel.VRel; rewrite[Typ.sub_closed WF]; assumption
    case a.var =>
      simp
      apply TRel.app; apply TRel'.VRel WS; apply V1; apply TRel'.VRel WS; apply V2; rfl
    case a.sig A'' =>
      cases WF with | sig WF
      simp; rw[Term.fmap_subs WF]
      apply TRel.fromTRel'
      apply TRel.app
      . apply TRel.app;
        . apply TRel'.VRel; apply WS; apply VRel.smap (B' := A''.sub (μ A' ⊗ B.sub (μ A'))) (B:=A''.sub (Typ.var ⊗ B)) WS
          simp; assumption
        . apply TRel.app; apply TRel'.VRel WS; apply VRel.fmap WF; apply TRel'.VRel WS; assumption
      . apply TRel'.VRel WS; assumption
open Term

lemma VRelMu.isCons : VRelMu i A ε v → exists w, v = Val.cons A w := by
  intros V
  cases i <;> simp at V
  rcases V with ⟨w,p,rfl,V⟩
  exists ⟨w,p⟩

lemma TRel.recur_val {s t : Term} : (t, ε1)⇓(v, ε2) → VRelMu i A ε2 v → s.recur B v ∈ T⟦B⟧ε2 → s.recur B t ∈ T⟦B⟧ε1 := by
  unfold TRel
  intro R1 Vv Vr
  rcases Vr with ⟨w, ε3, R2, Vw⟩
  cases R2
  case value IV => contradiction
  case recur u _ _ _ R2 R3 R4 =>
    have R3' := Eval.value (ε:=ε2) (v.prop)
    apply R3.determ at R3'
    apply VRelMu.isCons at Vv
    rcases Vv with ⟨v',rfl⟩
    rcases u with ⟨u, IVu⟩
    injections R3
    subst_eqs
    constructor;constructor;split_ands
    . apply Eval.recur <;> assumption
    . assumption


lemma TRel.recur {s t : Term}:
    A.Open →
    B.Closed →
    ε ## [A.sub (μ A ⊗ B)] ⊢ s ∷ B →
    t ∈ T'⟦var⟧⟨μ A, VRelMu i A⟩ # ε →
    (∀ {v ε' i}, ε.Sub ε' → v ∈ V⟦A.sub (var ⊗ B)⟧⟨μ A, VRelMu i A⟩ # ε' → s.sub v ∈ T⟦B⟧⟨μ A, VRelMu i A⟩ # ε') →
    Term.recur B s t ∈ T'⟦B⟧⟨μ A, VRelMu i A⟩ # ε := by
  intros WFA WFB Ts IH1 IH2
  intros ε1 S0
  have U := IH1 S0
  unfold TRel' TRel at U
  rcases U with ⟨ v, ε2 , R1 , U ⟩
  have S1 := R1.incr
  simp at U
  rcases U with ⟨T, U⟩
  cases i <;> simp at U
  case succ i =>
    have WS : WfSemSub { type := μ A, rel := VRelMu i A } := by simp
    rcases U with ⟨w,p,rfl,U⟩
    have V : ((Term.fmap A (μ A ⊗ B.sub (μ A))).app (Term.lam (Term.pair (var 0) (Term.recur B s (var 0))))).app w ∈ T⟦A.sub (var ⊗ B)⟧⟨μ A, VRelMu i A⟩ # ε2 := by
      apply TRel.fromTRel'; apply TRel.app; apply TRel.app
      apply TRel'.VRel WS; apply VRel.fmap WFA; apply TRel'.VRel WS; simp
      split_ands
      . constructor; constructor;constructor;simp; rw[Typ.sub_closed WFB]
        constructor; constructor; assumption; assumption
        apply HasType.weaken (Γ':=[μ A]) at Ts
        simp at Ts
        apply Ts.Sub' (S0.trans S1)
        constructor;simp
      . constructor;split_ands; rfl; intros ε3 S2 a q Ta Va
        simp[Term.sub]; apply TRel.fromTRel'
        apply TRel.pair WS; apply TRel'.VRel WS; simp
        split_ands<;> assumption
        rw[HasType.closed' Ts]; try omega
        have S3 := (S0.trans (S1.trans S2))
        apply TRel.recur WFA WFB (Ts.Sub' S3)
        apply TRel'.VRel WS; simp;split_ands; assumption; assumption
        intros vv ε4 i S4 V; apply IH2 (S3.trans S4) V
        simp
      . apply TRel'.VRel WS; assumption

    unfold TRel at V
    rcases V with ⟨ u, ε3 , R2 , V ⟩
    have S2 := R2.incr
    have W := IH2 (S0.trans (S1.trans S2)) V
    unfold TRel at W
    rcases W with ⟨ r, ε4 , R3 , W ⟩
    unfold TRel
    rw[Typ.sub_closed WFB] at R2
    exists r, ε4;split_ands
    constructor<;> assumption
    apply W.type_closed WFB
