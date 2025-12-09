import Rizzo.Typing


@[simp]
def Term.subs (t : Term) (s : Subs) (m : Nat) : Term  :=
  match t with
  | unit => unit
  | pair t1 t2 => pair (t1.subs s m) (t2.subs s m)
  | in1 t' => in1 (t'.subs s m)
  | in2 t' => in2 (t'.subs s m)
  | lam u => lam (u.subs s (m + 1))
  | app t1 t2 => app (t1.subs s m) (t2.subs s m)
  | case t1 t2 t3 => case (t1.subs s m) (t2.subs s (m + 1)) (t3.subs s (m + 1))
  | pr1 t' => pr1 (t'.subs s m)
  | pr2 t' => pr2 (t'.subs s m)
  | delay t' => delay (t'.subs s m)
  | never => never
  | wait t' => wait (t'.subs s m)
  | trig t' => trig (t'.subs s m)
  | newchan A => newchan A
  | chan κ => chan κ
  | sync t1 t2 => sync (t1.subs s m) (t2.subs s m)
  | appE t1 t2 => appE (t1.subs s m) (t2.subs s m)
  | appA t1 t2 => appA (t1.subs s m) (t2.subs s m)
  | head t' => head (t'.subs s m)
  | tail t' => tail (t'.subs s m)
  | sig A t1 t2 => sig A (t1.subs s m) (t2.subs s m)
  | cons A t' => cons A (t'.subs s m)
  | recur B t1 t2 => recur B (t1.subs s (m + 1)) (t2.subs s m)
  | var x => if LT : x < m then (.var x) else if LT' : x - m < s.length then s.get ⟨ x - m , by omega ⟩ else .var x
  | loc l => loc l
  | fix u => fix (u.subs s (m + 1))


def Term.sub (t : Term) (s : Term) : Term  :=
  t.subs [s] 0



-----------------------------
-- Typing of substitutions --
-----------------------------

inductive SubsType (H : HeapTy) (δ : ChanCtx) : Subs → Ctx → Prop where
| nil : SubsType H δ [] []
| cons : H # δ ⊢ t ∷ A → SubsType H δ γ Γ → SubsType H δ (t :: γ) (A :: Γ)

notation : 80 (name := subs_type_notation) " ⊢C " γ : 90 " ∷ " Γ : 90 => SubsType γ Γ



--------------------------------
-- Lemmas about substitutions --
--------------------------------

lemma Subs.empty {t : Term} : t.subs [] i = t := by
  revert i
  induction t <;> intro i <;> try simp <;> try grind


lemma HasType.closed' :  H # δ # Γ ⊢ t ∷ A → i ≥ Γ.length → t.subs γ i = t := by
  intros T; revert γ; revert i
  induction T <;> intro i γ L <;> simp <;> grind



lemma HasType.closed :  H # δ ⊢ t ∷ A → t.subs γ i = t := by
  intros T
  apply HasType.closed' T; grind


@[simp]
lemma Term.fmap_subs : A.Open → (Term.fmap A C).subs s n = Term.fmap A C := by
  intros;
  rw[HasType.closed (H:=∅) (δ :=∅)]
  apply HasType.fmap <;> assumption

@[simp]
lemma Term.smap_subs : (Term.smap B).subs s n = Term.smap B := by
  rw[HasType.closed (H:=∅) (δ :=∅)]
  apply HasType.smap ; assumption

------------------------------------------
-- Lemmas about typing of substitutions --
------------------------------------------


lemma SubsType.HasType {t : Term} {γ : List Term} {Γ : Ctx} {i : Nat}   :
  SubsType H δ γ Γ → t ∈ γ[i]? → ∃ A : Typ , A ∈ Γ[i]? /\ H # δ ⊢ t ∷ A := by
  intros G L
  revert i
  induction G <;> intro i L
  case nil => simp at *
  case cons IH =>
    cases i
    case zero => simp at L;grind
    case succ => simp at *; apply IH L;

lemma SubsType.HasType' {t : Term} {γ : List Term} {Γ : Ctx} {i : Nat} :
  SubsType H δ γ Γ → t ∈ γ[i]? → A ∈ Γ[i]? →  H # δ ⊢ t ∷ A := by
  intros G L L'
  apply SubsType.HasType G at L
  rcases L with ⟨A, E, T⟩
  rw [E] at L'
  cases L'
  assumption


lemma SubsType.length : SubsType H δ γ Γ → γ.length = Γ.length := by
  intros G
  induction G <;> simp
  assumption




lemma SubsType.closed' {t : Term} {γ' γ : List Term} {i : Nat} :
  SubsType H δ γ Γ → γ[i]? = some t → t.subs γ' j = t := by
  intros T G
  have S := SubsType.HasType T G
  rcases S with ⟨A, T1, T2⟩
  apply HasType.closed<;> assumption





lemma SubsType.closed {γ' γ : List Term} {i : Nat}
  {p : i < γ.length} :  SubsType H δ γ Γ → γ[i].subs γ' j = γ[i] := by
    intros T
    apply SubsType.closed'; assumption
    rw[getElem?_pos]


/-
Lemma for combining two substitutions
-/

lemma Term.subs_subs {t : Term} : SubsType H δ γ Γ → (t.subs γ i.succ).subs [s] i = t.subs (s::γ) i := by
  intros T
  revert i
  induction t <;> intro i <;> simp <;> try grind
  case var x =>
    split; split; simp; intros; grind;
    simp;split; split; grind;rfl; split; split
    have E : x - i = 0 := by grind
    suffices H : some s = (s :: γ)[x - i]? by rw[getElem?_pos] at H; injection H;grind
    rw [E]; simp
    grind
    split; grind
    rfl
    split; split; omega; split;
    rw [SubsType.closed]; rw[<- List.getElem_cons_succ]
    congr; omega;grind; assumption
    grind
    split;grind
    split; simp
    split;grind;split;grind;grind;simp;intros;grind


---------------------------------------------------
-- Typing judgement is closed under substitution --
---------------------------------------------------





lemma HasType.subs  :
  SubsType H δ γ Γ' →
  (T : H # δ # Γ ++ Γ' ⊢ t ∷ A) → H # δ # Γ ⊢ t.subs γ Γ.length ∷  A  := by
  intros G T
  revert A Γ
  induction t <;> intros Γ A T <;> simp <;> try {cases T; constructor <;> grind}
  case app IH1 IH2 | appE IH1 IH2  | appA IH1 IH2 =>
    cases T; constructor; apply IH1; assumption; apply IH2;assumption
  case recur IH1 IH2 =>
    cases T; constructor; assumption; assumption; apply IH1; assumption; apply IH2;assumption
  case pr1 IH1 | pr2 IH1 => cases T; constructor; apply IH1; assumption
  case case IH1 IH2 IH3 => cases T; constructor; apply IH1; assumption; apply IH2; assumption;apply IH3; assumption
  case var =>
    cases T with | var T
    split
    . constructor; apply List.isElem?_cons <;> assumption
    . split
      . apply HasType.weaken_closed; apply SubsType.HasType' G; rw[getElem?_pos];rfl;apply List.isElem?_cons' <;> assumption
      . constructor; apply SubsType.length at G; grind


lemma HasType.sub  :
  H # δ ⊢ s ∷ B →
  H # δ # [B] ⊢ t ∷ A → H # δ ⊢ t.sub s ∷ A  := by
    intros T1 T2
    apply T2.subs
    solve_by_elim

lemma HasType.subs_top  :
  SubsType H δ γ Γ →
  H # δ # Γ ⊢ t ∷ A → H # δ ⊢ t.subs γ 0 ∷  A  := by
    intros G T
    apply HasType.subs ; assumption; simp; assumption
