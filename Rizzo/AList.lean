/-
Additional definitions and lemmas for Mathlib's association list type `AList`
-/
import Init.Data.List.Perm
import Mathlib.Data.List.Lattice
import Mathlib.Data.List.AList

notation "⟪ " l ", " p " ⟫" => AList.mk l p

abbrev AList' α β := AList (fun _ : α => β)


def AList.Sub (xs ys : AList β) : Prop := xs.entries.Sublist ys.entries

@[refl,simp]
def AList.refl (xs : AList β) : xs.Sub xs := by simp [AList.Sub]


def AList.refl' (xs : AList β) : xs = xs' → xs.Sub xs' := by
  intros; subst_eqs;rfl

@[simp]
def AList.Sub_empty (xs : AList β) : AList.Sub ∅ xs := by simp [AList.Sub]



lemma AList.length_nonempty {xs : AList β} :   xs.entries.length > 0 → xs ≠ ∅ := by
  intros L
  cases xs with | mk xs D
  cases xs
  . cases L
  . intro L; cases L

def AList.Sub.trans {l l' l'' : (AList β)} : l.Sub l' → l'.Sub l'' → l.Sub l'' := by
    intros S T
    simp [AList.Sub] at *
    apply S.trans T

instance : IsTrans (AList β) AList.Sub where
  trans := by
    intros xs ys zs S T; apply S.trans T


instance : Trans (α := AList β) AList.Sub AList.Sub AList.Sub where
  trans := by
    intros xs ys zs S T
    simp [AList.Sub] at *
    apply S.trans T


def AList.cons {α} [DecidableEq α] {β : α → Type} (k : α) (v : β k) (l : AList β) (p : k ∉ l) : AList β :=
  ⟨ ⟨ k, v ⟩ :: l.entries , l.nodupKeys.cons p ⟩

@[simp]
lemma AList.Sub.cons {α} [DecidableEq α] {β : α → Type}  (k : α) (v : β k)  (l : AList β) (p : k ∉ l)
  : l.Sub (l.cons k v p) := by
  simp[AList.Sub]; apply List.Sublist.cons; rfl



@[simp]
lemma AList.Sub.cons_both {α} [DecidableEq α] {β : α → Type}  {k : α} {v : β k}  {xs ys : AList β} {p : k ∉ xs} {p' : k ∉ ys}
  : xs.Sub ys → (xs.cons k v p).Sub (ys.cons k v p') := by
  intros S
  simp[AList.Sub]; apply List.Sublist.cons₂;
  assumption

def AList.alloc {β : Nat → Type } (η : AList β) : Nat := (η.keys.max?.getD 0).succ


def AList.greater_fresh {β : Nat → Type } (η : AList β) : (∀ x ∈ η, l > x) → l ∉ η := by
  intros F M
  apply F at M
  omega



def AList.alloc_greater {β : Nat → Type } (η : AList β) : k ∈ η →  (η.alloc > k) := by
  intro M
  simp [AList.alloc]
  have M' : k ∈ η.keys := by assumption
  apply List.le_max?_getD_of_mem (k := 0) at M'
  grind


def AList.alloc_fresh' {β : Nat → Type } (η : AList β) : k ≥ η.alloc → k ∉ η := by
  intros L M
  apply η.alloc_greater at M
  generalize η.alloc = m at *
  grind

@[simp]
def AList.alloc_fresh {β : Nat → Type } (η : AList β) : η.alloc ∉ η := by
  apply η.alloc_fresh'
  grind

def List.entryMap (f: β → β') (l : List (Sigma (fun _ : α => β))) : List (Sigma (fun _ : α => β')) :=
  l.map (fun ⟨x,y⟩ => ⟨ x , f y⟩ )

@[simp]
lemma List.entryMap_keys (l : List (Sigma (fun _ : α => β))) (f : β → β') :
  (l.entryMap f).keys = l.keys := by
  cases l
  case nil => simp[entryMap]
  case cons => simp[entryMap]; apply List.entryMap_keys

@[simp]
lemma List.entryMap_NodupKeys (l : List (Sigma (fun _ : α => β))) (f : β → β')
  : l.NodupKeys → (l.entryMap f).NodupKeys := by
  simp[NodupKeys]

lemma List.dlookup_entryMap {α β γ} {f : β → γ} {xs : List (Sigma (fun _ : α => β))} [DecidableEq α] {l : α}:
   List.dlookup l (List.entryMap f xs) = Option.map f (List.dlookup l xs) := by
    cases xs
    . simp [List.entryMap]
    . simp [List.entryMap,dlookup]
      split
      . simp
      . apply dlookup_entryMap

lemma List.isElem?_cons {xs ys : List α}: x ∈ (xs ++ ys)[i]? → i < length xs → x ∈ xs[i]? := by
  intros E L
  revert i
  induction xs <;> intro i E L <;> simp at *
  case cons IH =>
    cases i <;> simp at *
    . assumption
    . apply IH <;> assumption

lemma List.isElem?_cons' {xs ys : List α}: x ∈ (xs ++ ys)[i]? → ¬ i < length xs → x ∈ ys[i-length xs]? := by
  intros E L
  revert i
  induction xs <;> intro i E L <;> simp at *
  case cons IH =>
    cases i <;> simp at *
    . apply IH <;> assumption
  case nil => assumption

def AList.concat {α} [DecidableEq α] {β : α → Type} (l : AList β) (k : α) (v : β k)
     (p : k ∉ l) : AList β :=
  ⟨ l.entries.concat ⟨ k, v ⟩ , by
    simp[List.NodupKeys,List.keys]
    rw[List.nodup_append]
    split_ands <;> try simp
    apply l.nodupKeys
    intros x y E Q
    subst_eqs
    apply p
    simp[AList.mem_keys,AList.keys.eq_1]
    apply List.mem_keys_of_mem at E
    simp at E
    assumption
   ⟩


def AList.append {α} [DecidableEq α] {β : α → Type}
  (xs ys : AList β) (D : xs.Disjoint ys) : AList β :=
  ⟨ xs.entries ++ ys.entries, by
  simp[List.NodupKeys,List.keys]
  apply List.Nodup.append xs.nodupKeys ys.nodupKeys
  apply D
  ⟩


lemma AList.concat_append  {α} [DecidableEq α] {β : α → Type} {l : α} {s : β l}  {xs ys : AList β}
    {p' : l ∉ ys}
    {D' : xs.Disjoint (ys.cons l s p')}
    {p : l ∉ xs}
    {D : (xs.concat l s p).Disjoint ys}:
    (xs.concat l s p).append ys D = xs.append (ys.cons l s p') D'
    := by
  rw [AList.ext_iff]
  cases xs with | mk xs D
  cases ys with | mk ys D
  simp[cons,append,concat]


lemma List.concat_non_empty {xs : List α} : [] ≠ xs ++ [x] := by
  intros E;
  cases xs <;> grind


lemma AList.length_empty {xs : AList β} :   xs.entries.length = 0 → xs = ∅ := by
  intros L
  cases xs with | mk xs D
  cases xs
  . rfl
  . cases L

lemma List.cons_NodupKeys : (x :: xs).NodupKeys → xs.NodupKeys := by
  intros N
  simp[NodupKeys] at *
  apply N.2


lemma List.cons_NodupKeys_fresh : (x :: xs).NodupKeys → x.1 ∉ ⟪ xs, D' ⟫ := by
  intros N
  simp[NodupKeys] at *
  apply N.1



def AList.reverse {α} [DecidableEq α] {β : α → Type} (xs : AList β) : AList β :=
  ⟨ xs.entries.reverse, by
    rw[List.perm_nodupKeys]
    . apply xs.nodupKeys
    . apply List.reverse_perm
   ⟩

@[simp]
def AList.nin_reverse {α} [DecidableEq α] {β : α → Type} {xs : AList β} {l : α}:
  l ∉ xs → l ∉ xs.reverse := by
  cases xs with | mk xs N
  simp[AList.reverse,AList.mem_keys,AList.keys,List.keys]


def AList.reverse_cons {α} [DecidableEq α] {β : α → Type} {xs : AList β} {l : α} {x : β l}
  {p : l ∉ xs} {p' : l ∉ xs.reverse} :
  (xs.cons l x p).reverse = xs.reverse.concat l x p' := by
  cases xs with | mk xs N
  rw[AList.ext_iff]
  simp[AList.reverse,AList.concat,cons]


@[simp]
def AList.reverse_reverse {α} [DecidableEq α] {β : α → Type} {xs : AList β} :
  xs.reverse.reverse = xs := by
  cases xs with | mk xs N
  rw[AList.ext_iff]
  simp[AList.reverse]

lemma AList.cons_decompose {α} [DecidableEq α] {β : α → Type} {xs : AList β} {n : Nat} :
  xs.entries.length = n.succ →
  ∃ (ys : AList β), ∃ l x, ∃ (p : l ∉ ys), xs = ys.cons l x p /\ ys.entries.length = n := by
  intros E
  cases xs with | mk xs D
  cases xs
  case nil =>
    simp! at E
  case cons x xs =>
    simp! at E
    have D' : xs.NodupKeys := by apply List.cons_NodupKeys D
    exists ⟪xs , D'⟫, x.1 ,x.2, List.cons_NodupKeys_fresh D


lemma AList.concat_decompose {α} [DecidableEq α] {β : α → Type} {xs : AList β} {n : Nat}:
  xs.entries.length = n.succ →
  ∃ (ys : AList β), ∃ l x, ∃ (p : l ∉ ys), xs = ys.concat l x p /\ ys.entries.length = n := by
  intros E
  have E' : xs.reverse.entries.length = n.succ := by simp[AList.reverse]; assumption
  apply AList.cons_decompose at E'
  rcases E' with ⟨ys ,l, x, p, E1, E2⟩
  have p' : l ∉ ys.reverse := AList.nin_reverse p
  have E1' : xs.reverse.reverse = (cons l x ys p).reverse := by
    rw[E1]
  rewrite [AList.reverse_cons,AList.reverse_reverse] at E1'
  exists ys.reverse, l , x, p'
  split_ands
  assumption
  simp[AList.reverse]; assumption

lemma AList.nonempty_decompose {α} [DecidableEq α] {β : α → Type} {xs : AList β} :
    xs ≠ ∅ → ∃ (ys : AList β), ∃ l x, ∃ (p : l ∉ ys), xs = ys.concat l x p := by
  intros N
  have N : ∃ (n : Nat), xs.entries.length = n.succ := by
    cases xs with | mk xs M
    cases xs
    case nil => contradiction
    case cons tl => exists tl.length
  rcases N with ⟨n,L⟩
  apply AList.concat_decompose at L
  grind


@[symm]
lemma AList.Disjoint.symm {xs ys : AList β} : xs.Disjoint ys → ys.Disjoint xs := by
  intros D
  have D' : xs.keys.Disjoint ys.keys := by assumption
  symm at D'
  apply D'

-------------------------
-- Disjointness lemmas --
-------------------------


lemma AList.Sub_Disjoint  (η η' η'' : AList β) : η.Sub η' → η'.Disjoint η'' → η.Disjoint η'' := by
  simp[Disjoint, AList.Sub, AList.keys]
  intros S D k E
  apply List.Sublist.subset at S
  unfold Subset at S
  apply List.exists_of_mem_keys at E
  rcases E with ⟨v,E⟩
  apply S at E
  apply List.mem_keys_of_mem at E; simp at E
  apply D at E
  apply E

lemma AList.cons_cons_Disjoint_keys
    {α} [DecidableEq α] {β : Type} {l:α} {s:β} {s':β'} {xs : AList' α β} {ys : AList' α β'}
    {p : l ∉ xs} {p':l ∉ ys}:
    (xs.cons l s p).keys.Disjoint ys.keys → xs.keys.Disjoint (ys.cons l s' p').keys := by
  intros D
  simp [AList.cons,AList.keys] at *
  constructor
  . intro E; apply p at E;contradiction
  . apply D.2

lemma AList.concat_cons_Disjoint_keys
    {α} [DecidableEq α] {β : Type} {l:α} {s:β} {s':β'} {xs : AList' α β} {ys : AList' α β'}
    {p : l ∉ xs} {p':l ∉ ys}:
    (xs.concat l s p).keys.Disjoint ys.keys → xs.keys.Disjoint (ys.cons l s' p').keys := by
  intros D
  apply AList.cons_cons_Disjoint_keys
  have P : List.Perm (cons l s xs p).keys (xs.concat l s p).keys := by
    simp[cons,AList.concat,AList.keys,List.keys];
    apply List.Perm.symm
    apply List.perm_append_singleton
  have R := List.Perm.disjoint_left (l := ys.keys) P
  apply R.mpr; apply D

lemma AList.concat_cons_Disjoint_nin
    {α} [DecidableEq α] {β : α → Type} {l:α} {s:β l} {xs ys : AList β}  {p : l ∉ xs} :
    (xs.concat l s p).Disjoint ys → l ∉ ys := by
  intros D
  simp[AList.Disjoint] at D
  apply D
  simp[AList.concat,AList.keys,List.keys]

lemma AList.concat_cons_Disjoint_nin_keys
    {α} [DecidableEq α]  {β : Type} {l:α} {s:β} {xs : AList' α β} {ys : AList' α β'} {p : l ∉ xs} :
    (xs.concat l s p).keys.Disjoint ys.keys → l ∉ ys := by
  intros D
  apply D
  simp[AList.concat,AList.keys,List.keys]


lemma AList.Disjoint_cons {α} [DecidableEq α] {β : α → Type} {xs ys : AList β}
    {l:α} {x:β l}  {p : l ∉ xs} : (xs.cons l x p).Disjoint ys →  xs.Disjoint ys := by
  intros D
  apply List.disjoint_of_disjoint_cons_left
  assumption
