/-
  Definition of the environments and its components, i.e. channel
  contexts, stores and heaps.
-/


import Mathlib.Data.Finset.Defs
import Rizzo.AList

import Rizzo.Terms

open Term
open Typ

---------------------------
-- Definition of events. --
-- (`e` in Fig. 1)     --
---------------------------
structure Event : Type where
    mk ::
    chan : Chan
    val : Term

notation κ " ↦ " v  => Event.mk κ v



structure Sig where
  mk ::
  type : Typ
  head : MVal
  ticked : Bool
  tail : MVal

def Sig.tick (s : Sig) := {s with ticked := true}

notation "mksig" => Sig.mk


abbrev HeapTy := AList' Loc Typ

abbrev HeapTy.le : HeapTy → HeapTy → Prop := AList.le


abbrev Heap := AList' Loc Sig

namespace Heap

abbrev le : Heap → Heap → Prop := AList.le

lemma le.trans' {η η' η'' : Heap} : η'.le η'' → η.le η' → η.le η'' := by
  intros S1 S2; apply S2.trans S1

def type (η : Heap) : HeapTy :=  ⟨ η.entries.entryMap (fun r => r.type  ) , List.entryMap_NodupKeys _ _ (η.nodupKeys) ⟩


lemma type_lookup {η : Heap} : η.type.lookup l = (η.lookup l).map Sig.type := by
  simp [AList.lookup,Heap.type,List.dlookup_entryMap]



lemma type_cons {η : Heap} {p p'} :
    type (η.cons l s p) = η.type.cons l s.type p' := by
  rw [AList.ext_iff]
  cases η with | mk η D
  simp[AList.cons,type,List.entryMap]


@[simp]
lemma type_keys {η : Heap} : η.type.keys = η.keys := by
  cases η with | mk η D
  simp[AList.keys,type]



lemma type_Disjoint {η η' : Heap} : η.Disjoint η' → η.type.Disjoint (η'.type) := by
  simp[AList.Disjoint]

lemma type_fresh {η:Heap} : l ∈ η.type ↔ l ∈ η := by
  rw[<-AList.lookup_isSome]
  rw[Heap.type_lookup]
  simp
  rw[<-AList.lookup_isSome]

lemma concat_inv {α} [DecidableEq α] {β : Type}  {η η' : AList' α β}
    {l l' s s' p' p}
    : η.concat l s p = η'.concat l' s' p' → η = η' /\ l = l' /\ s = s' := by
  intros E
  rw[AList.ext_iff] at E
  simp[AList.concat,-List.concat_eq_append] at E
  rw[List.concat_inj] at E
  rw[<-AList.ext_iff] at E
  grind

/-- Looking up the freshly-concatenated key returns its value. -/
lemma lookup_concat_self {ηE : Heap} {l₀ s₀} (p : l₀ ∉ ηE) :
    (ηE.concat l₀ s₀ p).lookup l₀ = some s₀ := by
  have hp : l₀ ∉ ηE.entries.keys := by rw [AList.mem_keys] at p; exact p
  simp [AList.lookup, AList.concat, List.concat_eq_append, List.dlookup_eq_none.mpr hp]

/-- Looking up a different key ignores the concatenated entry. -/
lemma lookup_concat_ne {ηE : Heap} {l₀ l s₀} (p : l₀ ∉ ηE) :
    l ≠ l₀ → (ηE.concat l₀ s₀ p).lookup l = ηE.lookup l := by
  intro h
  simp [AList.lookup, AList.concat, List.concat_eq_append, h]

end Heap

def Term.isSome (t : Term) :=
  match t with
  | in1 _ => true
  | _ => false
@[simp]
def MVal.isSome (v : MVal) := v.val.isSome

lemma Term.isSome_ex {t : Term} : t.isSome → ∃ (s : Term), t = s.in1 := by
  intros T
  simp[Term.isSome] at T
  grind

------------------------------------
-- Definition of ticked predicate --
-- (Fig. 8)                       --
------------------------------------

def Term.ticked (t : Term) (η : Heap) (κ : Chan) : Bool :=
  match t with
  | .wait (.chan κ') => κ = κ'
  | .watch (.loc l) =>
    match η.lookup l with
    | .some s => s.ticked /\ s.head.isSome
    | .none => false
  | .never => false
  | .select s t => s.ticked η κ \/ t.ticked η κ
  | .appE _ t => t.ticked η κ
  | .tail (.loc l) =>
    match η.lookup l with
    | .some r => r.ticked
    | .none => false
  | _ => false


abbrev MVal.ticked (t : MVal) (η : Heap) (κ : Chan) : Bool := t.val.ticked η κ

structure Store where
  now : Heap
  earlier : Heap
  disjoint : now.Disjoint earlier

notation : 191 ηN : 201 "✓[" D : 201 "]" ηE : 201 => Store.mk ηN ηE D

instance : EmptyCollection Store where
  emptyCollection := ∅ ✓[by simp[AList.Disjoint]] ∅

namespace Store

@[grind]
structure le (σ σ' : Store) : Prop where
  now : σ.now.le σ'.now
  earlier : σ.earlier = σ'.earlier

@[refl,simp]
def refl (σ : Store) : σ.le σ
  := by constructor <;> rfl


def le.trans {σ σ' σ'' : Store} : σ.le σ' → σ'.le σ'' → σ.le σ'' := by
  intros S T; constructor;
  apply S.now.trans T.now
  rw [S.earlier, T.earlier]

instance : IsTrans Store Store.le where
  trans := by
    intros σ σ2 σ3 S T; apply S.trans T

instance : Membership Loc Store :=
  ⟨fun σ l => l ∈ σ.now \/ l ∈ σ.earlier⟩

lemma now_fresh {σ : Store} : l ∉ σ → l ∉ σ.now := by
  intros N M; apply N; apply Or.inl; assumption

def insert (σ : Store) (l : Loc) (s : Sig) (p : l ∉ σ) : Store :=
 σ.now.cons l s (σ.now_fresh p)
   ✓[by
      intros l M M'
      apply p
      cases M
      case head => simp at *; apply Or.inr; apply M'
      case tail M'' => apply σ.disjoint at M''; contradiction]
  σ.earlier

@[simp]
lemma le.insert (σ : Store) (l : Loc) (s : Sig) (p : l ∉ σ)
  : σ.le (σ.insert l s p) := by
  constructor; apply AList.le.cons; apply Store.now_fresh p
  simp [Store.insert]

def alloc (σ : Store) : Loc := max (σ.now.alloc) (σ.earlier.alloc)

lemma alloc_fresh' (σ : Store) : k ≥ σ.alloc → k ∉ σ := by
  intro L M
  simp [Store.alloc] at *
  cases L
  cases M
  case inl M => apply AList.alloc_fresh' at M; contradiction; assumption
  case inr M => apply AList.alloc_fresh' at M; contradiction; assumption

@[simp]
lemma alloc_fresh (σ : Store) : σ.alloc ∉ σ := by
  apply σ.alloc_fresh'; grind


def type (σ : Store) := σ.earlier.type.append (σ.now.type) (Heap.type_Disjoint σ.disjoint.symm)


end Store

abbrev ChanCtx : Type := AList (fun _ : Chan => Typ)


abbrev ChanCtx.le : ChanCtx → ChanCtx → Prop := AList.le

structure Env where
  store : Store
  chans : ChanCtx

infix : 190 " ⧸ "  => Env.mk

namespace Env

abbrev now (ε : Env) := ε.store.now
abbrev earlier (ε : Env) := ε.store.earlier

@[grind]
structure le (ε ε' : Env) : Prop where
  store : ε.store.le ε'.store
  chans : ε.chans.le ε'.chans

@[refl,simp]
def refl (ε : Env) : ε.le ε := by constructor <;> rfl


def le.trans {ε ε' ε'' : Env} : ε.le ε' → ε'.le ε'' → ε.le ε'' := by
  intros S T; constructor;
  apply IsTrans.trans; apply S.store; apply T.store
  apply IsTrans.trans; apply S.chans; apply T.chans

instance : IsTrans Env Env.le where
  trans := by
    intros ε ε2 ε3 S T; apply S.trans T

instance : Membership Loc Env :=
  ⟨fun ε l => l ∈ ε.store⟩

lemma eq_inv :
    ηN ✓[D] ηE ⧸ Δ = ηN' ✓[D'] ηE' ⧸ Δ' → ηN = ηN' /\ ηE = ηE' /\ Δ = Δ' := by
  intros E
  cases E
  grind
end Env

lemma List.getElem?_some_length (l : List α) : y ∈ l[x]? -> x < l.length := by
  intro S
  cases l
  case nil => simp at S
  case cons =>
    cases x
    case zero => simp at *
    case succ => simp at *; apply List.getElem?_some_length; assumption



notation ε ".Δ" => Env.chans ε
notation ε ".σ" => Env.store ε
notation σ ".ηN" => Store.now σ
notation ε ".σN" => Env.now ε
notation η ".ηN" => Heap.earlier η
notation η ".𝕋" => Heap.type η


------------------------------------------------------
-- Lemmas about the environments, stores, and heaps --
------------------------------------------------------


@[grind .,simp]
lemma AList.lookup_cons {α} [DecidableEq α] {β : α → Type} (k : α) (x : β k) (xs : AList β) (p : k ∉ xs) :
  x ∈ (xs.cons k x p).lookup k := by
  simp[AList.lookup,cons]

@[simp]
lemma Store.lookup_insert (k : Loc) x (σ : Store) (p : k ∉ σ) :
  x ∈ (σ.insert k x p).now.lookup k := by
  simp[AList.lookup,Store.insert,AList.cons]

@[grind .]
lemma AList.le.lookup {α} [DecidableEq α] {β : α → Type} {k x} {xs ys : AList β} :
  xs.le ys → x ∈ xs.lookup k → x ∈ ys.lookup k := by
  intros S L
  simp [AList.le, AList.lookup] at *
  have L' : x ∈ List.dlookup k xs.entries := by assumption
  rw [List.mem_dlookup_iff xs.nodupKeys] at L'
  have E := List.Sublist.mem L' S
  rw [<- List.mem_dlookup_iff ys.nodupKeys] at E
  apply E

/-- A present key has the same lookup in a larger heap. -/
lemma AList.lookup_eq_of_le_mem {α} [DecidableEq α] {β : α → Type} {xs ys : AList β} {l} :
    xs.le ys → l ∈ xs → ys.lookup l = xs.lookup l := by
  intro hle hl
  obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hl)
  rw [hsl]; exact AList.le.lookup hle hsl

@[grind .,simp]
lemma Heap.le.type (η η' : Heap) : η.le η' → η.type.le η'.type := by
  intro S
  simp [Heap.type,List.entryMap, AList.le] at *
  apply List.Sublist.map
  apply S


lemma Store.le_type {σ σ' : Store} : σ.le σ' → σ.type.le σ'.type := by
  intros S
  rcases S with ⟨S1, S2⟩
  apply Heap.le.type at S1
  simp[Store.type, AList.le, AList.append] at *
  rw[S2]
  apply List.Sublist.append_left
  assumption
