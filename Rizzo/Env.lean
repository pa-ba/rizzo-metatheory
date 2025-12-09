/-
  Definition of the environments and its components, i.e. channel
  contexts, stores and heaps.
-/


import Mathlib.Data.Finset.Defs
import Rizzo.AList

import Rizzo.Syntax

open Term
open Typ


structure Inp : Type where
    mk ::
    chan : Chan
    val : Val

notation x " ↦ " y  => Inp.mk x y



structure Sig where
  mk ::
  type : Typ
  head : Val
  ticked : Bool
  tail : Val

def Sig.tick (s : Sig) := {s with ticked := true}

notation "mksig" => Sig.mk


abbrev HeapTy := AList' Loc Typ

abbrev HeapTy.Sub : HeapTy → HeapTy → Prop := AList.Sub


@[simp]
def HeapTy.Sub_empty (H : HeapTy) : HeapTy.Sub ∅ H := by simp

abbrev Heap := AList' Loc Sig

namespace Heap

abbrev Sub : Heap → Heap → Prop := AList.Sub

lemma Sub.trans' {η η' η'' : Heap} : η'.Sub η'' → η.Sub η' → η.Sub η'' := by
  intros S1 S2; apply S2.trans S1

def type (η : Heap) : HeapTy :=  ⟨ η.entries.entryMap (fun r => r.type  ) , List.entryMap_NodupKeys _ _ (η.nodupKeys) ⟩


lemma type_lookup {η : Heap} : η.type.lookup l = (η.lookup l).map Sig.type := by
  simp [AList.lookup,Heap.type,List.dlookup_entryMap]



lemma type_cons {η: Heap} {p : l ∉ η} {p' : l ∉ η.type} :
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
    {l l':α} {s s':β} {p' : l' ∉ η'} {p : l ∉ η}
    : η.concat l s p = η'.concat l' s' p' → η = η' /\ l = l' /\ s = s' := by
  intros E
  rw[AList.ext_iff] at E
  simp[AList.concat,-List.concat_eq_append] at E
  rw[List.concat_inj] at E
  rw[<-AList.ext_iff] at E
  grind



end Heap

def Term.isSome (t : Term) :=
  match t with
  | in1 _ => true
  | _ => false
@[simp]
def Val.isSome (v : Val) := v.val.isSome

lemma Term.isSome_ex {t : Term} : t.isSome → ∃ (s : Term), t = s.in1 := by
  intros T
  simp[Term.isSome] at T
  grind

lemma Val.isSome_ex {t : Val} : t.isSome → ∃ (s : Term), t = s.in1 := by
  intros T
  simp[Term.isSome] at T
  grind

def Term.ticked (t : Term) (η : Heap) (κ : Chan) : Bool :=
  match t with
  | .wait (.chan κ') => κ = κ'
  | .trig (.loc l) =>
    match η.lookup l with
    | .some s => s.ticked /\ s.head.isSome
    | .none => false
  | .never => false
  | .sync s t => s.ticked η κ \/ t.ticked η κ
  | .appE _ t => t.ticked η κ
  | .tail (.loc l) =>
    match η.lookup l with
    | .some r => r.ticked
    | .none => false
  | _ => false


abbrev Val.ticked (t : Val) (η : Heap) (κ : Chan) : Bool := t.val.ticked η κ




structure Store where
  now : Heap
  earlier : Heap
  disjoint : now.Disjoint earlier

notation : 191 ηN : 201 "✓[" D : 201 "]" ηE : 201 => Store.mk ηN ηE D

instance : EmptyCollection Store where
  emptyCollection := ∅ ✓[by simp[AList.Disjoint]] ∅

namespace Store

@[grind]
structure Sub (σ σ' : Store) : Prop where
  now : σ.now.Sub σ'.now
  earlier : σ.earlier = σ'.earlier

@[refl,simp]
def refl (σ : Store) : σ.Sub σ
  := by constructor <;> rfl


def Sub.trans {σ σ' σ'' : Store} : σ.Sub σ' → σ'.Sub σ'' → σ.Sub σ'' := by
  intros S T; constructor;
  apply S.now.trans T.now
  rw [S.earlier, T.earlier]

lemma Sub.trans' {σ σ' σ'' : Heap} : σ'.Sub σ'' → σ.Sub σ' → σ.Sub σ'' := by
  intros S1 S2; apply S2.trans S1


instance : IsTrans Store Store.Sub where
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
lemma Sub.insert (σ : Store) (l : Loc) (s : Sig) (p : l ∉ σ)
  : σ.Sub (σ.insert l s p) := by
  constructor; apply AList.Sub.cons; apply Store.now_fresh p
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


abbrev ChanCtx.Sub : ChanCtx → ChanCtx → Prop := AList.Sub

structure Env where
  store : Store
  chans : ChanCtx

infix : 190 " ⧸ "  => Env.mk

namespace Env

abbrev now (ε : Env) := ε.store.now
abbrev earlier (ε : Env) := ε.store.earlier

@[grind]
structure Sub (ε ε' : Env) : Prop where
  store : ε.store.Sub ε'.store
  chans : ε.chans.Sub ε'.chans

@[refl,simp]
def refl (ε : Env) : ε.Sub ε := by constructor <;> rfl


def Sub.trans {ε ε' ε'' : Env} : ε.Sub ε' → ε'.Sub ε'' → ε.Sub ε'' := by
  intros S T; constructor;
  apply IsTrans.trans; apply S.store; apply T.store
  apply IsTrans.trans; apply S.chans; apply T.chans

instance : IsTrans Env Env.Sub where
  trans := by
    intros ε ε2 ε3 S T; apply S.trans T

instance : Membership Loc Env :=
  ⟨fun ε l => l ∈ ε.store⟩

def alloc (ε : Env) : Loc := ε.store.alloc

lemma eq_inv :
    ηN ✓[D] ηE ⧸ δ = ηN' ✓[D'] ηE' ⧸ δ' → ηN = ηN' /\ ηE = ηE' /\ δ = δ' := by
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



notation ε ".δ" => Env.chans ε
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
lemma AList.Sub.lookup {α} [DecidableEq α] {β : α → Type} {k : α} {x : β k} {xs ys : AList β} :
  xs.Sub ys → x ∈ xs.lookup k → x ∈ ys.lookup k := by
  intros S L
  simp [AList.Sub, AList.lookup] at *
  have L' : x ∈ List.dlookup k xs.entries := by assumption
  rw [List.mem_dlookup_iff xs.nodupKeys] at L'
  have E := List.Sublist.mem L' S
  rw [<- List.mem_dlookup_iff ys.nodupKeys] at E
  apply E

@[grind .,simp]
lemma Heap.Sub.type (η η' : Heap) : η.Sub η' → η.type.Sub η'.type := by
  intro S
  simp [Heap.type,List.entryMap, AList.Sub] at *
  apply List.Sublist.map
  apply S


lemma Store.Sub_type {σ σ' : Store} : σ.Sub σ' → σ.type.Sub σ'.type := by
  intros S
  rcases S with ⟨S1, S2⟩
  apply Heap.Sub.type at S1
  simp[Store.type, AList.Sub, AList.append] at *
  rw[S2]
  apply List.Sublist.append_left
  assumption
