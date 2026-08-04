/-
  The correspondence between the `ticked` predicate and the *clock* of a
  delayed computation.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Rizzo.Preservation

open Term
open Typ

/- `Term.refs t` collects the signal locations that the delayed computation
`t` immediately inspects, i.e. the `watch`/`tail` locations reachable through
`select` and the applicative action `⊚` (`appE`). -/
def Term.refs : Term → Finset Loc
  | .watch (.loc l) => {l}
  | .tail (.loc l) => {l}
  | .select s t => s.refs ∪ t.refs
  | .appE _ t => t.refs
  | _ => ∅

--  The suffix of a heap after a location
def afterLoc (l : Loc) : List (Σ _ : Loc, Sig) → List (Σ _ : Loc, Sig)
  | [] => []
  | e :: rest => if e.fst = l then rest else afterLoc l rest

lemma afterLoc_sublist (l : Loc) : ∀ es : List (Σ _ : Loc, Sig), (afterLoc l es).Sublist es
  | [] => by simp [afterLoc]
  | e :: rest => by
      rw [afterLoc]
      split
      · exact (List.Sublist.refl rest).cons e
      · exact (afterLoc_sublist l rest).cons e

lemma afterLoc_length_lt (l : Loc) : ∀ {es : List (Σ _ : Loc, Sig)},
    (∃ e ∈ es, e.fst = l) → (afterLoc l es).length < es.length
  | [], h => by simp at h
  | e :: rest, h => by
      rw [afterLoc]
      split
      · simp
      · rename_i hne
        have hrest : ∃ e' ∈ rest, e'.fst = l := by
          obtain ⟨e', he', hfst⟩ := h
          rcases List.mem_cons.mp he' with rfl | hmem
          · exact absurd hfst hne
          · exact ⟨e', hmem, hfst⟩
        have := afterLoc_length_lt l hrest
        simp only [List.length_cons]; omega

--  The heap restricted to the entries after a location

def Heap.below (η : Heap) (l : Loc) : Heap :=
  ⟨ afterLoc l η.entries,
    List.NodupKeys.sublist (afterLoc_sublist l η.entries) η.nodupKeys ⟩

lemma Heap.below_le {η : Heap} {l} : (η.below l).le η :=
  afterLoc_sublist l η.entries

lemma Heap.below_length_lt {η : Heap} {l} :
    l ∈ η → (η.below l).entries.length < η.entries.length := by
  intro h
  apply afterLoc_length_lt
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr h)
  exact ⟨⟨l, s⟩, AList.mem_lookup_iff.mp hs, rfl⟩


inductive MClockElem where
  | chan : Chan → MClockElem
  | loc : Loc → MClockElem
deriving DecidableEq

-- machine clock
abbrev MClock := Finset MClockElem

---------------------------------------------------------
-- The clock of a delayed computation (in the machine) --
-- (Defined in sect. 4.2)                              --
---------------------------------------------------------
def mclock : Heap → Term → MClock
  | _, .wait (.chan κ) => {.chan κ}
  | _, .watch (.loc l) => {.loc l}
  | η, .select s t => mclock η s ∪ mclock η t
  | η, .appE _ t => mclock η t
  | η, .tail (.loc l) =>
      match _h : η.lookup l with
      | some s => mclock (η.below l) s.tail.val
      | none => ∅
  | _, _ => ∅
termination_by η t => (η.entries.length, sizeOf t)
decreasing_by
  all_goals
    first
    | (apply Prod.Lex.left
       exact Heap.below_length_lt (AList.lookup_isSome.mp (by simp [_h])))
    | (apply Prod.Lex.right; simp_wf; omega)


 -- Fresh signals and well-formedness

def freshSome (ηN : Heap) (l : Loc) : Prop :=
  ∃ s, s ∈ ηN.lookup l ∧ s.head.val.isSome ∧ s.ticked

-- Unfolding `ticked` on a stored tail

lemma ticked_tail_loc {ηN l κ} :
    (Term.tail (Term.loc l)).ticked ηN κ ↔ ∃ s, s ∈ ηN.lookup l ∧ s.ticked := by
  simp only [Term.ticked]
  cases ηN.lookup l <;> simp

-- `ticked` depends only on a term's references

lemma Term.ticked_refs_stable {η η' : Heap} {κ} {t : Term} :
    η.le η' → (∀ l ∈ t.refs, l ∈ η) → t.ticked η κ = t.ticked η' κ := by
  intro S
  induction t <;> intro h <;> try simp [Term.ticked]
  case wait t _ => cases t <;> simp [Term.ticked]
  case watch t _ =>
    cases t with
    | loc l =>
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp
        (AList.lookup_isSome.mpr (h l (by simp [Term.refs])))
      have e1 : η.lookup l = some s := Option.mem_def.mp hs
      have e2 : η'.lookup l = some s := Option.mem_def.mp (AList.le.lookup S hs)
      simp [Term.ticked, e1, e2]
    | _ => simp [Term.ticked]
  case select t1 t2 IH1 IH2 =>
    rw [IH1 (fun l hl => h l (Finset.mem_union.mpr (Or.inl hl))),
        IH2 (fun l hl => h l (Finset.mem_union.mpr (Or.inr hl)))]
  case appE a t _ IH =>
    exact IH (fun l hl => h l (by simpa only [Term.refs] using hl))
  case tail t _ =>
    cases t with
    | loc l =>
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp
        (AList.lookup_isSome.mpr (h l (by simp [Term.refs])))
      have e1 : η.lookup l = some s := Option.mem_def.mp hs
      have e2 : η'.lookup l = some s := Option.mem_def.mp (AList.le.lookup S hs)
      simp [Term.ticked, e1, e2]
    | _ => simp [Term.ticked]

-- A well-typed term only refers to locations present in the heap typing `H`.
lemma HasType.refs_sub {H Δ Γ} :
    ∀ {t A}, HasType H Δ Γ t A → ∀ l ∈ t.refs, l ∈ H := by
  intro t
  induction t with
  | watch t' ih =>
    intro A T l hl
    have ht' : t' = Term.loc l := by cases t' <;> simp_all [Term.refs]
    subst ht'
    cases T with
    | watch T' => cases T' with
      | loc M => exact AList.lookup_isSome.mp (Option.isSome_iff_exists.mpr ⟨_, M⟩)
  | tail t' ih =>
    intro A T l hl
    have ht' : t' = Term.loc l := by cases t' <;> simp_all [Term.refs]
    subst ht'
    cases T with
    | tail T' => cases T' with
      | loc M => exact AList.lookup_isSome.mp (Option.isSome_iff_exists.mpr ⟨_, M⟩)
  | select s t ihs iht =>
    intro A T l hl
    cases T with
    | select _ _ Ts Tt =>
      rw [Term.refs, Finset.mem_union] at hl
      rcases hl with h | h
      · exact ihs Ts l h
      · exact iht Tt l h
  | appE a t iha iht =>
    intro A T l hl
    cases T with
    | appE Ta Tt =>
      rw [Term.refs] at hl
      exact iht Tt l hl
  | _ => intro A T l hl; simp [Term.refs] at hl

-- The locations referenced by a delayed computation `u` typed against
-- a heap's type are present in that heap.
lemma HasType.term_wf {η : Heap} {Δ Γ u A} :
    HasType η.type Δ Γ u A → ∀ l ∈ u.refs, l ∈ η := fun T l hl =>
  Heap.type_fresh.mp (HasType.refs_sub T l hl)

-- `afterLoc` of a cons at the matching key drops the head.
lemma afterLoc_cons_self {l s es} :
    afterLoc l (⟨l, s⟩ :: es) = es := by simp [afterLoc]

-- `afterLoc` of a cons at a different key ignores the head.
lemma afterLoc_cons_ne {l l' s es} :
    l' ≠ l → afterLoc l (⟨l', s⟩ :: es) = afterLoc l es := by intro h; simp [afterLoc, h]

-- `afterLoc` past a prefix that avoids the key, followed by a
-- matching entry, returns the remaining suffix.
lemma afterLoc_append_self {l₀ s₀ t} :
    ∀ {xs : List (Σ _ : Loc, Sig)}, (∀ x ∈ xs, x.fst ≠ l₀) →
      afterLoc l₀ (xs ++ ⟨l₀, s₀⟩ :: t) = t
  | [], _ => afterLoc_cons_self
  | ⟨k, v⟩ :: xs', h => by
      have hk : k ≠ l₀ := h ⟨k, v⟩ List.mem_cons_self
      rw [List.cons_append, afterLoc_cons_ne hk,
          afterLoc_append_self (fun x hx => h x (List.mem_cons_of_mem _ hx))]

-- locations strictly after `l₀` in `η` lie outside the earlier prefix.

lemma Heap.below_of_earlier_prefix {η ηE : Heap} {l₀ s₀ p} :
    (ηE.concat l₀ s₀ p).entries <+: η.entries →
    ∀ l ∈ η.below l₀, l ∈ η ∧ l ∉ ηE ∧ l ≠ l₀ := by
  intro hpre
  obtain ⟨t, ht⟩ := hpre
  have hcat : (ηE.concat l₀ s₀ p).entries = ηE.entries ++ [⟨l₀, s₀⟩] := by
    simp [AList.concat, List.concat_eq_append]
  have hentries : η.entries = ηE.entries ++ ⟨l₀, s₀⟩ :: t := by
    rw [← ht, hcat, List.append_assoc, List.singleton_append]
  have hkne : ∀ x ∈ ηE.entries, x.fst ≠ l₀ := fun x hx he =>
    p (he ▸ AList.mem_keys.mpr (List.mem_keys_of_mem hx))
  have hbelow : (η.below l₀).entries = t := by
    show afterLoc l₀ η.entries = t
    rw [hentries]; exact afterLoc_append_self hkne
  have hnd : (ηE.entries.keys ++ l₀ :: t.keys).Nodup := by
    have h0 : η.entries.keys.Nodup := η.nodupKeys
    rw [hentries, List.keys_append, List.keys_cons] at h0
    exact h0
  obtain ⟨-, hndc, hdisj⟩ := List.nodup_append.mp hnd
  intro l hl
  have hlt : l ∈ t.keys := by
    have hk := AList.mem_keys.mp hl
    have he : (η.below l₀).keys = t.keys := by
      show (η.below l₀).entries.keys = t.keys; rw [hbelow]
    rwa [he] at hk
  refine ⟨AList.mem_keys.mpr ?_, ?_, ?_⟩
  · show l ∈ η.entries.keys
    rw [hentries, List.keys_append, List.keys_cons]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hlt)
  · intro hlE
    have h1 : l ∈ ηE.entries.keys := AList.mem_keys.mp hlE
    have h2 : l ∈ l₀ :: t.keys := List.mem_cons_of_mem _ hlt
    exact hdisj l h1 l h2 rfl
  · rintro rfl
    exact (List.nodup_cons.mp hndc).1 hlt

-- Inversion of `IsHeap` at a stored key.
lemma IsHeap.below_inv {Δ η} :
    ⊢[Δ] η ∷now →
    ∀ l s, s ∈ η.lookup l →
      (⊢[Δ] η.below l ∷now) ∧
      ⊢[Δ, (η.below l).type] s.tail.val ∷ ◯ (Typ.sig s.type) := by
  intro HT
  induction HT with
  | nil => intro l s hs; simp [AList.lookup_empty] at hs
  | cons HT' Thd Ttl ih =>
    rename_i es' M A l₀ hd a tl N
    intro l s hs
    by_cases hl : l = l₀
    · -- the looked-up signal is the head; the cons premises give both facts directly
      subst hl
      have hlk : AList.lookup l ⟪⟨l, mksig A hd a tl⟩ :: es', N⟫ = some (mksig A hd a tl) := by
        simp [AList.lookup, List.dlookup]
      rw [hlk] at hs
      simp only [Option.mem_def, Option.some.injEq] at hs
      subst hs
      have hbelow : Heap.below ⟪⟨l, mksig A hd a tl⟩ :: es', N⟫ l = ⟪es', M⟫ := by
        rw [AList.ext_iff]; exact afterLoc_cons_self
      rw [hbelow]
      exact ⟨HT', Ttl⟩
    · -- the looked-up signal lies in the suffix; conclude by induction
      have hl₀ : l₀ ≠ l := fun h => hl h.symm
      have hs' : s ∈ AList.lookup l (⟪es', M⟫ : Heap) := by
        have hlk : AList.lookup l ⟪⟨l₀, mksig A hd a tl⟩ :: es', N⟫
            = AList.lookup l ⟪es', M⟫ :=
          List.dlookup_cons_ne es' ⟨l₀, mksig A hd a tl⟩ hl
        rwa [hlk] at hs
      have hbelow : Heap.below ⟪⟨l₀, mksig A hd a tl⟩ :: es', N⟫ l = Heap.below ⟪es', M⟫ l := by
        rw [AList.ext_iff]; exact afterLoc_cons_ne hl₀
      rw [hbelow]
      exact ih l s hs'

-- intrinsic inductive invariant `TickConsistent` to prove the
-- correspondence.

def TickConsistent (η : Heap) (ε : Env) (κ : Chan) : Prop :=
  ∀ l s, s ∈ η.lookup l →
    s ∈ ε.earlier.lookup l ∨
    (l ∈ ε.now ∧
     (∀ l' ∈ s.tail.val.refs, l' ∈ ε.now) ∧
     ((∃ s', s' ∈ ε.now.lookup l ∧ s'.ticked) ↔ s.tail.val.ticked ε.now κ))

-- `TickConsistent` holds before the first update.
lemma TickConsistent.start {η κ Δ D} : TickConsistent η (∅ ✓[D] η ⧸ Δ) κ :=
  fun _ _ hs => Or.inl hs

-- earlier heap is a prefix of `η`
def EarlierPrefix (η : Heap) (ε : Env) : Prop := ε.earlier.entries <+: η.entries

lemma EarlierPrefix.start {η Δ D} :
    EarlierPrefix η (∅ ✓[D] η ⧸ Δ) := List.prefix_rfl

-- A single update step keeps the `earlier` heap a prefix of `η`
lemma EarlierPrefix.preserve {η ε ε' e} :
    ε [e]⇒ ε' → EarlierPrefix η ε → EarlierPrefix η ε' := by
  intro R h
  refine List.IsPrefix.trans ?_ h
  cases R with
  | skip Ch =>
    rename_i ηN Δ l₀ A hd tl p' ηE D' b p D
    show ηE.entries <+: (ηE.concat l₀ (mksig A hd b tl) p).entries
    simp [AList.concat, List.concat_eq_append, List.prefix_append]
  | adv Ch R' L =>
    rename_i ηN Δ l' ηN_adv Δ' s' l₀ p' ηE D'' sig0 p D D'
    show ηE.entries <+: (ηE.concat l₀ sig0 p).entries
    simp [AList.concat, List.concat_eq_append, List.prefix_append]

-- Locations after the processed one are already in the `now` heap.
lemma TickConsistent.below_now {η ηN ηE : Heap} {l₀ s₀ Δ p D κ} :
    (ηE.concat l₀ s₀ p).entries <+: η.entries →
    TickConsistent η (ηN ✓[D] ηE.concat l₀ s₀ p ⧸ Δ) κ →
    ∀ l ∈ η.below l₀, l ∈ ηN := by
  intro hpre h l hl
  obtain ⟨hlη, hlE, hll₀⟩ := Heap.below_of_earlier_prefix hpre l hl
  obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp (AList.lookup_isSome.mpr hlη)
  rcases h l sl hsl with hmem | ⟨hnow, _⟩
  · exfalso
    simp only [Env.earlier] at hmem
    rw [Heap.lookup_concat_ne p hll₀] at hmem
    exact hlE (AList.lookup_isSome.mp (Option.isSome_iff_exists.mpr ⟨sl, hmem⟩))
  · simpa only [Env.now] using hnow


lemma TickConsistent.processed_mono {ηN ηN' : Heap} {κ l} {s : Sig} :
    ηN.le ηN' → l ∈ ηN →
    (∀ l' ∈ s.tail.val.refs, l' ∈ ηN) →
    ((∃ s', s' ∈ ηN.lookup l ∧ s'.ticked) ↔ s.tail.val.ticked ηN κ) →
    l ∈ ηN' ∧ (∀ l' ∈ s.tail.val.refs, l' ∈ ηN') ∧
      ((∃ s', s' ∈ ηN'.lookup l ∧ s'.ticked) ↔ s.tail.val.ticked ηN' κ) := by
  intro hmono hlnow hrefs hcons
  refine ⟨AList.le.mem hmono hlnow, fun l' hl' => AList.le.mem hmono (hrefs l' hl'), ?_⟩
  rw [AList.lookup_eq_of_le_mem hmono hlnow, ← Term.ticked_refs_stable hmono hrefs]
  exact hcons

-- a single update step preserves `TickConsistent`

lemma TickConsistent.preserve {Δ₀ η ε ε' e} :
    ⊢[Δ₀] η ∷now → EarlierPrefix η ε →
    ε [e]⇒ ε' → TickConsistent η ε e.chan →
    TickConsistent η ε' e.chan := by
  intro Tη hpre R h
  cases R with
  | skip Ch =>
    rename_i ηN Δ l₀ A hd tl p' ηE D' b p D
    have hmono : ηN.le (ηN.cons l₀ (mksig A hd false tl) p') := AList.le.cons _ _ _ _
    intro l s hs
    rcases h l s hs with hmem | ⟨hlnow, hrefs, hcons⟩
    · by_cases hll : l = l₀
      · subst hll
        rw [Heap.lookup_concat_self p, Option.mem_def, Option.some.injEq] at hmem
        subst hmem
        have hrefs_now : ∀ l' ∈ (mksig A hd b tl).tail.val.refs, l' ∈ ηN := fun l' hl' =>
          TickConsistent.below_now hpre h l' ((Tη.below_inv l _ hs).2.term_wf l' hl')
        refine Or.inr ⟨?_, ?_, ?_⟩
        · exact AList.lookup_isSome.mp
            (Option.isSome_iff_exists.mpr ⟨_, AList.lookup_cons l (mksig A hd false tl) ηN p'⟩)
        · exact fun l' hl' => AList.le.mem hmono (hrefs_now l' hl')
        · have hlk : (ηN.cons l (mksig A hd false tl) p').lookup l = some (mksig A hd false tl) :=
            AList.lookup_cons l (mksig A hd false tl) ηN p'
          rw [hlk, ← Term.ticked_refs_stable hmono hrefs_now]
          simp only [Option.mem_some_iff, MVal.ticked, Bool.not_eq_true] at Ch ⊢
          simp [Ch]
      · rw [Heap.lookup_concat_ne p hll] at hmem
        exact Or.inl hmem
    · exact Or.inr (TickConsistent.processed_mono hmono hlnow hrefs hcons)
  | adv Ch R' L =>
    rename_i ηN Δ l' ηN_adv Δ' s' l₀ p' ηE D'' sig0 p D D'
    have hmono : ηN.le (ηN_adv.cons l₀ s'.tick p') :=
      AList.le.trans R'.incr.store.now (AList.le.cons _ _ _ _)
    intro l s hs
    rcases h l s hs with hmem | ⟨hlnow, hrefs, hcons⟩
    · by_cases hll : l = l₀
      · subst hll
        rw [Heap.lookup_concat_self p, Option.mem_def, Option.some.injEq] at hmem
        subst hmem
        have hrefs_now : ∀ l' ∈ sig0.tail.val.refs, l' ∈ ηN := fun l' hl' =>
          TickConsistent.below_now hpre h l' ((Tη.below_inv l _ hs).2.term_wf l' hl')
        refine Or.inr ⟨?_, ?_, ?_⟩
        · exact AList.lookup_isSome.mp
            (Option.isSome_iff_exists.mpr ⟨_, AList.lookup_cons l s'.tick ηN_adv p'⟩)
        · exact fun l' hl' => AList.le.mem hmono (hrefs_now l' hl')
        · have hlk : (ηN_adv.cons l s'.tick p').lookup l = some s'.tick :=
            AList.lookup_cons l s'.tick ηN_adv p'
          rw [hlk, ← Term.ticked_refs_stable hmono hrefs_now]
          simp only [Option.mem_some_iff, MVal.ticked] at Ch ⊢
          simp [Sig.tick, Ch]
      · rw [Heap.lookup_concat_ne p hll] at hmem
        exact Or.inl hmem
    · exact Or.inr (TickConsistent.processed_mono hmono hlnow hrefs hcons)

-- `TickConsistent` is preserved along an entire update sequence.
lemma TickConsistent.preserves {Δ₀ η ε ε' e} :
    ⊢[Δ₀] η ∷now → ε [e]⇒* ε' →
    EarlierPrefix η ε →
    TickConsistent η ε e.chan → TickConsistent η ε' e.chan := by
  intro Tη steps
  induction steps with
  | nil => intro _ h; exact h
  | cons R Rs IH =>
    intro hpre h
    exact IH (EarlierPrefix.preserve R hpre) (TickConsistent.preserve Tη hpre R h)


lemma mem_now_of_lookup {ε : Env} {l s} :
    s ∈ ε.now.lookup l → l ∈ ε.now :=
  fun hs => AList.lookup_isSome.mp (Option.isSome_iff_exists.mpr ⟨s, hs⟩)

-- freshly evaluated signals are unticked
lemma fresh_unticked_trans {ε ε' ε'' : Env} :
    ε'.now.le ε''.now →
    (∀ l s, s ∈ ε'.now.lookup l → l ∉ ε.now → ¬ s.ticked) →
    (∀ l s, s ∈ ε''.now.lookup l → l ∉ ε'.now → ¬ s.ticked) →
    ∀ l s, s ∈ ε''.now.lookup l → l ∉ ε.now → ¬ s.ticked := by
  intro h IH1 IH2 l s hs hl
  by_cases hl' : l ∈ ε'.now
  · rw [AList.lookup_eq_of_le_mem h hl'] at hs
    exact IH1 l s hs hl
  · exact IH2 l s hs hl'

-- Evaluation only allocates unticked signals

lemma Eval.now_fresh_unticked : ∀ {C D}, C ⇓ D →
    ∀ l s, s ∈ D.2.now.lookup l → l ∉ C.2.now → ¬ s.ticked := by
  intro C D R
  induction R with
  | value _ => intro l s hs hl; exact absurd (mem_now_of_lookup hs) hl
  | newchan => intro l s hs hl; exact absurd (mem_now_of_lookup hs) hl
  | in1 _ IH | in2 _ IH | pr1 _ IH | pr2 _ IH | wait _ IH | watch _ IH
  | tail _ IH | fix _ IH | cons _ IH => exact IH
  | head _ _ IH => exact IH
  | pair _ R2 IH1 IH2 | appE _ R2 IH1 IH2 | case1 _ R2 IH1 IH2 | case2 _ R2 IH1 IH2
  | select _ R2 IH1 IH2 | appA _ R2 IH1 IH2 =>
      exact fresh_unticked_trans R2.incr.store.now IH1 IH2
  | app _ R2 R3 IH1 IH2 IH3 | recur _ R2 R3 IH1 IH2 IH3 =>
      exact fresh_unticked_trans R3.incr.store.now
        (fresh_unticked_trans R2.incr.store.now IH1 IH2) IH3
  | @sig s ε v ε' t w σ Δ A R1 R2 IH1 IH2 =>
      intro l s2 hs hl
      by_cases hla : l = σ.alloc
      · subst hla
        have e1 : s2 = ⟨A, v, false, w⟩ := by
          have hc : (⟨A, v, false, w⟩ : Sig) ∈
              (σ.now.cons σ.alloc ⟨A, v, false, w⟩ (σ.now_fresh σ.alloc_fresh)).lookup σ.alloc :=
            AList.lookup_cons _ _ _ _
          simp only [Env.now, Store.insert] at hs
          rw [Option.mem_unique hs hc]
        simp [e1]
      · simp only [Env.now, Store.insert] at hs
        rw [AList.lookup_cons_ne (σ.now_fresh σ.alloc_fresh) hla] at hs
        exact fresh_unticked_trans R2.incr.store.now IH1 IH2 l s2 hs hl

-- Advancing a delayed computation only allocates unticked signals.
lemma Adv.now_fresh_unticked : ∀ {C D e}, C [e]⇘ D →
    ∀ l s, s ∈ D.2.now.lookup l → l ∉ C.2.now → ¬ s.ticked := by
  intro C D e R
  induction R with
  | wait Rev => exact Eval.now_fresh_unticked Rev
  | watch | tail => intro l s hs hl; exact absurd (mem_now_of_lookup hs) hl
  | appE R1 R2 IH =>
      have h2 := Eval.now_fresh_unticked R2
      exact fresh_unticked_trans R2.incr.store.now IH h2
  | select1 _ _ _ IH | select2 _ _ _ IH => exact IH
  | select3 _ _ R1 R2 IH1 IH2 => exact fresh_unticked_trans R2.incr.store.now IH1 IH2


-- `NowInv η ε` bundles the two structural facts we need about an intermediate
-- environment `ε` reached from `∅ ✓ η ⧸ Δ`

def NowInv (η : Heap) (ε : Env) : Prop :=
  (∀ l s, s ∈ ε.earlier.lookup l → s ∈ η.lookup l) ∧
  (∀ l, l ∉ η → ¬ ∃ s, s ∈ ε.now.lookup l ∧ s.ticked)

lemma NowInv.start {η Δ D} :
    NowInv η (∅ ✓[D] η ⧸ Δ) := by
  refine ⟨fun _ _ hs => hs, fun l _ => ?_⟩
  rintro ⟨s, hs, _⟩
  exact Option.not_mem_none s hs

-- A single update step preserves `NowInv`
lemma NowInv.preserve {η ε ε' e} :
    ε [e]⇒ ε' → NowInv η ε → NowInv η ε' := by
  intro R h
  obtain ⟨hsub, hfresh⟩ := h
  cases R with
  | skip Ch =>
    rename_i ηN Δ l₀ A hd tl p' ηE D' b p D
    refine ⟨?_, ?_⟩
    · intro l s hs
      apply hsub l s
      have hmem : l ∈ ηE := AList.lookup_isSome.mp (Option.isSome_iff_exists.mpr ⟨s, hs⟩)
      have hne : l ≠ l₀ := fun heq => p (heq ▸ hmem)
      rwa [Heap.lookup_concat_ne p hne]
    · intro l hl
      rintro ⟨s2, hs2, ht2⟩
      by_cases hll : l = l₀
      · subst hll
        have he : s2 = mksig A hd false tl :=
          Option.mem_unique hs2 (AList.lookup_cons l (mksig A hd false tl) ηN p')
        rw [he] at ht2
        simp at ht2
      · rw [AList.lookup_cons_ne p' hll] at hs2
        exact hfresh l hl ⟨s2, hs2, ht2⟩
  | adv Ch R' L =>
    rename_i ηN Δ l' ηN' Δ' s' l₀ p' ηE D'' s p D D'
    refine ⟨?_, ?_⟩
    · intro l s2 hs2
      apply hsub l s2
      have hmem : l ∈ ηE := AList.lookup_isSome.mp (Option.isSome_iff_exists.mpr ⟨s2, hs2⟩)
      have hne : l ≠ l₀ := fun heq => p (heq ▸ hmem)
      rwa [Heap.lookup_concat_ne p hne]
    · intro l hl
      rintro ⟨s2, hs2, ht2⟩
      by_cases hll : l = l₀
      · subst hll
        exact hl (AList.lookup_isSome.mp
          (Option.isSome_iff_exists.mpr ⟨s, hsub l s (Heap.lookup_concat_self p)⟩))
      · rw [AList.lookup_cons_ne p' hll] at hs2
        by_cases hlN : l ∈ ηN
        · rw [AList.lookup_eq_of_le_mem R'.incr.store.now hlN] at hs2
          exact hfresh l hl ⟨s2, hs2, ht2⟩
        · exact Adv.now_fresh_unticked R' l s2 hs2 hlN ht2

-- `NowInv` is preserved along an entire update sequence
lemma NowInv.preserves {η ε ε' e} :
    ε [e]⇒* ε' → NowInv η ε → NowInv η ε' := by
  intro steps
  induction steps with
  | nil => intro h; exact h
  | cons R _ IH => intro h; exact IH (NowInv.preserve R h)


-- Tick-consistency is inherited by `below` restrictions
lemma TickConsistent.below {η ε κ l₀} :
    TickConsistent η ε κ → TickConsistent (η.below l₀) ε κ :=
  fun h l s hs => h l s (AList.le.lookup Heap.below_le hs)

def TailReach (η : Heap) (ε : Env) (u : Term) : Prop :=
  ∀ l ∈ u.refs, l ∈ ε.now ∧ (l ∈ η ∨ ¬ ∃ s, s ∈ ε.now.lookup l ∧ s.ticked)

-- Localized ticked/mclock correspondence

lemma TickConsistent.ticked_mclock {Δ κ ε} (η : Heap) (u : Term) :
    (⊢[Δ] η ∷now) → TickConsistent η ε κ → TailReach η ε u →
    (u.ticked ε.now κ ↔
      (.chan κ ∈ mclock η u ∨ ∃ l, .loc l ∈ mclock η u ∧ freshSome ε.now l)) := by
  induction η, u using mclock.induct
  -- wait (chan κ')
  next x κ' =>
    intro _ _ _
    simp [Term.ticked, mclock]
  -- watch (loc l)
  next x l =>
    intro _ _ _
    simp only [Term.ticked, mclock, Finset.mem_singleton, freshSome]
    cases h : ε.now.lookup l <;> simp_all [and_comm]
  -- select s t
  next η s t ihs iht =>
    intro hη htc htr
    have hs : TailReach η ε s := fun l hl =>
      htr l (by simp only [Term.refs, Finset.mem_union]; exact Or.inl hl)
    have ht : TailReach η ε t := fun l hl =>
      htr l (by simp only [Term.refs, Finset.mem_union]; exact Or.inr hl)
    have IHs := ihs hη htc hs
    have IHt := iht hη htc ht
    simp only [Term.ticked, mclock, Finset.mem_union, decide_eq_true_eq]
    rw [IHs, IHt]
    constructor
    · rintro (hs' | ht')
      · rcases hs' with h | ⟨l, hl, hf⟩
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨l, Or.inl hl, hf⟩
      · rcases ht' with h | ⟨l, hl, hf⟩
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨l, Or.inr hl, hf⟩
    · rintro ((h | h) | ⟨l, hl | hl, hf⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr ⟨l, hl, hf⟩)
      · exact Or.inr (Or.inr ⟨l, hl, hf⟩)
  -- appE a t
  next η a t iht =>
    intro hη htc htr
    have ht : TailReach η ε t := fun l hl => htr l (by simpa only [Term.refs] using hl)
    have IHt := iht hη htc ht
    simp only [Term.ticked, mclock]
    exact IHt
  -- tail (loc l), signal present
  next η l s hlook ih =>
    intro hη htc htr
    obtain ⟨hbelow, htl⟩ := hη.below_inv l s hlook
    obtain ⟨hlnow, _⟩ := htr l (by simp [Term.refs])
    have hcons := (htc l s hlook).resolve_left (fun hE =>
      ε.store.disjoint l (AList.mem_keys.mp hlnow)
        (AList.mem_keys.mp (AList.lookup_isSome.mp (Option.isSome_iff_exists.mpr ⟨s, hE⟩))))
    have htr' : TailReach (η.below l) ε s.tail.val := fun l' hl' =>
      ⟨hcons.2.1 l' hl', Or.inl (htl.term_wf l' hl')⟩
    have IH := ih hbelow htc.below htr'
    have hmclock : mclock η (Term.tail (Term.loc l)) = mclock (η.below l) s.tail.val := by
      simp only [mclock]; rw [hlook]
    rw [ticked_tail_loc, hcons.2.2, IH, hmclock]
  -- tail (loc l), signal absent: mclock empty, location is fresh ⇒ unticked
  next η l hlook =>
    intro _ _ htr
    obtain ⟨_, hd⟩ := htr l (by simp [Term.refs])
    have hnt := hd.resolve_left (AList.lookup_eq_none.mp hlook)
    have hmclock : mclock η (Term.tail (Term.loc l)) = ∅ := by
      simp only [mclock]; rw [hlook]
    rw [ticked_tail_loc, hmclock]
    constructor
    · intro hL; exact absurd hL hnt
    · rintro (h | ⟨_, h, _⟩) <;> simp at h
  -- everything else: ticked is false and the mclock is empty
  next x u h1 h2 h3 h4 h5 =>
    intro _ _ _
    cases u <;>
      first
        | (exfalso; first
              | exact h1 _ rfl | exact h2 _ rfl | exact h3 _ _ rfl
              | exact h4 _ _ rfl | exact h5 _ rfl)
        | simp [mclock, Term.ticked]


inductive Extend : Env → Env → Prop where
| done : Extend ε ε
| alloc : Extend ε ε' → (sig A s t, ε') ⇓ (v,ε'') → Extend ε ε''
| newchan : Extend ε ε' → (newchan A, ε') ⇓ (v,ε'') → Extend ε ε''

lemma Extend.trans {ε ε' ε''} :
    Extend ε ε' → Extend ε' ε'' → Extend ε ε'' := by
  intro h1 h2
  induction h2 with
  | done => exact h1
  | alloc _ R IH => exact Extend.alloc IH R
  | newchan _ R IH => exact Extend.newchan IH R

lemma Extend.alloc_insert {σ Δ A v w} :
    Extend (σ ⧸ Δ) (σ.insert σ.alloc ⟨A, v, false, w⟩ σ.alloc_fresh ⧸ Δ) :=
  Extend.alloc Extend.done (Eval.sig (Eval.value v.2) (Eval.value w.2))

-- Every evaluation realizes an `Extend`
lemma Eval.extend : (t, ε) ⇓ (v, ε') → Extend ε ε' := by
  suffices T : ∀ {C D}, C ⇓ D → Extend C.2 D.2 by apply T
  intro C D R
  induction R with
  | value _ => exact Extend.done
  | newchan => exact Extend.newchan Extend.done Eval.newchan
  | sig _ _ IH1 IH2 => exact Extend.trans (IH1.trans IH2) Extend.alloc_insert
  | in1 _ IH | in2 _ IH | pr1 _ IH | pr2 _ IH | wait _ IH | watch _ IH
  | tail _ IH | fix _ IH | cons _ IH | head _ _ IH => exact IH
  | pair _ _ IH1 IH2 | appE _ _ IH1 IH2 | case1 _ _ IH1 IH2 | case2 _ _ IH1 IH2
  | select _ _ IH1 IH2 | appA _ _ IH1 IH2 => exact IH1.trans IH2
  | app _ _ _ IH1 IH2 IH3 | recur _ _ _ IH1 IH2 IH3 => exact (IH1.trans IH2).trans IH3

-- A single evaluation step preserves `TickConsistent`.
lemma TickConsistent.eval {η ε ε' κ t v} :
    (t, ε) ⇓ (v, ε') → TickConsistent η ε κ → TickConsistent η ε' κ := by
  intro R h
  have hle := Eval.incr R
  intro l s hs
  rcases h l s hs with hmem | ⟨hlnow, hrefs, hcons⟩
  · refine Or.inl ?_
    have he : ε.earlier = ε'.earlier := hle.store.earlier
    rwa [he] at hmem
  · exact Or.inr (TickConsistent.processed_mono hle.store.now hlnow hrefs hcons)

-- A single evaluation step preserves `NowInv`

lemma NowInv.eval {η ε ε' t v} :
    (t, ε) ⇓ (v, ε') → NowInv η ε → NowInv η ε' := by
  intro R h
  obtain ⟨hsub, hfresh⟩ := h
  have hle := Eval.incr R
  refine ⟨?_, ?_⟩
  · intro l s hs
    apply hsub l s
    have he : ε.earlier = ε'.earlier := hle.store.earlier
    rwa [he]
  · intro l hl
    rintro ⟨s2, hs2, ht2⟩
    by_cases hlN : l ∈ ε.now
    · rw [AList.lookup_eq_of_le_mem hle.store.now hlN] at hs2
      exact hfresh l hl ⟨s2, hs2, ht2⟩
    · exact Eval.now_fresh_unticked R l s2 hs2 hlN ht2

lemma TickConsistent.extend {η ε ε' κ} :
    Extend ε ε' → TickConsistent η ε κ → TickConsistent η ε' κ := by
  intro ex h
  induction ex with
  | done => exact h
  | alloc _ R IH | newchan _ R IH => exact IH.eval R

lemma NowInv.extend {η ε ε'} :
    Extend ε ε' → NowInv η ε → NowInv η ε' := by
  intro ex h
  induction ex with
  | done => exact h
  | alloc _ R IH | newchan _ R IH => exact IH.eval R


-- Ticked/mclock correspondence under an extended environment
lemma ticked_mclock_ext {Δ η D e ε u A} :
    ⊢[Δ] η ∷now → ⊢{ε'} u ∷ A →
    (∅ ✓[D] η ⧸ Δ) [e]⇒* ε →
    Extend ε ε' →
    (u.ticked ε'.now e.chan ↔
      (.chan e.chan ∈ mclock η u ∨ ∃ l, .loc l ∈ mclock η u ∧ freshSome ε'.now l)) := by
  intro Tη Tu steps ex
  have htc : TickConsistent η ε' e.chan :=
    (TickConsistent.preserves Tη steps EarlierPrefix.start TickConsistent.start).extend ex
  have hni : NowInv η ε' := (NowInv.preserves steps NowInv.start).extend ex
  have htr : TailReach η ε' u := fun l hl => by
    refine ⟨Tu.term_wf l hl, ?_⟩
    by_cases hlη : l ∈ η
    · exact Or.inl hlη
    · exact Or.inr (hni.2 l hlη)
  exact TickConsistent.ticked_mclock η u Tη htc htr


--------------------------------------------------
-- Proposition 5.10: ticked-mclock correspondence --
--------------------------------------------------

theorem ticked_mclock {Δ η D e ε u A t v} :
    ⊢[Δ] η ∷now → ⊢{ε'} u ∷ A →
    (∅ ✓[D] η ⧸ Δ) [e]⇒* ε →
    (t, ε) ⇓ (v, ε') →
    (u.ticked ε'.now e.chan ↔
      (.chan e.chan ∈ mclock η u ∨ ∃ l, .loc l ∈ mclock η u ∧ freshSome ε'.now l)) :=
  fun Tη Tu steps R => ticked_mclock_ext Tη Tu steps R.extend



inductive ClockElem where
  | chan : Chan → ClockElem
  | sig : Term → ClockElem
deriving DecidableEq


--  clock
abbrev Clock := Finset ClockElem


----------------------------------------
-- The clock of a delayed computation --
-- (Defined in sect. 2.2)             --
----------------------------------------

def clock : Term → Clock
  | .wait (.chan κ) => {.chan κ}
  | .watch s => {.sig s}
  | .select s t => clock s ∪ clock t
  | .appE _ t => clock t
  | _ => ∅


------------------------------------------------------------------
-- Heap substitution, unfolded as a left fold of `locSigSub` over --
-- the heap entries.  This gives clean structural equations for   --
-- how `heapSub` distributes over the term constructors.          --
------------------------------------------------------------------

def locListSub (t : Term) : List (Σ _ : Loc, Sig) → Term
  | [] => t
  | e :: es => locListSub (t.locSigSub e.1 e.2.type e.2.head e.2.tail) es

lemma heapSub_eq_locListSub : ∀ (es : List (Σ _ : Loc, Sig)) (N : es.NodupKeys) (t : Term),
    t.heapSub ⟨es, N⟩ = locListSub t es
  | [], _, _ => by simp only [Term.heapSub, locListSub]
  | ⟨_, ⟨_, _, _, _⟩⟩ :: es, _, t => by
      simp only [Term.heapSub]; rw [heapSub_eq_locListSub es _ _]; rfl

lemma heapSub_eq_locListSub' (t : Term) (η : Heap) : t.heapSub η = locListSub t η.entries := by
  rcases η with ⟨es, N⟩; exact heapSub_eq_locListSub es N t

-- `locListSub` distributes over each term constructor that `clock` inspects,
-- and preserves the (non-`loc`) machine-value constructors.
lemma locListSub_chan {κ} : ∀ es, locListSub (Term.chan κ) es = Term.chan κ
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_chan es
lemma locListSub_unit : ∀ es, locListSub Term.unit es = Term.unit
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_unit es
lemma locListSub_never : ∀ es, locListSub Term.never es = Term.never
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_never es
lemma locListSub_wait {t} : ∀ es, locListSub (Term.wait t) es = Term.wait (locListSub t es)
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_wait es
lemma locListSub_watch {t} : ∀ es, locListSub (Term.watch t) es = Term.watch (locListSub t es)
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_watch es
lemma locListSub_lam {t} : ∀ es, locListSub (Term.lam t) es = Term.lam (locListSub t es)
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_lam es
lemma locListSub_in1 {t} : ∀ es, locListSub (Term.in1 t) es = Term.in1 (locListSub t es)
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_in1 es
lemma locListSub_in2 {t} : ∀ es, locListSub (Term.in2 t) es = Term.in2 (locListSub t es)
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_in2 es
lemma locListSub_delay {t} : ∀ es, locListSub (Term.delay t) es = Term.delay (locListSub t es)
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_delay es
lemma locListSub_cons {A t} : ∀ es, locListSub (Term.cons A t) es = Term.cons A (locListSub t es)
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_cons es
lemma locListSub_pair {s t} : ∀ es, locListSub (Term.pair s t) es = Term.pair (locListSub s es) (locListSub t es)
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_pair es
lemma locListSub_sig {A s t} : ∀ es, locListSub (Term.sig A s t) es = Term.sig A (locListSub s es) (locListSub t es)
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_sig es
lemma locListSub_select {s t} : ∀ es, locListSub (Term.select s t) es = Term.select (locListSub s es) (locListSub t es)
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_select es
lemma locListSub_appE {a t} : ∀ es, locListSub (Term.appE a t) es = Term.appE (locListSub a es) (locListSub t es)
  | [] => rfl | _ :: es => by simp only [locListSub, Term.locSigSub]; exact locListSub_appE es

-- A stored location unfolds to the substituted (expanded) signal below it.
lemma locListSub_loc_some {l s} : ∀ es, List.dlookup l es = some s →
    locListSub (Term.loc l) es = locListSub (Term.sig s.type s.head s.tail) (afterLoc l es)
  | [], h => by simp [List.dlookup] at h
  | ⟨k, _⟩ :: es, h => by
      by_cases hkl : k = l
      · subst hkl
        simp only [List.dlookup, dite_eq_ite, if_true, Option.some.injEq] at h
        subst h; simp only [locListSub, Term.locSigSub, afterLoc, if_true]
      · have hne : l ≠ k := fun e => hkl e.symm
        simp only [locListSub, Term.locSigSub, if_neg hne, afterLoc, if_neg hkl]
        exact locListSub_loc_some es (by simpa [List.dlookup, hkl] using h)

-- An absent location is left untouched.
lemma locListSub_loc_none {l} : ∀ es, List.dlookup l es = none → locListSub (Term.loc l) es = Term.loc l
  | [], _ => rfl
  | ⟨k, _⟩ :: es, h => by
      by_cases hkl : k = l
      · subst hkl; simp [List.dlookup] at h
      · have hne : l ≠ k := fun e => hkl e.symm
        simp only [locListSub, Term.locSigSub, if_neg hne]
        exact locListSub_loc_none es (by simpa [List.dlookup, hkl] using h)

-- The tail of a stored location unfolds directly to the stored tail below it.
lemma locListSub_tailLoc_some {l s} : ∀ es, List.dlookup l es = some s →
    locListSub (Term.tail (Term.loc l)) es = locListSub s.tail.val (afterLoc l es)
  | [], h => by simp [List.dlookup] at h
  | ⟨k, _⟩ :: es, h => by
      by_cases hkl : k = l
      · subst hkl
        simp only [List.dlookup, dite_eq_ite, if_true, Option.some.injEq] at h
        subst h; simp only [locListSub, Term.locSigSub_tail_loc, afterLoc, if_true]
      · have hne : l ≠ k := fun e => hkl e.symm
        simp only [locListSub, Term.locSigSub_tail_loc, if_neg hne, afterLoc, if_neg hkl]
        exact locListSub_tailLoc_some es (by simpa [List.dlookup, hkl] using h)

-- The tail of an absent location is left untouched.
lemma locListSub_tailLoc_none {l} : ∀ es, List.dlookup l es = none →
    locListSub (Term.tail (Term.loc l)) es = Term.tail (Term.loc l)
  | [], _ => rfl
  | ⟨k, _⟩ :: es, h => by
      by_cases hkl : k = l
      · subst hkl; simp [List.dlookup] at h
      · have hne : l ≠ k := fun e => hkl e.symm
        simp only [locListSub, Term.locSigSub_tail_loc, if_neg hne]
        exact locListSub_tailLoc_none es (by simpa [List.dlookup, hkl] using h)

lemma keys_afterLoc_sub {l : Loc} {rest : List (Σ _ : Loc, Sig)} {x} :
    x ∈ (afterLoc l rest).keys → x ∈ rest.keys :=
  fun h => (List.Sublist.map _ (afterLoc_sublist l rest)).mem h

-- Substituting the whole heap and substituting only its tail below `l`
-- agree on a location `l'` that already lives below `l`: the entries
-- preceding it never mention it.
lemma locListSub_loc_skip {l l'} : ∀ (es : List (Σ _ : Loc, Sig)), es.NodupKeys →
    l' ∈ (afterLoc l es).keys → locListSub (Term.loc l') es = locListSub (Term.loc l') (afterLoc l es)
  | [], _, h => by simp [afterLoc] at h
  | ⟨k, _⟩ :: rest, N, h => by
      rw [List.nodupKeys_cons] at N
      obtain ⟨hknr, Nrest⟩ := N
      by_cases hkl : k = l
      · subst hkl
        rw [afterLoc, if_pos rfl] at h ⊢
        simp only [locListSub, Term.locSigSub, if_neg (fun e => hknr (e ▸ h) : l' ≠ k)]
      · rw [afterLoc, if_neg hkl] at h ⊢
        simp only [locListSub, Term.locSigSub, if_neg (fun e => hknr (e ▸ keys_afterLoc_sub h) : l' ≠ k)]
        exact locListSub_loc_skip rest Nrest h

-- Heap-level restatements of the fold equations.
lemma heapSub_chan {κ} {η : Heap} : (Term.chan κ).heapSub η = Term.chan κ := by
  rw [heapSub_eq_locListSub', locListSub_chan]
lemma heapSub_unit {η : Heap} : Term.unit.heapSub η = Term.unit := by
  rw [heapSub_eq_locListSub', locListSub_unit]
lemma heapSub_never {η : Heap} : Term.never.heapSub η = Term.never := by
  rw [heapSub_eq_locListSub', locListSub_never]
lemma heapSub_wait {t} {η : Heap} : (Term.wait t).heapSub η = Term.wait (t.heapSub η) := by
  rw [heapSub_eq_locListSub', locListSub_wait, ← heapSub_eq_locListSub']
lemma heapSub_watch {t} {η : Heap} : (Term.watch t).heapSub η = Term.watch (t.heapSub η) := by
  rw [heapSub_eq_locListSub', locListSub_watch, ← heapSub_eq_locListSub']
lemma heapSub_lam {t} {η : Heap} : (Term.lam t).heapSub η = Term.lam (t.heapSub η) := by
  rw [heapSub_eq_locListSub', locListSub_lam, ← heapSub_eq_locListSub']
lemma heapSub_in1 {t} {η : Heap} : (Term.in1 t).heapSub η = Term.in1 (t.heapSub η) := by
  rw [heapSub_eq_locListSub', locListSub_in1, ← heapSub_eq_locListSub']
lemma heapSub_in2 {t} {η : Heap} : (Term.in2 t).heapSub η = Term.in2 (t.heapSub η) := by
  rw [heapSub_eq_locListSub', locListSub_in2, ← heapSub_eq_locListSub']
lemma heapSub_delay {t} {η : Heap} : (Term.delay t).heapSub η = Term.delay (t.heapSub η) := by
  rw [heapSub_eq_locListSub', locListSub_delay, ← heapSub_eq_locListSub']
lemma heapSub_cons {A t} {η : Heap} : (Term.cons A t).heapSub η = Term.cons A (t.heapSub η) := by
  rw [heapSub_eq_locListSub', locListSub_cons, ← heapSub_eq_locListSub']
lemma heapSub_pair {s t} {η : Heap} : (Term.pair s t).heapSub η = Term.pair (s.heapSub η) (t.heapSub η) := by
  rw [heapSub_eq_locListSub', locListSub_pair, ← heapSub_eq_locListSub', ← heapSub_eq_locListSub']
lemma heapSub_sig {A s t} {η : Heap} : (Term.sig A s t).heapSub η = Term.sig A (s.heapSub η) (t.heapSub η) := by
  rw [heapSub_eq_locListSub', locListSub_sig, ← heapSub_eq_locListSub', ← heapSub_eq_locListSub']
lemma heapSub_select {s t} {η : Heap} : (Term.select s t).heapSub η = Term.select (s.heapSub η) (t.heapSub η) := by
  rw [heapSub_eq_locListSub', locListSub_select, ← heapSub_eq_locListSub', ← heapSub_eq_locListSub']
lemma heapSub_appE {a t} {η : Heap} : (Term.appE a t).heapSub η = Term.appE (a.heapSub η) (t.heapSub η) := by
  rw [heapSub_eq_locListSub', locListSub_appE, ← heapSub_eq_locListSub', ← heapSub_eq_locListSub']

lemma heapSub_loc_none {l} {η : Heap} (h : η.lookup l = none) : (Term.loc l).heapSub η = Term.loc l := by
  rw [heapSub_eq_locListSub']; exact locListSub_loc_none η.entries h
lemma heapSub_loc_some {l s} {η : Heap} (h : η.lookup l = some s) :
    (Term.loc l).heapSub η = (Term.sig s.type s.head s.tail).heapSub (η.below l) := by
  rw [heapSub_eq_locListSub', heapSub_eq_locListSub']; exact locListSub_loc_some η.entries h

lemma heapSub_tailLoc_none {l} {η : Heap} (h : η.lookup l = none) :
    (Term.tail (Term.loc l)).heapSub η = Term.tail (Term.loc l) := by
  rw [heapSub_eq_locListSub']; exact locListSub_tailLoc_none η.entries h
lemma heapSub_tailLoc_some {l s} {η : Heap} (h : η.lookup l = some s) :
    (Term.tail (Term.loc l)).heapSub η = s.tail.val.heapSub (η.below l) := by
  rw [heapSub_eq_locListSub', heapSub_eq_locListSub']; exact locListSub_tailLoc_some η.entries h
lemma heapSub_below_stable {η : Heap} {l l'} (h : l' ∈ η.below l) :
    (Term.loc l').heapSub η = (Term.loc l').heapSub (η.below l) := by
  rw [heapSub_eq_locListSub', heapSub_eq_locListSub']
  exact locListSub_loc_skip η.entries η.nodupKeys (AList.mem_keys.mp h)

-- Heap-substituting a `loc` never yields a `clock`-relevant term.
lemma clock_heapSub_loc {l} {η : Heap} : clock ((Term.loc l).heapSub η) = ∅ := by
  cases hl : η.lookup l with
  | none => rw [heapSub_loc_none hl]; rfl
  | some s => rw [heapSub_loc_some hl, heapSub_sig]; rfl

----------------------------------------------------------
-- `MClock.heapSub` sends a machine clock to a clock by  --
-- applying `Term.heapSub` to each stored location.      --
----------------------------------------------------------

def MClock.heapSub (cl : MClock) (η : Heap) : Clock :=
  cl.image (fun e => match e with
    | .chan κ => ClockElem.chan κ
    | .loc l => ClockElem.sig ((Term.loc l).heapSub η))

@[simp] lemma MClock.heapSub_empty {η : Heap} : MClock.heapSub ∅ η = ∅ :=
  Finset.image_empty _
lemma MClock.heapSub_union {a b : MClock} {η : Heap} :
    MClock.heapSub (a ∪ b) η = MClock.heapSub a η ∪ MClock.heapSub b η := by
  simp only [MClock.heapSub, Finset.image_union]
lemma MClock.heapSub_chan {κ} {η : Heap} :
    MClock.heapSub {MClockElem.chan κ} η = {ClockElem.chan κ} := by simp [MClock.heapSub]
lemma MClock.heapSub_loc {l} {η : Heap} :
    MClock.heapSub {MClockElem.loc l} η = {ClockElem.sig ((Term.loc l).heapSub η)} := by
  simp [MClock.heapSub]

-- If a machine clock only mentions locations below `l₀`, then substituting
-- against the whole heap and against its tail below `l₀` coincide.
lemma MClock.heapSub_below_congr {cl : MClock} {η : Heap} {l₀ : Loc}
    (H : ∀ l', MClockElem.loc l' ∈ cl →
      (Term.loc l').heapSub η = (Term.loc l').heapSub (η.below l₀)) :
    MClock.heapSub cl η = MClock.heapSub cl (η.below l₀) := by
  apply Finset.image_congr
  intro e he
  cases e with
  | chan κ => rfl
  | loc l' => exact congrArg ClockElem.sig (H l' he)

-- The locations appearing in a machine clock of a well-typed term all live
-- in the heap.
lemma mclock_loc_mem {Δ} : ∀ (η : Heap) (p : Term),
    ⊢[Δ] η ∷now → (∃ A, ⊢[Δ, η.type] p ∷ A) →
    ∀ l', MClockElem.loc l' ∈ mclock η p → l' ∈ η := by
  intro η p
  induction η, p using mclock.induct
  next x κ =>
    intro _ _ l' hl'; simp [mclock] at hl'
  next x l =>
    intro _ hty l' hl'
    obtain ⟨A, hty⟩ := hty
    simp only [mclock, Finset.mem_singleton, MClockElem.loc.injEq] at hl'
    rw [hl']; exact hty.term_wf l (by simp [Term.refs])
  next η s t ihs iht =>
    intro hnow hty l' hl'
    obtain ⟨A, hty⟩ := hty
    cases hty with | select _ _ Ts Tt =>
    simp only [mclock, Finset.mem_union] at hl'
    rcases hl' with h | h
    · exact ihs hnow ⟨_, Ts⟩ l' h
    · exact iht hnow ⟨_, Tt⟩ l' h
  next η a t iht =>
    intro hnow hty l' hl'
    obtain ⟨A, hty⟩ := hty
    cases hty with | appE Ta Tt =>
    simp only [mclock] at hl'
    exact iht hnow ⟨_, Tt⟩ l' hl'
  next η l s hlook ih =>
    intro hnow _ l' hl'
    obtain ⟨hbelow, htl⟩ := hnow.below_inv l s hlook
    have hmc : mclock η (Term.tail (Term.loc l)) = mclock (η.below l) s.tail.val := by
      simp only [mclock]; rw [hlook]
    rw [hmc] at hl'
    exact AList.le.mem Heap.below_le (ih hbelow ⟨_, htl⟩ l' hl')
  next η l hlook =>
    intro _ _ l' hl'
    have hmc : mclock η (Term.tail (Term.loc l)) = ∅ := by simp only [mclock]; rw [hlook]
    rw [hmc] at hl'; simp at hl'
  next x u hw hwt hs ha ht =>
    intro _ _ l' hl'
    cases u <;> simp_all [mclock]

--------------------------------------------
-- Proposition 5.11: clock correspondence --
--------------------------------------------

theorem clock_mclock {Δ η p A} (hv : IsMValue p) (hη : ⊢[Δ] η ∷now)
    (hp : ⊢[Δ, η.type] p ∷ A) : (mclock η p).heapSub η = clock (p.heapSub η) := by
  suffices key : ∀ (η : Heap) (p : Term), IsMValue p → ⊢[Δ] η ∷now →
      (∃ A, ⊢[Δ, η.type] p ∷ A) → (mclock η p).heapSub η = clock (p.heapSub η) by
    exact key η p hv hη ⟨A, hp⟩
  intro η p
  induction η, p using mclock.induct
  -- wait (chan κ)
  next x κ =>
    intro _ _ _
    simp only [mclock, MClock.heapSub_chan, heapSub_wait, heapSub_chan, clock]
  -- watch (loc l)
  next x l =>
    intro _ _ _
    simp only [mclock, MClock.heapSub_loc, heapSub_watch, clock]
  -- select s t
  next η s t ihs iht =>
    intro hmv hnow hty
    obtain ⟨A, hty⟩ := hty
    cases hmv with | select hs' ht' =>
    cases hty with | select _ _ Ts Tt =>
    have IHs := ihs hs' hnow ⟨_, Ts⟩
    have IHt := iht ht' hnow ⟨_, Tt⟩
    simp only [mclock, MClock.heapSub_union, heapSub_select, clock]
    rw [IHs, IHt]
  -- appE a t
  next η a t iht =>
    intro hmv hnow hty
    obtain ⟨A, hty⟩ := hty
    cases hmv with | appE ha' ht' =>
    cases hty with | appE Ta Tt =>
    have IHt := iht ht' hnow ⟨_, Tt⟩
    simp only [mclock, heapSub_appE, clock]
    exact IHt
  -- tail (loc l), signal present
  next η l s hlook ih =>
    intro _ hnow _
    obtain ⟨hbelow, htl⟩ := hnow.below_inv l s hlook
    have IH := ih s.tail.property hbelow ⟨_, htl⟩
    have hmc : mclock η (Term.tail (Term.loc l)) = mclock (η.below l) s.tail.val := by
      simp only [mclock]; rw [hlook]
    rw [hmc, MClock.heapSub_below_congr (fun l' hl' =>
      heapSub_below_stable (mclock_loc_mem (η.below l) s.tail.val hbelow ⟨_, htl⟩ l' hl')),
      IH, heapSub_tailLoc_some hlook]
  -- tail (loc l), signal absent
  next η l hlook =>
    intro _ _ _
    have hmc : mclock η (Term.tail (Term.loc l)) = ∅ := by simp only [mclock]; rw [hlook]
    rw [hmc, MClock.heapSub_empty, heapSub_tailLoc_none hlook]
    rfl
  -- everything else: both sides empty
  next x u hw hwt hs ha ht =>
    intro hmv _ hty
    obtain ⟨A, hty⟩ := hty
    cases u with
    | select a b => exact (hs a b rfl).elim
    | appE a b => exact (ha a b rfl).elim
    | wait t' =>
      cases hmv with | wait => exact (hw _ rfl).elim
    | watch t' =>
      cases hmv with | watch => exact (hwt _ rfl).elim
    | tail t' =>
      cases hmv with | tail => exact (ht _ rfl).elim
    | loc l => simp only [mclock, MClock.heapSub_empty, clock_heapSub_loc]
    | _ =>
      -- machine values: both sides reduce to `∅`; non-values: `hmv` is absurd
      simp only [mclock, MClock.heapSub_empty, heapSub_unit, heapSub_lam, heapSub_in1,
          heapSub_in2, heapSub_pair, heapSub_delay, heapSub_never, heapSub_cons,
          heapSub_chan, clock] <;>
        exact absurd hmv (by rintro ⟨⟩)
