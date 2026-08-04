/-
Definition of the typing relation
-/

import Rizzo.Env
import Rizzo.Terms


open Term
open Typ


abbrev Ctx : Type := List Typ

---------------------------
-- Typing rules of Rizzo --
-- (Fig. 3 & sect. 4.5)  --
---------------------------

-- `HasType` (denoted `Γ ⊢[Δ,H] t ∷ A`) is the general typing
-- judgement (introduced in sect 4.5) that includes a heap typing
-- context `H`. The typing judgement in Fig. 3 is the special case
-- where `H = ∅` (denoted `Γ ⊢[Δ] t ∷ A`).


inductive HasType (H : HeapTy) (Δ : ChanCtx) : Ctx → Term → Typ → Prop where
| unit : HasType H Δ Γ unit 𝟭
| lam : A.Closed → HasType H Δ (A :: Γ) t B → HasType H Δ Γ (lam t) (A ⟶ B)
| var : A ∈ Γ[x]? → HasType H Δ Γ (var x) A
| loc : A ∈ H.lookup l → HasType H Δ Γ (.loc l) (sig A)
| chan : A ∈ Δ.lookup κ → HasType H Δ Γ (.chan κ) (chan A)
| sig : HasType H Δ Γ s A → HasType H Δ Γ t (◯ (sig A)) → HasType H Δ Γ (sig A s t) (sig A)
| app : HasType H Δ Γ s (A ⟶ B) → HasType H Δ Γ t A → HasType H Δ Γ (app s t) B
| appA : HasType H Δ Γ s (□ (A ⟶ B)) → HasType H Δ Γ t (□ A) → HasType H Δ Γ (appA s t) (□ B)
| appE : HasType H Δ Γ s (□ (A ⟶ B)) → HasType H Δ Γ t (◯ A) → HasType H Δ Γ (appE s t) (◯ B)
| in1 : B.Closed → HasType H Δ Γ t A → HasType H Δ Γ (in1 t) (A ⨁ B)
| in2 : A.Closed → HasType H Δ Γ t B → HasType H Δ Γ (in2 t) (A ⨁ B)
| case : A1.Closed → A2.Closed → HasType H Δ Γ t (A1 ⨁ A2) → HasType H Δ (A1 :: Γ) t1 B
       → HasType H Δ (A2 :: Γ) t2 B → HasType H Δ Γ (Term.case t t1 t2) B
| pair : HasType H Δ Γ s A → HasType H Δ Γ t B → HasType H Δ Γ (pair s t) (A ⨂ B)
| pr1 : HasType H Δ Γ t (A ⨂ B) → HasType H Δ Γ (pr1 t) A
| pr2 : HasType H Δ Γ t (A ⨂ B) → HasType H Δ Γ (pr2 t) B
| delay : HasType H Δ Γ t A → HasType H Δ Γ (delay t) (□ A)
| never : A.Closed → HasType H Δ Γ never (◯ A)
| newchan : A.Closed → HasType H Δ Γ (newchan A) (chan A)
| wait : HasType H Δ Γ t (chan A) → HasType H Δ Γ (wait t) (◯ A)
| select : A.Closed → B.Closed → HasType H Δ Γ s (◯ A) → HasType H Δ Γ t (◯ B) → HasType H Δ Γ (select s t) (◯ ((A ⨁ B) ⨁ (A ⨂ B)))
| cons : (μ A).Closed → HasType H Δ Γ t (A.sub (μ A)) → HasType H Δ Γ (cons A t) (μ A)
| recur : (μ A).Closed → B.Closed → HasType H Δ (A.sub ((μ A) ⨂ B) :: Γ) s B → HasType H Δ Γ t (μ A) → HasType H Δ Γ (recur B s t) B
| fix : A.Closed → HasType H Δ (□ A :: Γ) t A → HasType H Δ Γ (fix t) A
| head : HasType H Δ Γ t (sig A) → HasType H Δ Γ (head t) A
| tail : HasType H Δ Γ t (sig A) → HasType H Δ Γ (tail t) (◯ (sig A))
| watch : HasType H Δ Γ t (sig (A ⨁ 𝟭)) → HasType H Δ Γ (watch t) (◯ A)

notation:50 (name := has_type)        Γ:60 " ⊢[" Δ ", " H "] " t:60 " ∷ " A:60 => HasType H Δ Γ t A
notation:50 (name := has_type_cl)          " ⊢[" Δ ", " H "] " t:60 " ∷ " A:60 => HasType H Δ [] t A
notation:50 (name := has_type_noH)    Γ:60 " ⊢[" Δ "] "        t:60 " ∷ " A:60 => HasType ∅ Δ Γ t A
notation:50 (name := has_type_noH_cl)      " ⊢[" Δ "] "        t:60 " ∷ " A:60 => HasType ∅ Δ [] t A
notation:50 (name := has_type_noD)    Γ:60 " ⊢[," H "] "       t:60 " ∷ " A:60 => HasType H ∅ Γ t A
notation:50 (name := has_type_noD_cl)      " ⊢[," H "] "       t:60 " ∷ " A:60 => HasType H ∅ [] t A
notation:50 (name := has_type_emp)    Γ:60 " ⊢ "               t:60 " ∷ " A:60 => HasType ∅ ∅ Γ t A
notation:50 (name := has_type_emp_cl)      " ⊢ "               t:60 " ∷ " A:60 => HasType ∅ ∅ [] t A

-- Env shorthands: H and Δ are taken from the environment ε (written ⊢{ε}).
notation:50 (name := has_type_env)    Γ:60 " ⊢{" ε "} " t:60 " ∷ " A:60 => HasType (Heap.type (Env.now ε)) (Env.chans ε) Γ t A
notation:50 (name := has_type_env_cl)      " ⊢{" ε "} " t:60 " ∷ " A:60 => HasType (Heap.type (Env.now ε)) (Env.chans ε) [] t A


---------------------------------
-- 'now' heap typing judgement --
--- denoted `⊢[Δ] η ∷now`      --
-- (Fig. 9)                    --
---------------------------------

inductive IsHeap : ChanCtx → Heap → Prop where
| nil : IsHeap Δ ∅
| cons :
  IsHeap Δ ⟨η, M⟩ →
  ⊢[Δ, Heap.type ⟨η, M⟩] hd.val ∷ A →
  ⊢[Δ, Heap.type ⟨η, M⟩] tl.val ∷ ◯ (sig A) →
  IsHeap Δ ⟨⟨l, ⟨A, hd, a, tl⟩⟩ :: η, N⟩


notation:80 (name := is_heap_notation) "⊢[" Δ "] " η:90 " ∷now" => IsHeap Δ η


@[simp]
def IsNowEnv (ε : Env) := ⊢[ε.chans] ε.store.now ∷now


notation:80 (name := is_now_env_notation) "⊩" ε:90 " ∷Env" => IsNowEnv ε


@[grind]
structure EvalType (ε : Env) (Γ : Ctx) (t : Term)  (A : Typ) : Prop where
  mk ::
  term : Γ ⊢{ε} t ∷  A
  env : ⊩ ε ∷Env

notation:80 (name := eval_type_notation') Γ:91 " ⊩{" ε "} " t:90 " ∷ " A:90 => EvalType ε Γ t A
notation:80 (name := eval_type_notation) " ⊩{" ε "} " t:90 " ∷ " A:90 => EvalType ε [] t A

-----------------------------
-- event typing judgement  --
-- denoted `⊢[Δ] e ∷Event` --
-- (Fig. 8)                --
-----------------------------

def IsEvent Δ (e : Event) := ∃ A ∈ Δ.lookup e.chan, ⊢[Δ] e.val ∷ A

notation:80 (name := is_event_notation) "⊢[" Δ "] " e:90 " ∷Event" => IsEvent Δ e



--------------------------------------
-- 'earlier' heap typing judgement  --
-- denoted `⊢[Δ,H] η ∷earlier`      --
-- (Fig. 9)                         --
--------------------------------------

inductive IsEarlierHeap (Δ : ChanCtx) : HeapTy → Heap → Prop where
| nil : IsEarlierHeap Δ H ∅
| cons :
  IsEarlierHeap Δ (H.cons l s.type p) η →
  ⊢[Δ, H] s.head ∷ s.type →
  ⊢[Δ, H] s.tail ∷ ◯ (.sig s.type) →
  IsEarlierHeap Δ H (η.concat l s p')

notation:80 (name := is_earlier_heap_notation) "⊢[" Δ ", " H "] " η:90 " ∷earlier" => IsEarlierHeap Δ H η
notation:80 (name := is_earlier_heap_notation') "⊢[" Δ "] " η:90 " ∷earlier" => IsEarlierHeap Δ ∅ η


----------------------------------
-- environment typing judgement --
-- denoted `⊢ ε ∷Env`           --
-- (Fig. 9)                     --
----------------------------------

def IsEnv (ε : Env) := ⊩ ε ∷Env /\ ⊢[ε.chans, ε.now.type] ε.earlier ∷earlier
notation:50 (name := is_env_notation) " ⊢ " ε:60 " ∷Env" => IsEnv ε

-- well-typed signals stored on the heap

structure SigType (η : Heap) (Δ : ChanCtx) (s : Sig) : Prop where
  head : ⊢[Δ, η.type] s.head ∷ s.type
  tail : ⊢[Δ, η.type] s.tail ∷ ◯ (.sig s.type)

notation:80 (name := sig_type_notation) "⊢[" Δ ", " η "] " s:90 " ∷Sig" => SigType η Δ s

---------------------------------------
-- Lemmas about the typing relations --
---------------------------------------
@[simp]
lemma SigType.tick : ⊢[Δ, η] s ∷Sig → ⊢[Δ, η] s.tick ∷Sig := by
  intro T; cases T; solve_by_elim

lemma HasType.lam_inv  : Γ ⊢[Δ, H] t.lam ∷ A ⟶ B → (A :: Γ) ⊢[Δ, H] t ∷ B := by
  intro T
  cases T
  assumption


lemma HasType.app' {s} : Γ ⊢[Δ, H] t ∷ A → Γ ⊢[Δ, H] s ∷ A ⟶ B → Γ ⊢[Δ, H] s.app t ∷ B := by
  intros; solve_by_elim

lemma HasType.smap {A B : Typ} :
    A.Closed → B.Closed → Γ ⊢[Δ, H] smap B ∷ (A ⟶ B) ⟶ A.sig ⟶ B.sig := by
  intro hA hB
  simp only [Term.smap]
  apply HasType.lam (Typ.Wf.arr hA hB)
  apply HasType.fix (Typ.Wf.arr (Typ.Wf.sig hA) (Typ.Wf.sig hB))
  apply HasType.lam (Typ.Wf.sig hA)
  apply HasType.sig
  · exact HasType.app (HasType.var rfl) (HasType.head (HasType.var rfl))
  · exact HasType.appE (HasType.var rfl) (HasType.tail (HasType.var rfl))


-- Applying a `funcsTo`-typed term to its list of function arguments
-- yields the result type.
lemma HasType.apps : ∀ {Ss Cs} {fns : List Term} {e T},
    Γ ⊢[Δ, H] e ∷ Typ.funcsTo Ss Cs T → Ss.length = Cs.length → fns.length = Cs.length →
    (∀ i (hiS : i < Ss.length) (hiC : i < Cs.length) (hif : i < fns.length),
       Γ ⊢[Δ, H] fns[i]'hif ∷ Ss[i]'hiS ⟶ Cs[i]'hiC) →
    Γ ⊢[Δ, H] Term.apps e fns ∷ T := by
  intro Ss
  induction Ss with
  | nil =>
      intro Cs fns e T he hlen hflen _
      cases Cs with
      | nil => cases fns with
        | nil => simpa [Term.apps] using he
        | cons => simp at hflen
      | cons => simp at hlen
  | cons S Ss' ih =>
      intro Cs fns e T he hlen hflen hg
      cases Cs with
      | nil => simp at hlen
      | cons C Cs' =>
          cases fns with
          | nil => simp at hflen
          | cons f fns' =>
              simp only [Typ.funcsTo] at he
              simp only [Term.apps]
              have h0 : Γ ⊢[Δ, H] f ∷ S ⟶ C := by
                have := hg 0 (by simp) (by simp) (by simp); simpa using this
              refine ih (HasType.app' h0 he) (by simpa using hlen) (by simpa using hflen) ?_
              intro i hiS hiC hif
              have := hg (i + 1) (by simp only [List.length_cons]; omega)
                (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
              simpa using this

lemma HasType.nlam_funcsTo : ∀ {Ss Cs : List Typ} {body} {Sx : Typ} {Tx Γ},
    Ss.length = Cs.length →
    (∀ S ∈ Ss, S.Closed) → (∀ C ∈ Cs, C.Closed) → Sx.Closed →
    (Sx :: (List.zipWith (fun S C => S ⟶ C) Ss Cs).reverse ++ Γ) ⊢[Δ, H] body ∷ Tx →
    Γ ⊢[Δ, H] Term.nlam Cs.length (Term.lam body) ∷ Typ.funcsTo Ss Cs (Sx ⟶ Tx) := by
  intro Ss
  induction Ss with
  | nil =>
      intro Cs body Sx Tx Γ hlen hSc hCc hSx hb
      cases Cs with
      | nil => simp only [Term.nlam, Typ.funcsTo]; exact HasType.lam hSx (by simpa using hb)
      | cons => simp at hlen
  | cons S Ss' ih =>
      intro Cs body Sx Tx Γ hlen hSc hCc hSx hb
      cases Cs with
      | nil => simp at hlen
      | cons C Cs' =>
          simp only [Term.nlam, Typ.funcsTo]
          apply HasType.lam (Typ.Wf.arr (hSc S (by simp)) (hCc C (by simp)))
          apply ih (by simpa using hlen)
            (fun S' h => hSc S' (by simp [h])) (fun C' h => hCc C' (by simp [h])) hSx
          simpa [List.zipWith_cons_cons, List.reverse_cons, List.append_assoc] using hb


lemma HasType.zipWith_rev_get {Ss Cs : List Typ} {Sx Γ i} (hlen : Ss.length = Cs.length)
    (hiS : i < Ss.length) (hiC : i < Cs.length) :
    (Sx :: (List.zipWith (fun S C => S ⟶ C) Ss Cs).reverse ++ Γ)[Cs.length - i]?
      = some (Ss[i]'hiS ⟶ Cs[i]'hiC) := by
  have hlz : (List.zipWith (fun S C => S ⟶ C) Ss Cs).length = Cs.length := by
    simp [List.length_zipWith, hlen]
  obtain ⟨d, hd⟩ : ∃ d, Cs.length - i = d + 1 := ⟨Cs.length - i - 1, by omega⟩
  rw [hd, List.getElem?_append_left (by rw [List.length_cons, List.length_reverse, hlz]; omega),
      List.getElem?_cons_succ,
      List.getElem?_reverse (by rw [hlz]; omega), List.getElem?_zipWith]
  have e1 : (List.zipWith (fun S C => S ⟶ C) Ss Cs).length - 1 - d = i := by rw [hlz]; omega
  rw [e1, List.getElem?_eq_getElem hiS, List.getElem?_eq_getElem hiC]

lemma HasType.fmap_fns {Ss Cs : List Typ} {Sx Γ} (hlen : Ss.length = Cs.length)
    (i : Nat) (hiS : i < Ss.length) (hiC : i < Cs.length)
    (hif : i < ((List.range Cs.length).map (fun i => Term.var (Cs.length - i))).length) :
    (Sx :: (List.zipWith (fun S C => S ⟶ C) Ss Cs).reverse ++ Γ) ⊢[Δ, H]
      ((List.range Cs.length).map (fun i => Term.var (Cs.length - i)))[i]'hif
      ∷ Ss[i]'hiS ⟶ Cs[i]'hiC := by
  rw [List.getElem_map, List.getElem_range]
  exact HasType.var (HasType.zipWith_rev_get hlen hiS hiC)

lemma HasType.fmap_fns_shift {Ss Cs : List Typ} {Sx E Γ} (hlen : Ss.length = Cs.length)
    (i : Nat) (hiS : i < Ss.length) (hiC : i < Cs.length)
    (hif : i < ((List.range Cs.length).map (fun i => Term.var (Cs.length + 1 - i))).length) :
    (E :: Sx :: (List.zipWith (fun S C => S ⟶ C) Ss Cs).reverse ++ Γ) ⊢[Δ, H]
      ((List.range Cs.length).map (fun i => Term.var (Cs.length + 1 - i)))[i]'hif
      ∷ Ss[i]'hiS ⟶ Cs[i]'hiC := by
  rw [List.getElem_map, List.getElem_range]
  exact HasType.var (by
    rw [show Cs.length + 1 - i = (Cs.length - i) + 1 from by omega, List.cons_append,
        List.getElem?_cons_succ]
    exact HasType.zipWith_rev_get hlen hiS hiC)

lemma HasType.fmap : ∀ {A} {Ss Cs : List Typ} {Γ},
    Cs.length ⊢ A ∷type → Ss.length = Cs.length → (∀ S ∈ Ss, S.Closed) → (∀ C ∈ Cs, C.Closed) →
    Γ ⊢[Δ, H] fmap A Cs ∷ Typ.funcsTo Ss Cs (A.substAll Ss ⟶ A.substAll Cs) := by
  intro A
  induction A with
  | unit =>
      intro Ss Cs Γ hWf hlen hSc hCc
      have hSx := Typ.substAll_Wf_closed (Cs := Ss) (by rw [hlen]; exact hWf) hSc
      simp only [Term.fmap]
      apply HasType.nlam_funcsTo hlen hSc hCc hSx
      exact HasType.var rfl
  | var i =>
      intro Ss Cs Γ hWf hlen hSc hCc
      have hSx := Typ.substAll_Wf_closed (Cs := Ss) (by rw [hlen]; exact hWf) hSc
      cases hWf with | var hi =>
      have hiS : i < Ss.length := by omega
      simp only [Term.fmap]
      apply HasType.nlam_funcsTo hlen hSc hCc hSx
      rw [if_pos hi]
      have eS : (Typ.var i).substAll Ss = Ss[i]'hiS := by
        simp only [Typ.substAll, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiS, Option.getD_some]
      have eC : (Typ.var i).substAll Cs = Cs[i]'hi := by
        simp only [Typ.substAll, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      apply HasType.app'
      · exact HasType.var rfl
      · apply HasType.var
        rw [eS, eC]
        exact HasType.zipWith_rev_get hlen hiS hi
  | prod A1 A2 ih1 ih2 =>
      intro Ss Cs Γ hWf hlen hSc hCc
      have hSx := Typ.substAll_Wf_closed (Cs := Ss) (by rw [hlen]; exact hWf) hSc
      cases hWf with | prod WF1 WF2 =>
      simp only [Term.fmap]
      apply HasType.nlam_funcsTo hlen hSc hCc hSx
      apply HasType.pair
      · exact HasType.app' (HasType.pr1 (HasType.var rfl))
          (HasType.apps (ih1 WF1 hlen hSc hCc) hlen (by simp) (HasType.fmap_fns hlen))
      · exact HasType.app' (HasType.pr2 (HasType.var rfl))
          (HasType.apps (ih2 WF2 hlen hSc hCc) hlen (by simp) (HasType.fmap_fns hlen))
  | sum A1 A2 ih1 ih2 =>
      intro Ss Cs Γ hWf hlen hSc hCc
      have hSx := Typ.substAll_Wf_closed (Cs := Ss) (by rw [hlen]; exact hWf) hSc
      cases hWf with | sum WF1 WF2 =>
      simp only [Term.fmap]
      apply HasType.nlam_funcsTo hlen hSc hCc hSx
      apply HasType.case (Typ.substAll_Wf_closed (by rw [hlen]; exact WF1) hSc)
        (Typ.substAll_Wf_closed (by rw [hlen]; exact WF2) hSc) (HasType.var rfl)
      · apply HasType.in1 (Typ.substAll_Wf_closed WF2 hCc)
        exact HasType.app' (HasType.var rfl)
          (HasType.apps (ih1 WF1 hlen hSc hCc) hlen (by simp) (HasType.fmap_fns_shift hlen))
      · apply HasType.in2 (Typ.substAll_Wf_closed WF1 hCc)
        exact HasType.app' (HasType.var rfl)
          (HasType.apps (ih2 WF2 hlen hSc hCc) hlen (by simp) (HasType.fmap_fns_shift hlen))
  | arr A1 A2 _ ih2 =>
      intro Ss Cs Γ hWf hlen hSc hCc
      have hSx := Typ.substAll_Wf_closed (Cs := Ss) (by rw [hlen]; exact hWf) hSc
      cases hWf with | arr WF1 WF2 =>
      have hA1 : ∀ L : List Typ, A1.substAll L = A1 :=
        fun L => Typ.substAll_id WF1 (fun i h => (Nat.not_lt_zero i h).elim)
      simp only [Term.fmap]
      apply HasType.nlam_funcsTo hlen hSc hCc hSx
      -- BODY = lam ((apps (fmap A2 Cs) fns1).app ((var 1).app (var 0)))
      simp only [Typ.substAll, hA1]
      refine HasType.lam WF1 ?_
      exact HasType.app' (HasType.app' (HasType.var rfl) (HasType.var rfl))
        (HasType.apps (ih2 WF2 hlen hSc hCc) hlen (by simp) (HasType.fmap_fns_shift hlen))
  | delayA A' _ =>
      intro Ss Cs Γ hWf hlen hSc hCc
      have hSx := Typ.substAll_Wf_closed (Cs := Ss) (by rw [hlen]; exact hWf) hSc
      cases hWf with | delayA WF =>
      simp only [Term.fmap]
      apply HasType.nlam_funcsTo hlen hSc hCc hSx
      -- `□ A'` is closed, so `fmap` is the identity `var 0`.
      have e : (□ A').substAll Cs = (□ A').substAll Ss := by
        rw [Typ.substAll_id (Typ.Wf.delayA WF) (fun i h => (Nat.not_lt_zero i h).elim),
            Typ.substAll_id (Typ.Wf.delayA WF) (fun i h => (Nat.not_lt_zero i h).elim)]
      rw [e]; exact HasType.var rfl
  | delayE A' _ =>
      intro Ss Cs Γ hWf hlen hSc hCc
      have hSx := Typ.substAll_Wf_closed (Cs := Ss) (by rw [hlen]; exact hWf) hSc
      cases hWf with | delayE WF =>
      simp only [Term.fmap]
      apply HasType.nlam_funcsTo hlen hSc hCc hSx
      -- `◯ A'` is closed, so `fmap` is the identity `var 0`.
      have e : (◯ A').substAll Cs = (◯ A').substAll Ss := by
        rw [Typ.substAll_id (Typ.Wf.delayE WF) (fun i h => (Nat.not_lt_zero i h).elim),
            Typ.substAll_id (Typ.Wf.delayE WF) (fun i h => (Nat.not_lt_zero i h).elim)]
      rw [e]; exact HasType.var rfl
  | chan A' _ =>
      intro Ss Cs Γ hWf hlen hSc hCc
      have hSx := Typ.substAll_Wf_closed (Cs := Ss) (by rw [hlen]; exact hWf) hSc
      cases hWf with | chan WF =>
      simp only [Term.fmap]
      apply HasType.nlam_funcsTo hlen hSc hCc hSx
      have e : (Typ.chan A').substAll Cs = (Typ.chan A').substAll Ss := by
        rw [Typ.substAll_id (Typ.Wf.chan WF) (fun i h => (Nat.not_lt_zero i h).elim),
            Typ.substAll_id (Typ.Wf.chan WF) (fun i h => (Nat.not_lt_zero i h).elim)]
      rw [e]; exact HasType.var rfl
  | sig A' ih =>
      intro Ss Cs Γ hWf hlen hSc hCc
      have hSx := Typ.substAll_Wf_closed (Cs := Ss) (by rw [hlen]; exact hWf) hSc
      cases hWf with | sig WF =>
      simp only [Term.fmap]
      apply HasType.nlam_funcsTo hlen hSc hCc hSx
      -- BODY = ((smap (A'.substAll Cs)).app (apps (fmap A' Cs) fns)).app (var 0)
      apply HasType.app' (HasType.var rfl)
      apply HasType.app' (HasType.apps (ih WF hlen hSc hCc) hlen (by simp) (HasType.fmap_fns hlen))
      exact HasType.smap (Typ.substAll_Wf_closed (by rw [hlen]; exact WF) hSc)
        (Typ.substAll_Wf_closed WF hCc)
  | mu A' ih =>
      intro Ss Cs Γ hWf hlen hSc hCc
      have hSx := Typ.substAll_Wf_closed (Cs := Ss) (by rw [hlen]; exact hWf) hSc
      cases hWf with | mu W' =>
      -- Closedness of the source/target recursive types.
      have hmuC : ∀ (L : List Typ), (∀ C ∈ L, C.Closed) → L.length = Cs.length →
          (μ (A'.substAll (Typ.var 0 :: L.map (Typ.shift 0)))).Closed := by
        intro L hLc hLlen
        refine Typ.Wf.mu (Typ.substAll_Wf W' ?_)
        intro i hi
        cases i with
        | zero => exact ⟨Typ.var 0, rfl, Typ.Wf.var (by omega)⟩
        | succ j =>
            have hjL : j < L.length := by omega
            refine ⟨(L[j]'hjL).shift 0, ?_, (hLc _ (List.getElem_mem hjL)).shift (Nat.zero_le _)⟩
            rw [List.getElem?_cons_succ, List.getElem?_map, List.getElem?_eq_getElem hjL]; rfl
      have hcomm : ∀ (L : List Typ) (X : Typ), (∀ C ∈ L, C.Closed) → L.length = Cs.length →
          A'.substAll (X :: L.map (Typ.shift 0))
            = (A'.substAll (Typ.var 0 :: L.map (Typ.shift 0))).subAt 0 X := by
        intro L X hLc hLlen
        have := Typ.substAll_subAt_comm (A := A') (k := 0) (pre := []) (L := L.map (Typ.shift 0))
          (X := X) (by simpa [List.length_map, hLlen, Nat.add_comm] using W') rfl
          (fun i h => (Nat.not_lt_zero i h).elim)
          (by intro C hC; simp only [List.mem_map] at hC; obtain ⟨C', hC', rfl⟩ := hC
              rw [Typ.shift_closed (hLc C' hC')]; exact hLc C' hC')
        simpa using this.symm
      simp only [Term.fmap]
      apply HasType.nlam_funcsTo hlen hSc hCc hSx
      refine HasType.recur (hmuC Ss hSc hlen) (hmuC Cs hCc rfl) ?_ (HasType.var rfl)
      refine HasType.cons (hmuC Cs hCc rfl) ?_
      refine HasType.app' (HasType.var rfl) ?_
      simp only [Typ.sub]
      rw [← hcomm Ss _ hSc hlen, ← hcomm Cs _ hCc rfl]
      refine HasType.apps (ih ?_ ?_ ?_ ?_) ?_ ?_ ?_
      · simpa [List.length_map, hlen] using W'
      · simp [List.length_map, hlen]
      · intro S hS
        simp only [List.mem_cons, List.mem_map] at hS
        rcases hS with rfl | ⟨S', hS', rfl⟩
        · exact Typ.Wf.prod (hmuC Ss hSc hlen) (hmuC Cs hCc rfl)
        · rw [Typ.shift_closed (hSc S' hS')]; exact hSc S' hS'
      · intro C hC
        simp only [List.mem_cons, List.mem_map] at hC
        rcases hC with rfl | ⟨C', hC', rfl⟩
        · exact hmuC Cs hCc rfl
        · rw [Typ.shift_closed (hCc C' hC')]; exact hCc C' hC'
      · simp [List.length_map, hlen]
      · simp [List.length_map]
      · intro i hiS hiC hif
        cases i with
        | zero =>
            simp only [List.getElem_cons_zero]
            exact HasType.lam (Typ.Wf.prod (hmuC Ss hSc hlen) (hmuC Cs hCc rfl))
              (HasType.pr2 (HasType.var rfl))
        | succ j =>
            simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range,
              List.getElem_cons_succ]
            have hjS : j < Ss.length := by simp only [List.length_cons, List.length_map] at hiS; omega
            have hjC : j < Cs.length := by simp only [List.length_cons, List.length_map] at hiC; omega
            rw [Typ.shift_closed (hSc _ (List.getElem_mem hjS)),
              Typ.shift_closed (hCc _ (List.getElem_mem hjC))]
            exact HasType.var (by
              rw [show Cs.length + 1 - j = (Cs.length - j) + 1 from by omega, List.cons_append,
                  List.getElem?_cons_succ]
              exact HasType.zipWith_rev_get hlen hjS hjC)

-- Single-variable instantiation `A.substAll [D] = A.sub D` for an
-- open functor `A`.
lemma Typ.substAll_singleton {A} (W : 1 ⊢ A ∷type) (D : Typ) : A.substAll [D] = A.sub D := by
  have hc := Typ.substAll_subAt_comm (A := A) (k := 0) (pre := []) (L := []) (X := D)
    (by simpa using W) rfl (fun i h => (Nat.not_lt_zero i h).elim)
    (by intro C hC; cases hC)
  simp only [List.nil_append] at hc
  rw [Typ.substAll_id (Cs := [Typ.var 0]) W (by intro i hi; simp [Nat.lt_one_iff.mp hi])] at hc
  exact hc.symm

-- Single-variable special case of `HasType.fmap`
lemma HasType.fmap₁ :
    1 ⊢ A ∷type → B.Closed → C.Closed →
    Γ ⊢[Δ, H] fmap₁ A C ∷ (B ⟶ C) ⟶ A.sub B ⟶ A.sub C := by
  intro W hB hC
  rw [Term.fmap₁, ← Typ.substAll_singleton W B, ← Typ.substAll_singleton W C]
  have hg := HasType.fmap (A := A) (Ss := [B]) (Cs := [C]) (Γ := Γ) (Δ := Δ) (H := H)
    (by simpa using W) rfl (by simpa using hB) (by simpa using hC)
  simpa [Typ.funcsTo] using hg




------------------------------------------------
-- The order on environments preserves typing --
------------------------------------------------

--------------------------
-- Lemma 5.3: weakening --
--------------------------

@[grind .]
lemma HasType.le :
  Γ ⊢[Δ, H] t ∷ A → H.le H' → Δ.le Δ' → Γ ⊢[Δ', H'] t ∷ A := by
    intros T SH SΔ
    induction T <;> try {constructor <;> assumption}
    case loc M => constructor; apply SH.lookup at M; apply M
    case chan M => constructor; apply SΔ.lookup at M; apply M
    case case W1 W2 _ _ _ IH1 IH2 IH3 => exact HasType.case W1 W2 IH1 IH2 IH3


@[grind .]
lemma HasType.le' {ε ε'} :
  Γ ⊢{ε} t ∷ A → ε.le ε' → Γ ⊢{ε'} t ∷ A := by
    intros T S
    apply T.le S.store.now.type S.chans


lemma IsHeap.le : Δ.le Δ' → ⊢[Δ] η ∷now → ⊢[Δ'] η ∷now := by
  intros D T
  induction T
  case nil => constructor
  case cons H1 H2 H3 H4 IH =>
    constructor <;> try assumption
    . apply HasType.le H3 <;> simp[D]
    . apply HasType.le H4 <;> simp[D]



lemma EvalType.le :
   Γ ⊩{ε} t ∷ A → ε.le ε' → ⊩ ε' ∷Env → Γ ⊩{ε'} t ∷ A := by
   intros T S E
   constructor
   case term => apply T.term.le <;> try grind
   case env => apply E

/--
On well-typed terms, clocks are closed under expansion of heaps.
-/

lemma HasType.ticked_Sub {t} : ⊢[Δ, η.type] t ∷ ◯ A → η.le η' → t.ticked η κ = t.ticked η' κ := by
  intros T S
  revert A
  induction t <;> intros A T <;> try simp[Term.ticked]
  case wait t E => cases t  <;> try simp[Term.ticked]
  case watch t E =>
    cases t  <;> try simp[Term.ticked]
    case loc l =>
      cases T with | watch T
      cases T with | loc M
      rw[Heap.type_lookup] at M
      simp at M
      rcases M with ⟨s, M, R⟩
      have M' := AList.le.lookup S M
      rw[M,M']
  case select t1 t2 E1 E2 =>
    cases T with | select _ _ T1 T2
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
      have M' := AList.le.lookup S M
      rw[M,M']

-- This lemma is unused, but let's keep it for the sake of intuition.
lemma SigType.le : ⊢[Δ, η] s ∷Sig → η.le η' → Δ.le Δ' → ⊢[Δ', η'] s ∷Sig := by
  intros T S1 S2
  constructor
  . apply T.head.le <;> grind
  . apply T.tail.le <;> grind


-- Inversion lemma for IsEarlierHeap --

lemma IsEarlierHeap.cons_inv : ⊢[Δ, H] η.concat l s p ∷earlier
    → ∃ p', ⊢[Δ, H.cons l s.type p'] η ∷earlier /\
    ⊢[Δ, H] s.head ∷ s.type /\
    ⊢[Δ, H] s.tail ∷ ◯ (.sig s.type) := by
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
    rcases E with ⟨E1, ⟨rfl, rfl⟩⟩
    rw [<- AList.ext_iff] at E1
    subst E1
    constructor;split_ands<;>assumption

lemma IsEnv.tail_type : ⊢ (ηN ✓[D] AList.concat  ηE l' s p ⧸ Δ) ∷Env →
    ⊩{ηN ✓[D] AList.concat ηE l' s p ⧸ Δ} s.tail ∷ ◯ (.sig s.type) := by
  intros T
  have T' := T.2
  simp[Env.now,Env.earlier] at T'
  have T'' := T'.cons_inv
  rcases T'' with ⟨p', T'', Hd, Tl⟩
  constructor
  . simp[Env.now]; apply Tl
  . apply T.1





lemma IsEarlierHeap.le : ⊢[Δ, H] η ∷earlier → H.le H' → Δ.le Δ' → H'.keys.Disjoint η.keys → ⊢[Δ', H'] η ∷earlier := by
  intros E SH Sd D
  revert H' Δ'
  induction E <;> intros H' Δ' SH Sd D
  case nil => constructor
  case cons l _ _ _ _ Hd Tl IH =>
    have p : l ∉ H' := by
      symm at D
      apply AList.concat_cons_Disjoint_nin_keys D
    constructor
    . apply IH
      . apply AList.le.cons_both SH; assumption
      . assumption
      . symm; apply AList.concat_cons_Disjoint_keys;symm; assumption
    . apply Hd.le SH Sd
    . apply Tl.le SH Sd

lemma IsEarlierHeap.le' {ε ε' : Env} :
    ⊢[ε.chans, ε.now.type] ε.earlier ∷earlier → ε.le ε' → ⊢[ε'.chans, ε'.now.type] ε'.earlier ∷earlier  := by
  intros E S
  simp[Env.earlier] at *
  rw[S.store.earlier] at E
  apply E.le S.store.now.type S.chans
  have D := ε'.store.disjoint
  rw[Heap.type_keys]
  apply D


lemma IsEnv.step : ⊢ ε ∷Env → ε.le ε' → ⊩ ε' ∷Env →  ⊢ ε' ∷Env := by
  intro E S N
  cases E with | intro E1 E2
  unfold IsNowEnv at N
  constructor; assumption
  apply E2.le' S

lemma IsHeap.append_sub {η : Heap} {η' D}: ⊢[Δ] η.append η' D ∷now → ⊢[Δ] η' ∷now := by
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



lemma IsHeap.end_step {η η' : Heap} {D} :
    ⊢[Δ] η.append η' D ∷now → ⊢[Δ, η'.type] η ∷earlier := by
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
    have T' : ∃ p D, ⊢[Δ] η''.append (AList.cons l s η' p) D ∷now := by
      constructor; constructor
      rw[<- AList.concat_append] <;> try assumption
      apply  AList.concat_cons_Disjoint_nin D
      apply AList.concat_cons_Disjoint_keys<;>assumption
    rcases T' with ⟨p', D', T'⟩
    constructor
    suffices H : ⊢[Δ, Heap.type (AList.cons l s η' p')] η'' ∷earlier by
      simp[Heap.type] at *
      apply H
    apply IH <;> try assumption
    . apply IsHeap.append_sub at T'; cases T'; assumption
    . apply IsHeap.append_sub at T'; cases T'; assumption
    . rw[Heap.type_fresh]; assumption


lemma IsHeap.end_step' {η} : ⊢[Δ] η ∷now → ⊢[Δ] η ∷earlier := by
  intros T
  have E : ∅ = Heap.type ∅ := by
    simp[Heap.type]; rfl
  rw[E]
  apply IsHeap.end_step
  . simp[AList.append]; apply T
  . apply List.disjoint_nil_right

-- This lemma not used but let's keep it for intuition's sake.
lemma IsEnv.end_step : ⊢ (η ✓[N] ∅ ⧸ Δ) ∷Env → ⊢ (∅ ✓[M] η ⧸ Δ) ∷Env := by
  intros T
  cases T with | intro T1 T2
  unfold IsEnv;
  split_ands
  . constructor
  . simp[Env.earlier,Env.now] at *
    apply T1.end_step'


lemma HasType.loc_inv  : Γ ⊢[Δ, H] .loc l ∷ A → ∃ B, B ∈ H.lookup l /\ A = Typ.sig B := by
  intros T
  cases T
  grind


-----------------------------------------------
-- Decomposition lemmas for typing of values --
-----------------------------------------------


lemma HasType.delayA_value' : ⊢[Δ, H] t ∷ □ A → IsMValue t → ∃ s : Term , t = Term.delay s := by
  intros T V
  cases T<;> try {solve | contradiction | cases V}
  case delay t T => exists t

lemma HasType.delayA_value {v : MVal} : ⊢[Δ, H] v ∷ □ A → ∃ s : Term , v = MVal.delay s := by
  intros T
  rcases v with ⟨t,V⟩
  cases T<;> try {solve | contradiction | cases V}
  case delay t T => exists t


lemma HasType.chan_value: ⊢[Δ, H] t ∷ .chan A → IsMValue t → ∃ κ , t = Term.chan κ := by
  intros T V
  cases T<;> try {solve | contradiction | cases V}
  case chan κ T => exists κ

lemma HasType.sig_value' : ⊢[Δ, H] v ∷ Typ.sig A → IsMValue v → ∃ l , v = MVal.loc l := by
  intros T V
  cases T<;> try {solve | contradiction | cases V}
  case loc l T => exists l

lemma HasType.sig_value {v : MVal} : ⊢[Δ, H] v ∷ Typ.sig A → ∃ l , v = MVal.loc l := by
  intros T
  rcases v with ⟨t,V⟩
  simp at T
  apply T.sig_value' at V
  grind


---------------------------------------
-- Weakening of the typing judgement --
---------------------------------------


lemma HasType.weaken : Γ ⊢[Δ, H] t ∷ A → Γ ++ Γ' ⊢[Δ, H] t ∷ A := by
  intro T
  cases T
  case var V => constructor;  rw [Γ.getElem?_append_left]; assumption; apply Γ.getElem?_some_length; assumption
  case unit | loc | chan | never | newchan => constructor <;> assumption
  case pr1 T' | pr2 T' | delay T' | wait T' | watch T' | head T' | tail T'
     => constructor; apply T'.weaken
  case lam W T' | in1 W T' | in2 W T' | fix W T'
     => constructor; assumption; apply T'.weaken
  case sig T1 T2 | app T2 T1 | appA T1 T2 | pair T1 T2 | appE T1 T2
     => constructor; apply T1.weaken; apply T2.weaken
  case select W1 W2 T1 T2
     => constructor; assumption; assumption; apply T1.weaken; apply T2.weaken
  case recur T2 _ T1
     => constructor; assumption; assumption; apply T1.weaken; apply T2.weaken
  case  cons T' => constructor; assumption; apply T'.weaken
  case case W1 W2 T1 T2 T3
     => exact HasType.case W1 W2 T1.weaken T2.weaken T3.weaken




lemma HasType.weaken_closed: ⊢[Δ, H] t ∷ A → Γ ⊢[Δ, H] t ∷ A := by
  intros T
  apply weaken at T
  simp at T
  apply T


---------------------------------------------------
-- Regularity: typing only involves closed types --
---------------------------------------------------

-- All types assigned by a heap type are closed.
def HeapTy.Closed (H : HeapTy) : Prop := ∀ ⦃l : Loc⦄ ⦃A : Typ⦄, A ∈ H.lookup l → A.Closed

-- All types assigned by a channel context are closed.
def ChanCtx.Closed (Δ : ChanCtx) : Prop := ∀ ⦃κ : Chan⦄ ⦃A : Typ⦄, A ∈ Δ.lookup κ → A.Closed


-- All types in a typing context are closed.
def Ctx.Closed (Γ : Ctx) : Prop := ∀ {A}, A ∈ Γ → A.Closed

-- Regularity: if the typing context, heap type and channel context
-- assign only closed types, then the subject type of any typing
-- derivation is closed.
theorem HasType.regular :
    Γ ⊢[Δ, H] t ∷ A → H.Closed → Δ.Closed → Γ.Closed → A.Closed := by
  intro T hH hΔ
  induction T <;> intro hΓ
  case unit => exact .unit
  case lam W _ IH =>
    refine .arr W (IH ?_)
    intro B hB
    headTail hB
    · exact W
    · apply hΓ;assumption
  case var M => apply hΓ; apply (List.mem_of_getElem? M)
  case loc M => exact .sig (hH M)
  case chan M => exact .chan (hΔ M)
  case sig _ _ IH1 _ => exact .sig (IH1 hΓ)
  case app _ _ IH1 _ => cases IH1 hΓ with | arr _ W => exact W
  case appA _ _ IH1 _ =>
    cases IH1 hΓ with | delayA W =>
    cases W with | arr _ W2 => exact .delayA W2
  case appE _ _ IH1 _ =>
    cases IH1 hΓ with | delayA Wa =>
    cases Wa with | arr _ W2 => exact .delayE W2
  case in1 W _ IH => exact .sum (IH hΓ) W
  case in2 W _ IH => exact .sum W (IH hΓ)
  case case W1 _ _ _ _ _ IH1 _ =>
    refine IH1 ?_
    intro B hB
    headTail hB
    · exact W1
    · apply hΓ; apply hB
  case pair _ _ IH1 IH2 => exact .prod (IH1 hΓ) (IH2 hΓ)
  case pr1 _ IH => cases IH hΓ with | prod W1 _ => exact W1
  case pr2 _ IH => cases IH hΓ with | prod _ W2 => exact W2
  case delay _ IH => exact .delayA (IH hΓ)
  case never W => exact .delayE W
  case newchan W => exact .chan W
  case wait _ IH => cases IH hΓ with | chan W => exact .delayE W
  case select W1 W2 _ _ _ _ => exact .delayE (.sum (.sum W1 W2) (.prod W1 W2))
  case cons W _ _ => exact W
  case recur _ WB _ _ _ _ => exact WB
  case fix W _ _ => exact W
  case head _ IH => cases IH hΓ with | sig W => exact W
  case tail _ IH => cases IH hΓ with | sig W => exact .delayE (.sig W)
  case watch _ IH =>
    cases IH hΓ with | sig W =>
    cases W with | sum W1 _ => exact .delayE W1

-- Corollary: Closed-context special case: a term typeable in the empty context
-- (with closed heap/channel types) has a closed type.
theorem HasType.regular_closed : ⊢[Δ, H] t ∷ A → H.Closed → Δ.Closed → A.Closed := by
  intro T hH hΔ
  apply T.regular hH hΔ
  intro _ hΓ; contradiction



----------------------
-- Auxiliary lemmas --
----------------------

open MVal Typ

lemma HasType.insert :
  ⊩{σ ⧸ Δ} v.val ∷ A → ⊩{σ ⧸ Δ} w.val ∷ ◯ (.sig A) →
  ⊩{σ.insert l ⟨A, v, b, w ⟩ p ⧸ Δ} .loc l ∷ .sig A := by
  intros T1 T2
  constructor
  case term => constructor; rw[Heap.type_lookup,Store.lookup_insert];simp
  case env =>
    simp; constructor
    . apply T1.env
    . apply T1.term
    . apply T2.term

-- This lemma is not used but let's keep it for intuition's sake.
lemma IsHeap.append{η} {η' : Heap} {D} :
  ⊢[Δ] η'.append η D ∷now → ⊢[Δ] η ∷now  := by
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



lemma IsHeap.lookup_SigType : ⊢[Δ] η ∷now →
  s ∈ η.lookup l → ⊢[Δ, η] s ∷Sig := by
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
        . apply H3.le <;> simp [AList.le]
        . apply H4.le <;> simp [AList.le]
      case tail H6 =>
        apply IH at H6
        apply H6.le <;> simp [AList.le]

lemma HasType.loc_lookup {η : Heap}: ⊢[Δ, η.type] ↑(MVal.loc l) ∷ A → ∃ s, s ∈ η.lookup l :=  by
  intros T
  cases T
  case loc A T =>
    rw[Heap.type_lookup] at T
    simp at T
    rcases T with ⟨s, T, E⟩
    exists s



@[simp,grind .]
lemma EvalType.empty : ⊢[Δ] t ∷ A →  ⊩{∅ ⧸ Δ} t ∷ A := by
  intros
  constructor
  simp[Env.now]
  assumption
  constructor
