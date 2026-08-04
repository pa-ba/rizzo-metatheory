/-
Definition of the operational semantics
-/

import Rizzo.Terms
import Rizzo.Env
import Rizzo.Substitution

open Term
open MVal

--------------------------------------------
-- Definition of the evaluation semantics --
-- (Fig. 7)                               --
--------------------------------------------

inductive Eval : Term × Env → MVal × Env → Prop where
| value : (V : IsMValue v) → Eval (v, ε) (⟨v , V⟩, ε)
| pair : Eval (s, ε) (u, ε') → Eval (t, ε') (v, ε'') →
    Eval (pair s t, ε) (pair u v, ε'')
| appE : Eval (s, ε) (u, ε') → Eval (t, ε') (v, ε'') →
    Eval (appE s t, ε) (appE u v, ε'')
| in1 : Eval (t, ε) (v, ε') →
    Eval (in1 t, ε) (in1 v, ε')
| in2 : Eval (t, ε) (v, ε') →
    Eval (in2 t, ε) (in2 v, ε')
| pr1 : Eval (t, ε) (pair u v, ε') →
    Eval (pr1 t, ε) (u, ε')
| pr2 : Eval (t, ε) (pair u v, ε') →
    Eval (pr2 t, ε) (v, ε')
| case1 : Eval (t, ε) (in1 u, ε') → Eval (t1.sub u, ε') (v, ε'') →
    Eval (case t t1 t2, ε) (v, ε'')
| case2 : Eval (t, ε) (in2 u, ε') → Eval (t2.sub u, ε') (v, ε'') →
    Eval (case t t1 t2, ε) (v, ε'')
| app : Eval (s, ε) (lam s', ε') → Eval (t, ε') (u, ε'') → Eval (s'.sub u, ε'') (v, ε''') →
    Eval (app s t, ε) (v, ε''')
| wait : Eval (t, ε) (chan κ, ε') →
    Eval (.wait t, ε) (wait κ, ε')
| watch : Eval (t, ε) (loc l, ε') →
    Eval (.watch t, ε) (watch l, ε')
| newchan : Eval (newchan A, σ ⧸ Δ)  (chan Δ.alloc, σ ⧸ Δ.cons Δ.alloc A Δ.alloc_fresh)
| select : Eval (s, ε) (u, ε') → Eval (t, ε') (v, ε'') →
    Eval (select s t, ε) (select u v, ε'')
| sig : Eval (s, ε) (v, ε') → Eval (t, ε') (w, σ ⧸ Δ)
    → Eval (sig A s t, ε)  (loc σ.alloc, σ.insert σ.alloc ⟨ A , v , false, w ⟩ σ.alloc_fresh ⧸ Δ)
| tail : Eval (t, ε) (loc l, ε') →
    Eval (.tail t, ε) (tail l, ε')
| head : Eval (t, ε) (loc l, ε') → s ∈ ε'.store.now.lookup l →
    Eval (.head t, ε) (s.head, ε')
| fix : Eval (t.sub (.delay (fix t)), ε) (v, ε') →
    Eval (fix t, ε) (v, ε')
| appA : Eval (s, ε) (delay s', ε') → Eval (t, ε') (delay t', ε'') →
    Eval (appA s t, ε) (delay (app s' t'), ε'')
| cons : Eval (t, ε) (v, ε') →
    Eval (cons A t, ε) (cons A v, ε')
| recur :
  Eval (t, ε) (cons A v, ε') →
  Eval (((Term.fmap₁ A (μ A ⨂ B)).app (Term.lam (pair (var 0) (recur B s (var 0))))).app v, ε') (w, ε'') →
  Eval (s.sub w, ε'') (u, ε''') →
  Eval (recur B s t, ε) (u, ε''')


infix : 80 "⇓" => Eval
-----------------------------------------
-- Definition of the advance semantics --
-- (Fig. 8)                            --
-----------------------------------------


inductive Adv : MVal × Env → Event → MVal × Env → Prop where
| appE {t : Term}: Adv (v, ε) e (v', ε') → (t.app v', ε') ⇓ (w, ε'') → Adv ((MVal.delay t).appE v, ε) e (w, ε'')
| wait {u : Term} : (u, ε) ⇓ (w, ε') → Adv (wait κ, ε) (κ ↦ u) (w, ε')
| watch : s ∈ ε.now.lookup l → s.ticked → s.head = v.in1 → Adv (watch l, ε) e (v, ε)
| select1 : v1.ticked ε.now e.chan → ¬ v2.ticked ε.now e.chan → Adv (v1, ε) e (w, ε') → Adv (select v1 v2, ε) e (in1 (in1 w), ε')
| select2 : v2.ticked ε.now e.chan → ¬ v1.ticked ε.now e.chan → Adv (v2, ε) e (w, ε') → Adv (select v1 v2, ε) e (in1 (in2 w), ε')
| select3 : v1.ticked ε.now e.chan → v2.ticked ε.now e.chan → Adv (v1, ε) e (w1, ε') → Adv (v2, ε') e (w2, ε'')
     → Adv (select v1 v2, ε) e (in2 (pair w1 w2), ε'')
| tail : Adv (tail l, ε) e (loc l, ε)

notation : 80 x : 90 " [" i : 90 "]⇘ " y : 90 => Adv x i y

----------------------------------------
-- Definition of the update semantics --
-- (Fig. 8)                           --
----------------------------------------

inductive Update : Env → Event → Env → Prop where
| skip
    {D : ηN.Disjoint (ηE.concat l ⟨A,hd,b,tl⟩ p) } :
    ¬ tl.ticked ηN e.chan →
    Update (ηN ✓[D] ηE.concat l ⟨A,hd,b,tl⟩ p ⧸ Δ) e
          (ηN.cons l ⟨A,hd,false,tl⟩ p' ✓[D'] ηE ⧸ Δ)
| adv
      {D : ηN.Disjoint (ηE.concat l s p) }
      {D' : ηN'.Disjoint (ηE.concat l s p)} :
    s.tail.ticked ηN e.chan →
    (s.tail, (ηN ✓[D] ηE.concat l s p ⧸ Δ)) [e]⇘ (.loc l' , (ηN'✓[D'] ηE.concat l s p  ⧸ Δ')) →
    s' ∈ ηN'.lookup l' →
    Update (ηN ✓[D] ηE.concat l s p ⧸ Δ) e (ηN'.cons l s'.tick p' ✓[D''] ηE ⧸ Δ')

notation : 80 x : 90 " [" e : 90 "]⇒ "  y : 90 => Update x e y

/-- Transitive closure of the update semantics -/

inductive Updates : Env → Event → Env → Prop where
| nil : Updates ε e ε
| cons : ε1 [e]⇒ ε2 → Updates ε2 e ε3 → Updates ε1 e ε3

notation : 80 ε : 90 " [" e : 90 "]⇒* " ε' : 90 => Updates ε e ε'

------------------------------------
-- Step semantics (reactive step) --
-- denoted (p,η/Δ)[e]⟹ (p,η'/Δ') --
-- (Fig. 8)                       --
------------------------------------

inductive ReactStep : MVal × Heap × ChanCtx → Event → MVal × Heap × ChanCtx → Prop where
| react :
    Updates ( ∅ ✓[D] η ⧸ Δ) e (η' ✓[D'] ∅ ⧸ Δ') →  ReactStep (v, η , Δ) e (v, η', Δ')

notation : 80 x : 90 " [" e : 90"]⟹ " y : 90 => ReactStep x e y


----------------------------------
-- Step semantics (init step)   --
-- denoted (t,Δ)init⟹ (p,η/Δ') --
-- (Fig. 8)                     --
----------------------------------

inductive InitStep : Term × ChanCtx → MVal × Heap × ChanCtx → Prop where
| init : (t, ∅ ⧸ Δ) ⇓ (v, η ✓[D] ∅ ⧸ Δ') →  InitStep (t , Δ) (v, η, Δ')


notation : 80 x : 90 " init⟹ " y : 90 => InitStep x y

----------------------------------------------------
-- Finite sequence of steps in the step semantics --
----------------------------------------------------

-- finite sequence of events (in reverse order)
def Events := List Event

-- Finite step sequence, i.e. a finite sequence of steps with well-typed event.
inductive Steps : Term × ChanCtx → Events → MVal × Heap × ChanCtx → Prop where
  | init : (t,Δ) init⟹ (v,η,Δ') → Steps (t,Δ) [] (v,η,Δ')
  | react :
    Steps (t,Δ0) τ (v,η,Δ) → ⊢[Δ] e ∷Event → (v,η,Δ) [e]⟹ (v',η',Δ') → Steps (t,Δ0) (e :: τ) (v',η',Δ')

notation : 80 x : 90 " [ " τ : 90 " ]⟹+ " y : 90 => Steps x τ y

-----------------------------------
-- Reactive evaluation semantics --
-- (Fig. 8)                      --
-----------------------------------

inductive Reacts : (Term × ChanCtx) → Events → (Term × ChanCtx) → Prop where
  | reacts (steps : (t, Δ) [τ]⟹+ (v, η, Δ')) :
      Reacts (t, Δ) τ (v.val.heapSub η, Δ')

notation : 80 x : 90  " [ " τ : 90 " ]⤳ " y : 90 => Reacts x τ y


------------------------------------------------------
-- Infinite sequence of steps in the step semantics --
------------------------------------------------------

-- infinite sequence of events (in reverse order)
def Eventsω := Nat → Event

-- Infinite step sequence, i.e. an infinite sequence of steps with well-typed event.
structure Stepsω  (start : Term × ChanCtx) (events : Eventsω) where
  state : Nat → MVal × Heap × ChanCtx
  wfevent : ∀ i, ⊢[(state i).2.2] events i ∷Event
  init : start init⟹ state 0
  react : ∀ i, (state i) [events i]⟹ state (i+1)

notation : 80 x : 90 " [ " τ : 90 " ]⟹ω"  => Stepsω x τ

def Stepsω.heap (S : (t, Δ0) [τ]⟹ω) (i : Nat) : Heap :=
  (S.state i).2.1
def Stepsω.chans (S : (t, Δ0) [τ]⟹ω) (i : Nat) : ChanCtx :=
  (S.state i).2.2
def Stepsω.val (S : (t, Δ0) [τ]⟹ω) (i : Nat) : MVal :=
  (S.state i).1

def Eventsω.prefix (τ : Eventsω) (n : Nat) : Events :=
  match n with
  | 0 => []
  | .succ m => τ m :: τ.prefix m

def Stepsω.prefix (S : (t, Δ) [τ]⟹ω) (n : Nat) : (t,Δ) [τ.prefix n]⟹+ (S.state n) :=
  match n with
  | 0 => Steps.init S.init
  | .succ m => Steps.react (S.prefix m) (S.wfevent m) (S.react m)

---------------
-- Lemma 5.6 --
---------------

/--
The evaluation semantics is increasing wrt. the ordering on
environments
-/

lemma Eval.incr : (t, ε) ⇓ (v, ε') → ε.le ε' := by
    suffices T : ∀ {C D}, C ⇓ D → C.2.le D.2 by apply T
    intro C C' R
    induction R <;> simp at * <;> clear C C'
    case pair | appE | appA | case1 | case2 | select => trans <;> assumption
    case pr1 | pr2 | wait | watch | tail | head | fix | in1 | in2 | cons => assumption
    case app R1 R2 R3 | recur R1 R2 R3 => trans; apply R1; trans; apply R2; apply R3
    case newchan => constructor <;> simp[AList.le.cons]
    case sig R1 R2 =>
        trans; apply R1; trans; apply R2; constructor
        case store => simp[Store.le.insert]
        case chans => rfl

------------------------------------------------------
-- Auxilliary lemmas about the evaluation semantics --
------------------------------------------------------

lemma Eval.IsValue_rfl :
  IsMValue t → (t, ε)⇓(v, ε') → v = t /\ ε = ε' := by
  intros V R
  revert v ε ε'
  induction V <;> intros ε v ε' R <;> cases R <;> try simp!
  case in1 IH v R | in2 IH v R | cons IH v R =>
    apply IH at R; cases R; subst_vars;
    split_ands<;>rfl
  case tail l R | wait κ R | watch l R => cases R; exact ⟨rfl, rfl⟩
  case pair IH1 IH2 v2 ε1 v1 R1 R2 | appE IH1 IH2 v2 ε1 v1 R1 R2  | select IH1 IH2 v2 ε1 v1 R1 R2 =>
    apply IH1 at R1; apply IH2 at R2;
    cases R1; cases R2; subst_vars;
    split_ands<;>rfl


/-
Auxiliary lemmas about the advancing semantics.
-/

/-
Decomposition/inversion lemmas about the advancing semantics.
-/
lemma Adv.appE_inv :
    ((MVal.delay t).appE v, ε) [i]⇘ (w, ε'') →
  ∃ v' ε', (v, ε) [i]⇘ (v', ε') /\ (t.app v', ε') ⇓ (w, ε'') := by
  generalize E : (MVal.delay t).appE v = t'
  intro R
  cases R <;> try cases E
  injections; rw[<-Subtype.ext_iff] at *;subst_eqs
  constructor;constructor; constructor;assumption;assumption


lemma Adv.wait_inv :
    (MVal.wait κ, ε) [e]⇘ (w, ε') → e.chan = κ /\ (e.val, ε) ⇓ (w, ε') := by
  generalize E : MVal.wait κ = t'
  intro R
  cases R <;> try cases E
  exact ⟨rfl, by assumption⟩

lemma Adv.tail_inv {l : Loc} :
    (.tail l, ε) [e]⇘ (v', ε') -> v' = .loc l /\ ε' = ε := by
  generalize E : MVal.tail l = t'
  intro R
  cases R <;> try cases E
  simp

lemma Adv.select1_inv : v1.ticked ε.now e.chan → ¬ v2.ticked ε.now e.chan →
    (select v1 v2, ε) [e]⇘ t' →
    ∃ w ε', t' = (in1 (in1 w), ε') /\ (v1, ε) [e]⇘ (w, ε') := by
  generalize E : MVal.select v1 v2 = t
  intro M1 M2 R
  cases R <;> try solve | cases E
  case select1 =>
    injections; rw[<-Subtype.ext_iff] at * ;subst_eqs
    constructor; constructor; constructor;
    rfl; assumption
  case select2 M' _ | select3 M' _ =>
    simp at M1 M2 M'
    injections; rw[<-Subtype.ext_iff] at * ;subst_eqs
    grind

lemma Adv.select2_inv : v2.ticked ε.now e.chan → ¬ v1.ticked ε.now e.chan →
    (select v1 v2, ε) [e]⇘ t' →
    ∃ w ε', t' = (in1 (in2 w), ε') /\ (v2, ε) [e]⇘ (w, ε') := by
  generalize E : MVal.select v1 v2 = t
  intro M1 M2 R
  cases R <;> try solve | cases E
  case select2 =>
    injections; rw[<-Subtype.ext_iff] at * ;subst_eqs
    constructor; constructor; constructor;
    rfl; assumption
  case select1 M' _ | select3 M' _ =>
    simp at M1 M2 M'
    injections; rw[<-Subtype.ext_iff] at * ;subst_eqs
    grind


lemma Adv.select3_inv : v1.ticked ε.now e.chan → v2.ticked ε.now e.chan →
    (select v1 v2, ε) [e]⇘ t' →
    ∃ w1 w2 ε' ε'', t' = (in2 (pair w1 w2), ε'') /\ (v1, ε) [e]⇘ (w1, ε') /\ (v2, ε') [e]⇘ (w2, ε'') := by
  generalize E : MVal.select v1 v2 = t
  intro M1 M2 R
  cases R <;> try solve | cases E
  case select3 =>
    injections; rw[<-Subtype.ext_iff] at * ;subst_eqs
    constructor; constructor; constructor;constructor
    split_ands; rfl; assumption; assumption
  case select1 M' _ | select2 M' _ =>
    simp at M1 M2 M'
    injections; rw[<-Subtype.ext_iff] at * ;subst_eqs
    grind


/-
The advancing semantics is increasing wrt. the ordering on
environments
-/

lemma Adv.incr : (t, ε) [e]⇘ (v, ε') → ε.le ε' := by
    suffices T : ∀ {C D}, C [e]⇘ D → C.2.le D.2 by apply T
    intro C D R
    induction R <;> simp at * <;> clear C D
    case wait R => exact Eval.incr R
    case appE R1 R2 IH1 => apply Eval.incr at R2;trans <;> assumption
    case select1 | select2 => assumption
    case select3 IH1 IH2 => trans <;> assumption

/--
The update semantics is increasing wrt. the ordering on
the chanel context and the now heap
-/

lemma Update.incr_chans : ε [ e ]⇒ ε' → ε.chans.le ε'.chans := by
  intros R
  cases R
  case skip => unfold Env.chans;simp
  case adv R =>
    unfold Env.chans;simp
    have S := R.incr.chans
    apply S



lemma Updates.incr_chans : ε [ e ]⇒* ε' → ε.chans.le ε'.chans := by
  intros Rs
  induction Rs
  case nil => rfl
  case cons R Rs IH => trans; apply R.incr_chans; apply IH

-- Unused lemma, but let's keep it for the sake of intuition.
lemma Update.incr_now : ε [ e ]⇒ ε' → ε.now.le ε'.now := by
  intros R
  cases R
  case skip => unfold Env.now;simp
  case adv R =>
    unfold Env.now;simp
    have S := R.incr.store.now
    simp at S
    trans; apply S; simp


lemma Update.decrease : ε [ e ]⇒ ε' → ε.earlier.entries.length = ε'.earlier.entries.length.succ := by
  intros R
  cases R<;>simp[Env.earlier,AList.concat] at *

/- Inversion lemmas for the update semantics. -/

lemma Update.skip_inv {D : ηN.Disjoint (ηE.concat l ⟨A,hd,θ,tl⟩ p) }  :
    Update (ηN ✓[D] ηE.concat l ⟨A,hd,θ,tl⟩ p ⧸ Δ) e ε → ¬ tl.ticked ηN e.chan →
    ∃ p' D' , ε = (ηN.cons l ⟨A,hd,false ,tl⟩ p' ✓[D'] ηE ⧸ Δ) := by

  generalize E : ηN ✓[D] AList.concat ηE l (mksig A hd θ tl) p ⧸ Δ = ε'
  intros R Ch
  cases R
  case adv Ch' _ =>
    apply Env.eq_inv at E
    rcases E with ⟨rfl, E, rfl⟩
    apply Heap.concat_inv at E
    rcases E with ⟨rfl, rfl, rfl⟩
    contradiction
  case skip Ch' _ =>
    apply Env.eq_inv at E
    rcases E with ⟨rfl, E, rfl⟩
    apply Heap.concat_inv at E
    rcases E with ⟨rfl, rfl, E⟩
    cases E
    grind



lemma Update.adv_inv {D : ηN.Disjoint (ηE.concat l s p) }  :
     (ηN ✓[D] ηE.concat l s p ⧸ Δ) [e]⇒ ε → s.tail.ticked ηN e.chan →
    ∃ ηN' l' Δ' s' p' D' D'' ,
    (s.tail, (ηN ✓[D] ηE.concat l s p ⧸ Δ)) [e]⇘ (.loc l' , ( ηN' ✓[D'] ηE.concat l s p ⧸ Δ')) /\
    s' ∈ ηN'.lookup l' /\
    ε = (ηN'.cons l s'.tick p' ✓[D''] ηE ⧸ Δ') := by
  generalize E : ηN ✓[D] AList.concat ηE l s p ⧸ Δ = ε'
  intros R Ch
  cases R
  case skip Ch' =>
    apply Env.eq_inv at E
    rcases E with ⟨rfl, E, rfl⟩
    apply Heap.concat_inv at E
    rcases E with ⟨rfl, rfl, rfl⟩
    simp at Ch
    contradiction
  case adv Ch' _ =>
    apply Env.eq_inv at E
    rcases E with ⟨rfl, E, rfl⟩
    apply Heap.concat_inv at E
    rcases E with ⟨rfl, rfl, E⟩
    cases E
    grind

lemma ReactStep.constValue : (v,η,Δ) [e]⟹ (v',η',Δ') → v = v' := by
  intro R;cases R;rfl
