/-
Definition of the operational semantics
-/

import Rizzo.Syntax
import Rizzo.Env
import Rizzo.Substitution

open Term
open Val

--------------------------------------------
-- Definition of the evaluation semantics --
--------------------------------------------

inductive Eval : Term × Env → Val × Env → Prop where
| value : (V : IsValue v) → Eval (v, ε) (⟨v , V⟩, ε)
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
| wait : Eval (t, ε) (v, ε') →
    Eval (.wait t, ε) (wait v, ε')
| trig : Eval (t, ε) (v, ε') →
    Eval (.trig t, ε) (trig v, ε')
| newchan : Eval (newchan A, σ ⧸ δ)  (chan δ.alloc, σ ⧸ δ.cons δ.alloc A δ.alloc_fresh)
| sync : Eval (s, ε) (u, ε') → Eval (t, ε') (v, ε'') →
    Eval (sync s t, ε) (sync u v, ε'')
| sig : Eval (s, ε) (v, ε') → Eval (t, ε') (w, σ ⧸ δ)
    → Eval (sig A s t, ε)  (loc σ.alloc, σ.insert σ.alloc ⟨ A , v , false, w ⟩ σ.alloc_fresh ⧸ δ)
| tail : Eval (t, ε) (v, ε') →
    Eval (.tail t, ε) (tail v, ε')
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
  Eval (((Term.fmap A (μ A ⊗ B)).app (Term.lam (pair (var 0) (recur B s (var 0))))).app v, ε') (w, ε'') →
  Eval (s.sub w, ε'') (u, ε''') →
  Eval (recur B s t, ε) (u, ε''')


infix : 80 "⇓" => Eval
-------------------------------------------
-- Definition of the advancing semantics --
-------------------------------------------


inductive Adv : Val × Env → Inp → Val × Env → Prop where
| appE {t : Term}: Adv (v, ε) i (v', ε') → (t.app v', ε') ⇓ (w, ε'') → Adv ((Val.delay t).appE v, ε) i (w, ε'')
| wait : Adv (wait (chan κ), ε) (κ ↦ w) (w, ε)
| trig : s ∈ ε.now.lookup l → s.ticked → s.head = v.in1 → Adv (trig (loc l), ε) i (v, ε)
| sync1 : v1.ticked ε.now i.chan → ¬ v2.ticked ε.now i.chan → Adv (v1, ε) i (w, ε') → Adv (sync v1 v2, ε) i (in1 (in1 w), ε')
| sync2 : v2.ticked ε.now i.chan → ¬ v1.ticked ε.now i.chan → Adv (v2, ε) i (w, ε') → Adv (sync v1 v2, ε) i (in1 (in2 w), ε')
| sync3 : v1.ticked ε.now i.chan → v2.ticked ε.now i.chan → Adv (v1, ε) i (w1, ε') → Adv (v2, ε') i (w2, ε'')
     → Adv (sync v1 v2, ε) i (in2 (pair w1 w2), ε'')
| tail : Adv (tail v, ε) i (v, ε)

notation : 80 x : 90 " [" i : 90 "]⇘ " y : 90 => Adv x i y

----------------------------------------
-- Definition of the update semantics --
----------------------------------------

inductive Update : Env → Inp → Env → Prop where
| skip
    {D : ηN.Disjoint (ηE.concat l ⟨A,hd,b,tl⟩ p) } :
    ¬ tl.ticked ηN i.chan →
    Update (ηN ✓[D] ηE.concat l ⟨A,hd,b,tl⟩ p ⧸ δ) i
          (ηN.cons l ⟨A,hd,false,tl⟩ p' ✓[D'] ηE ⧸ δ)
| adv
      {D : ηN.Disjoint (ηE.concat l s p) }
      {D' : ηN'.Disjoint (ηE.concat l s p)} :
    s.tail.ticked ηN i.chan →
    (s.tail, (ηN ✓[D] ηE.concat l s p ⧸ δ)) [i]⇘ (.loc l' , (ηN'✓[D'] ηE.concat l s p  ⧸ δ')) →
    s' ∈ ηN'.lookup l' →
    Update (ηN ✓[D] ηE.concat l s p ⧸ δ) i (ηN'.cons l s'.tick p' ✓[D''] ηE ⧸ δ')

notation : 80 x : 90 " [" i : 90 "]⇒ "  y : 90 => Update x i y

/-- Transitive closure of the update semantics -/

inductive Updates : Env → Inp → Env → Prop where
| nil : Updates ε i ε
| cons : ε1 [i]⇒ ε2 → Updates ε2 i ε3 → Updates ε1 i ε3

notation : 80 x : 90 " [" i : 90 "]⇒* " y : 90 => Updates x i y

---------------------------------------
-- Definition of the step semantics --
---------------------------------------

inductive ReactStep : Val × Heap × ChanCtx → Inp → Val × Heap × ChanCtx → Prop where
| react :
    Updates ( ∅ ✓[D] η ⧸ δ) i (η' ✓[D'] ∅ ⧸ δ') →  ReactStep (v, η , δ) i (v, η', δ')

notation : 80 x : 90 " [" i : 90"]⟹ " y : 90 => ReactStep x i y


inductive InitStep : Term × ChanCtx → Val × Heap × ChanCtx → Prop where
| init : (t, ∅ ⧸ δ) ⇓ (v, η ✓[D] ∅ ⧸ δ') →  InitStep (t , δ) (v, η, δ')


notation : 80 x : 90 " init⟹ " y : 90 => InitStep x y

---------------
-- Lemma 5.5 --
---------------

/--
The evaluation semantics is increasing wrt. the ordering on
environments
-/

lemma Eval.incr : (t, ε) ⇓ (v, ε') → ε.Sub ε' := by
    suffices T : ∀ {C D}, C ⇓ D → C.2.Sub D.2 by apply T
    intro C C' R
    induction R <;> simp at * <;> clear C C'
    case pair | appE | appA | case1 | case2 | sync => trans <;> assumption
    case pr1 | pr2 | wait | trig | tail | head | fix | in1 | in2 | cons => assumption
    case app R1 R2 R3 | recur R1 R2 R3 => trans; apply R1; trans; apply R2; apply R3
    case newchan => constructor <;> simp[AList.Sub.cons]
    case sig R1 R2 =>
        trans; apply R1; trans; apply R2; constructor
        case store => simp[Store.Sub.insert]
        case chans => rfl

------------------------------------------------------
-- Auxilliary lemmas about the evaluation semantics --
------------------------------------------------------

lemma Eval.IsValue_rfl :
  IsValue t → (t, ε)⇓(v, ε') → v = t /\ ε = ε' := by
  intros V R
  revert v ε ε'
  induction V <;> intros ε v ε' R <;> cases R <;> try simp!
  case in1 IH v R | in2 IH v R | wait IH v R | trig IH v R | tail IH v R | cons IH v R =>
    apply IH at R; cases R; subst_vars;
    split_ands<;>rfl
  case pair IH1 IH2 v2 ε1 v1 R1 R2 | appE IH1 IH2 v2 ε1 v1 R1 R2  | sync IH1 IH2 v2 ε1 v1 R1 R2 =>
    apply IH1 at R1; apply IH2 at R2;
    cases R1; cases R2; subst_vars;
    split_ands<;>rfl


/-
Auxiliary lemmas about the advancing semantics.
-/

/-
Decomposition/inversion lemmas about the advancing semantics.
-/
-- TODO rename "_decompose" lemmas to "_inv"
lemma Adv.appE_decompose :
    Adv ((Val.delay t).appE v, ε) i (w, ε'') →
  ∃ v' ε', Adv (v, ε) i (v', ε') /\ (t.app v', ε') ⇓ (w, ε'') := by
  generalize E : (Val.delay t).appE v = t'
  intro R
  cases R <;> try cases E
  injections; rw[<-Subtype.eq_iff] at *;subst_eqs
  constructor;constructor; constructor;assumption;assumption


lemma Adv.tail_decompose :
    Adv (.tail v, ε) i (v', ε') -> v' = v /\ ε' = ε := by
  generalize E : Val.tail v = t'
  intro R
  cases R <;> try cases E
  injections; rw[<-Subtype.eq_iff] at *;subst_eqs
  simp

lemma Adv.sync1_decompose : v1.ticked ε.now i.chan → ¬ v2.ticked ε.now i.chan →
    Adv (sync v1 v2, ε) i t' →
    ∃ w ε', t' = (in1 (in1 w), ε') /\ Adv (v1, ε) i (w, ε') := by
  generalize E : Val.sync v1 v2 = t
  intro M1 M2 R
  cases R <;> try solve | cases E
  case sync1 =>
    injections; rw[<-Subtype.eq_iff] at * ;subst_eqs
    constructor; constructor; constructor;
    rfl; assumption
  case sync2 M' _ | sync3 M' _ =>
    simp at M1 M2 M'
    injections; rw[<-Subtype.eq_iff] at * ;subst_eqs
    grind

lemma Adv.sync2_decompose : v2.ticked ε.now i.chan → ¬ v1.ticked ε.now i.chan →
    Adv (sync v1 v2, ε) i t' →
    ∃ w ε', t' = (in1 (in2 w), ε') /\ Adv (v2, ε) i (w, ε') := by
  generalize E : Val.sync v1 v2 = t
  intro M1 M2 R
  cases R <;> try solve | cases E
  case sync2 =>
    injections; rw[<-Subtype.eq_iff] at * ;subst_eqs
    constructor; constructor; constructor;
    rfl; assumption
  case sync1 M' _ | sync3 M' _ =>
    simp at M1 M2 M'
    injections; rw[<-Subtype.eq_iff] at * ;subst_eqs
    grind


lemma Adv.sync3_decompose : v1.ticked ε.now i.chan → v2.ticked ε.now i.chan →
    Adv (sync v1 v2, ε) i t' →
    ∃ w1 w2 ε' ε'', t' = (in2 (pair w1 w2), ε'') /\ Adv (v1, ε) i (w1, ε') /\ Adv (v2, ε') i (w2, ε'') := by
  generalize E : Val.sync v1 v2 = t
  intro M1 M2 R
  cases R <;> try solve | cases E
  case sync3 =>
    injections; rw[<-Subtype.eq_iff] at * ;subst_eqs
    constructor; constructor; constructor;constructor
    split_ands; rfl; assumption; assumption
  case sync1 M' _ | sync2 M' _ =>
    simp at M1 M2 M'
    injections; rw[<-Subtype.eq_iff] at * ;subst_eqs
    grind

/--
Variant of Adv.tail that is easier to use in proofs.
-/
lemma Adv.tail' : v' = v → ε' = ε → t = .tail v → Adv (t, ε) i (v', ε') := by
  intros E1 E2 E3
  subst_vars
  apply Adv.tail


/-
The advancing semantics is increasing wrt. the ordering on
environments
-/

lemma Adv.incr : (t, ε) [i]⇘ (v, ε') → ε.Sub ε' := by
    suffices T : ∀ {C D}, C [i]⇘ D → C.2.Sub D.2 by apply T
    intro C D R
    induction R <;> simp at * <;> clear C D
    case appE R1 R2 IH1 => apply Eval.incr at R2;trans <;> assumption
    case sync1 | sync2 => assumption
    case sync3 IH1 IH2 => trans <;> assumption

/--
The update semantics is increasing wrt. the ordering on
the chanel context and the now heap
-/

lemma Update.incr_chans : ε [ i ]⇒ ε' → ε.chans.Sub ε'.chans := by
  intros R
  cases R
  case skip => unfold Env.chans;simp
  case adv R =>
    unfold Env.chans;simp
    have S := R.incr.chans
    apply S



lemma Updates.incr_chans : ε [ i ]⇒* ε' → ε.chans.Sub ε'.chans := by
  intros Rs
  induction Rs
  case nil => rfl
  case cons R Rs IH => trans; apply R.incr_chans; apply IH

lemma Update.incr_now : ε [ i ]⇒ ε' → ε.now.Sub ε'.now := by
  intros R
  cases R
  case skip => unfold Env.now;simp
  case adv R =>
    unfold Env.now;simp
    have S := R.incr.store.now
    simp at S
    trans; apply S; simp


lemma Updates.incr_now : ε [ i ]⇒* ε' → ε.now.Sub ε'.now := by
  intros Rs
  induction Rs
  case nil => rfl
  case cons R Rs IH => trans; apply R.incr_now; apply IH

lemma Update.decrease : ε [ i ]⇒ ε' → ε.earlier.entries.length = ε'.earlier.entries.length.succ := by
  intros R
  cases R<;>simp[Env.earlier,AList.concat] at *

/- Inversion lemmas for the update semantics. -/

lemma Update.skip_inv {D : ηN.Disjoint (ηE.concat l ⟨A,hd,θ,tl⟩ p) }  :
    Update (ηN ✓[D] ηE.concat l ⟨A,hd,θ,tl⟩ p ⧸ δ) i ε → ¬ tl.ticked ηN i.chan →
    ∃ p' D' , ε = (ηN.cons l ⟨A,hd,false ,tl⟩ p' ✓[D'] ηE ⧸ δ) := by

  generalize E : ηN ✓[D] AList.concat ηE l (mksig A hd θ tl) p ⧸ δ = ε'
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
     (ηN ✓[D] ηE.concat l s p ⧸ δ) [i]⇒ ε → s.tail.ticked ηN i.chan →
    ∃ ηN' l' δ' s' p' D' D'' ,
    (s.tail, (ηN ✓[D] ηE.concat l s p ⧸ δ)) [i]⇘ (.loc l' , ( ηN' ✓[D'] ηE.concat l s p ⧸ δ')) /\
    s' ∈ ηN'.lookup l' /\
    ε = (ηN'.cons l s'.tick p' ✓[D''] ηE ⧸ δ') := by
  generalize E : ηN ✓[D] AList.concat ηE l s p ⧸ δ = ε'
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

lemma ReactStep.constValue : (v,η,δ) [i]⟹ (v',η',δ') → v = v' := by
  intro R;cases R;rfl
