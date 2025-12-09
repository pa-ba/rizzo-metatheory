import Rizzo.Semantics

theorem Eval.determ : e ⇓ e1 → e ⇓ e2 → e1 = e2 := by
  intro R1
  revert e2
  induction R1 <;> intros e2 R2
  case value V =>
    apply Eval.IsValue_rfl V at R2;
    cases R2; subst_eqs; rfl
  case pair IH1 IH2 =>
    cases R2 with
    | value V =>
      cases V with | pair V1 V2
      apply Eval.value at V1; apply IH1 at V1
      apply Eval.value at V2; apply IH2 at V2
      cases V1; cases V2; rfl
    | pair R21 R22 =>
      apply IH1 at R21; cases R21
      apply IH2 at R22; cases R22
      rfl
  case appE IH1 IH2 =>
    cases R2 with
    | value V =>
      cases V with | appE V1 V2
      apply Eval.value at V1; apply IH1 at V1
      apply Eval.value at V2; apply IH2 at V2
      cases V1; cases V2; rfl
    | appE R21 R22 =>
      apply IH1 at R21; cases R21
      apply IH2 at R22; cases R22
      rfl
  case sync IH1 IH2 =>
    cases R2 with
    | value V =>
      cases V with | sync V1 V2
      apply Eval.value at V1; apply IH1 at V1
      apply Eval.value at V2; apply IH2 at V2
      cases V1; cases V2; rfl
    | sync R21 R22 =>
      apply IH1 at R21; cases R21
      apply IH2 at R22; cases R22
      rfl
  case in1 IH =>
    cases R2 with
    | value V =>
      cases V with | in1 V
      apply Eval.value at V; apply IH at V
      cases V; rfl
    | in1 R2' => apply IH at R2'; cases R2'; rfl
  case in2 IH =>
    cases R2 with
    | value V =>
      cases V with | in2 V
      apply Eval.value at V; apply IH at V
      cases V; rfl
    | in2 R2' => apply IH at R2'; cases R2'; rfl
  case wait IH =>
    cases R2 with
    | value V =>
      cases V with | wait V
      apply Eval.value at V; apply IH at V
      cases V; rfl
    | wait R2' =>  apply IH at R2'; cases R2'; rfl
  case trig IH =>
    cases R2 with
    | value V =>
      cases V with | trig V
      apply Eval.value at V; apply IH at V
      cases V; rfl
    | trig R2' =>  apply IH at R2'; cases R2'; rfl
  case tail IH =>
    cases R2 with
    | value V =>
      cases V with | tail V
      apply Eval.value at V; apply IH at V
      cases V; rfl
    | tail R2' =>  apply IH at R2'; cases R2'; rfl
  case pr1 IH =>
    cases R2 with
    | value V => cases V
    | pr1 R2' => apply IH at R2'; injections;simp[Subtype.eq_iff, *]
  case pr2 IH =>
    cases R2 with
    | value V => cases V
    | pr2 R2' => apply IH at R2'; injections;simp[Subtype.eq_iff, *]
  case cons IH =>
    cases R2 with
    | value V =>
      cases V with | cons V
      apply Eval.value at V; apply IH at V
      cases V; rfl
    | cons R2' => apply IH at R2'; injections;simp[*]
  case recur IH1 IH2 IH3 =>
    cases R2 with
    | value V => cases V
    | recur R21 R22 R23 =>
      apply IH1 at R21; injections R21;subst_eqs;simp[*] at *
      apply IH2 at R22; rcases R22 with ⟨rfl,rfl⟩
      apply IH3 at R23; cases R23
      grind
  case app IH1 IH2 IH3 =>
    cases R2 with
    | value V => cases V
    | app R21 R22 R23 =>
      apply IH1 at R21; cases R21
      apply IH2 at R22; cases R22
      apply IH3 at R23; cases R23
      rfl
  case appA IH1 IH2 =>
    cases R2 with
    | value V => cases V
    | appA R21 R22 =>
      apply IH1 at R21; cases R21
      apply IH2 at R22; cases R22
      rfl
  case case1 IH1 IH2 =>
    cases R2 with
    | value V => cases V
    | case1 R21 R22 =>
      apply IH1 at R21;
      injections;simp[Subtype.eq_iff, *] at *
      apply IH2 at R22; cases R22
      split_ands<;>assumption
    | case2 R21 R22 => apply IH1 at R21; injections
  case case2 IH1 IH2 =>
    cases R2 with
    | value V => cases V
    | case2 R21 R22 =>
      apply IH1 at R21;
      injections;simp[Subtype.eq_iff, *] at *
      apply IH2 at R22; cases R22
      split_ands<;>assumption
    | case1 R21 R22 => apply IH1 at R21; injections
  case newchan =>
    cases R2 with
    | value V => cases V
    | newchan => rfl
  case sig IH1 IH2 =>
    cases R2 with
    | value V => cases V
    | sig R21 R22 =>
      apply IH1 at R21; cases R21
      apply IH2 at R22; cases R22
      rfl
  case head L1 IH =>
    cases R2 with
    | value V => cases V
    | head R2' L2 =>
      apply IH at R2'; injections; subst_eqs
      simp at L1 L2
      rw[L1] at L2;cases L2; rfl
  case fix IH =>
    cases R2 with
    | value V => cases V
    | fix R2' =>
      apply IH at R2'; cases R2'
      rfl

open Val


lemma Val.in1_inj {v w : Val} : v.in1 = w.in1 → v = w := by
  intros E
  cases v
  cases w
  cases E;rfl

theorem Adv.determ : e [i]⇘ e1 → e [i]⇘ e2 → e1 = e2 := by
  intro R1
  revert e2
  induction R1 <;> intros e2 R2
  case wait => cases R2;rfl
  case appE R1' IH =>
    apply Adv.appE_decompose at R2
    rcases R2 with ⟨v', ε', R21,R22⟩
    apply IH at R21
    injections;subst_eqs
    have E := Eval.determ R1' R22
    injections;subst_eqs
    rfl
  case sync1 M1 M2 R IH =>
    apply Adv.sync1_decompose M1 M2 at R2
    rcases R2 with ⟨v', ε', rfl, R21⟩
    apply IH at R21
    injections;subst_eqs
    rfl
  case sync2 M1 M2 R IH =>
    apply Adv.sync2_decompose M1 M2 at R2
    rcases R2 with ⟨v', ε', rfl, R21⟩
    apply IH at R21
    injections;subst_eqs
    rfl
  case sync3 M1 M2 R11 R12 IH1 IH2 =>
    apply Adv.sync3_decompose M1 M2 at R2
    rcases R2 with ⟨w1 ,w2, ε' , ε'', rfl, R21, R22⟩
    apply IH1 at R21
    injections;subst_eqs
    apply IH2 at R22
    injections;subst_eqs
    rfl
  case tail =>
    apply Adv.tail_decompose at R2
    rcases R2 with ⟨v', ε', rfl, rfl⟩
    subst_eqs; rfl
  case trig L1 Td1 Hd1 =>
    cases R2 with | trig L2 Td2 Hd2
    rw[L1] at L2
    injection L2; subst_eqs
    rw[Hd1] at Hd2
    apply Val.in1_inj at Hd2; subst Hd2
    rfl



theorem Update.determ : ε [i]⇒ ε1 → ε [i]⇒ ε2 → ε1 = ε2 := by
  intros R1 R2
  cases R1
  case skip Ch =>
    have E := Update.skip_inv R2 Ch
    grind
  case adv L Ch R =>
    have E := Update.adv_inv R2 Ch
    rcases E with ⟨ηN', l', δ', s', p', D', D'', R', L' ,E⟩
    have E' := Adv.determ R R'
    injection E' with F1 F2
    cases F1
    apply Env.eq_inv at F2
    rcases F2 with ⟨rfl, E', rfl⟩
    apply Heap.concat_inv at E'
    rcases E' with ⟨F1, F2, F3⟩
    subst_eqs
    simp at L L'
    rw[L'] at L
    cases L
    rfl

theorem Updates.determ : ε [i]⇒* ε1 → ε [i]⇒* ε2 → ε1.earlier = ∅ → ε2.earlier = ∅ → ε1 = ε2 := by
  intros R1 R2 E1 E2
  induction R1
  case nil ε0 ε1 =>
    cases R2
    case cons R Rs =>
      have D := Update.decrease R
      rw[E1] at D
      simp! at D
    case nil => rfl
  case cons ε5 i ε4 ε3 R1 Rs1 IH =>
    cases R2
    case nil =>
      have D := Update.decrease R1
      rw[E2] at D
      simp! at D
    case cons R2 Rs2 =>
      have E := Update.determ R1 R2
      subst_eqs
      solve_by_elim


---------------------------------------------------
-- Lemma 4.3 (ii):                               --
-- The reactive step semantics is deterministic  --
---------------------------------------------------

theorem ReactStep.determ : e [i]⟹ e1 → e [i]⟹ e2 → e1 = e2 := by
  intros R1 R2
  cases R1 with | react R1
  cases R2 with | react R2
  have E := Updates.determ R1 R2 (by simp) (by simp)
  grind


--------------------------------------------------------
-- Lemma 4.3 (i):                                     --
-- The initialisation step semantics is deterministic --
--------------------------------------------------------

theorem InitStep.determ : e init⟹ e1 → e init⟹ e2 → e1 = e2 := by
  intros R1 R2
  cases R1 with | init R1
  cases R2 with | init R2
  have E := Eval.determ R1 R2
  grind
