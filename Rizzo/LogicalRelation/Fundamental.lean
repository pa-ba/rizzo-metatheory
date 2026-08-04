import Rizzo.LogicalRelation.Properties

open Term
open MVal
open Typ
open List

---------------------------------------------
-- lemmas for proving fundamental property --
---------------------------------------------

abbrev TRel' (A : Typ) (ρ : LRelSubs)  (ε : Env) (t : Term) : Prop :=
  ∀ {ε'}, ε.le ε' → t ∈ T⟦A⟧ ρ # ε'

notation : 80 v : 90 " ∈ " "T'⟦" A : 90 "⟧" ρ : 90 "#" ε : 90 => TRel' A ρ ε v
notation : 80 v : 90 " ∈ " "T'⟦" A : 90 "⟧" ε : 90 => TRel' A ρ0 ε v

lemma TRel'.VRel  :  LRelSubs.Kripke ρ → ⟨t, p⟩  ∈ V⟦A⟧ρ#ε → t ∈ T'⟦A⟧ρ#ε := by
  intro WS V ε' S
  apply TRel.VRel
  apply V.kripke WS S

lemma TRel.fromTRel'  :  t ∈ T'⟦A⟧ρ#ε → t ∈ T⟦A⟧ρ#ε := by
  intro T; apply T; rfl

lemma TRel.app : s ∈ T'⟦A ⟶ B⟧ ρ # ε → t ∈ T'⟦A⟧ ρ # ε → s.app  t ∈ T'⟦B⟧ ρ # ε := by
    intros IH1 IH2 ε1 S
    obtain ⟨ v, ε2 , R1 , U1 ⟩ := (IH1 S).elim
    vrel at U1
    rcases U1 with ⟨ U1 , s' , rfl , V1  ⟩
    have S1 := Eval.incr R1
    obtain ⟨ w, ε3 , R2 , U2 ⟩ := (IH2 (by trans<;> assumption)).elim
    have S3 := Eval.incr R2
    have V3 := V1 ε3 S3 w U2
    simp only [TRel] at V3
    obtain ⟨ u, ε4 , R3 , U3 ⟩ := V3
    exact TRel.intro (.app R1 R2 R3) U3

lemma TRel.pair : LRelSubs.Kripke ρ → s ∈ T'⟦A⟧ ρ # ε → t ∈ T'⟦B⟧ ρ # ε → s.pair t ∈ T'⟦A ⨂ B⟧ ρ # ε := by
  intros WS IH1 IH2 ε1 S
  obtain ⟨ v1, ε2 , R1 , U1 ⟩ := (IH1 S).elim
  have S1 := Eval.incr R1
  obtain ⟨ v2, ε3 , R2 , U2 ⟩ := (IH2 (S.trans S1)).elim
  have S3 := Eval.incr R2
  refine TRel.intro (Eval.pair R1 R2) ?_
  vrel
  exact ⟨v1, v2, rfl, U1.kripke WS S3, U2⟩

lemma TRel.in1 : t ∈ T'⟦A⟧ ρ # ε → t.in1 ∈ T'⟦A ⨁ B⟧ ρ # ε := by
  intros IH ε1 S
  obtain ⟨ v, ε2 , R , U ⟩ := (IH S).elim
  refine TRel.intro (Eval.in1 R) ?_
  vrel
  exact Or.inl ⟨v, by simp, U⟩

lemma TRel.in2 : t ∈ T'⟦B⟧ ρ # ε → t.in2 ∈ T'⟦A ⨁ B⟧ ρ # ε := by
  intros IH ε1 S
  obtain ⟨ v, ε2 , R , U ⟩ := (IH S).elim
  refine TRel.intro (Eval.in2 R) ?_
  vrel
  exact Or.inr ⟨v, by simp, U⟩

lemma TRel.pr1 : t ∈ T⟦A ⨂ B⟧ ρ # ε → t.pr1 ∈ T⟦A⟧ ρ # ε := by
  intro h
  obtain ⟨ v, ε2 , R , U ⟩ := h.elim
  vrel at U
  rcases U with ⟨v1, v2, E, U1 , U2⟩
  have E' : v = MVal.pair v1 v2 := by
    cases v; cases v1; cases v2; simpa [MVal.pair] using E
  subst E'
  exact TRel.intro (Eval.pr1 R) U1

lemma TRel.pr2 : t ∈ T⟦A ⨂ B⟧ ρ # ε → t.pr2 ∈ T⟦B⟧ ρ # ε := by
  intro h
  obtain ⟨ v, ε2 , R , U ⟩ := h.elim
  vrel at U
  rcases U with ⟨v1, v2, E, U1 , U2⟩
  have E' : v = MVal.pair v1 v2 := by
    cases v; cases v1; cases v2; simpa [MVal.pair] using E
  subst E'
  exact TRel.intro (Eval.pr2 R) U2

lemma TRel.case {t} :
  t ∈ T⟦A1 ⨁ A2⟧ρ # ε →
  (∀ {v ε'}, ε.le ε' → v ∈ V⟦A1⟧ρ # ε' → t1.sub v ∈ T⟦B⟧ρ # ε') →
  (∀ {v ε'}, ε.le ε' → v ∈ V⟦A2⟧ρ # ε' → t2.sub v ∈ T⟦B⟧ρ # ε') →
  Term.case t t1 t2 ∈ T⟦B⟧ρ # ε := by
  intro hs h1 h2
  obtain ⟨ v, ε2 , R , U ⟩ := hs.elim
  have S' := R.incr
  vrel at U
  rcases U with ⟨ v' , E , U ⟩ |  ⟨ v' , E , U ⟩
  · have E' : v = MVal.in1 v' := by
      cases v; cases v'; simpa [MVal.in1] using E
    subst E'
    obtain ⟨ w, ε3 , R1 , U1 ⟩ := (h1 S' U).elim
    refine TRel.intro ?_ U1
    apply Eval.case1; apply R
    simpa [Term.sub] using R1
  · have E' : v = MVal.in2 v' := by
      cases v; cases v'; simpa [MVal.in2] using E
    subst E'
    obtain ⟨ w, ε3 , R2 , U2 ⟩ := (h2 S' U).elim
    refine TRel.intro ?_ U2
    apply Eval.case2; apply R
    simpa [Term.sub] using R2

lemma TRel.fix :
    ⊢{ε} s ∷ A.substAll ρ.types →
    s = fix t →
    (∀ v p , ⟨v,p⟩ ∈ V⟦□ A⟧ρ#ε → t.sub v ∈ T⟦A⟧ ρ # ε) →
    s ∈ T⟦A⟧ρ # ε := by
  intros T E P
  subst E
  cases T with | fix hA T
  let v : MVal := delay t.fix
  have V : v ∈ V⟦□ A⟧ ρ # ε := by
      simp only [_root_.VRel, v]
      constructor
      constructor
      exact hA
      apply T
  obtain ⟨ vU, ε2, R, U ⟩ := (P v.val v.prop V).elim
  refine TRel.intro ?_ U
  unfold v at R
  constructor; simpa [Term.sub] using R

lemma TRel.sig : A.Wf ρ.length → LRelSubs.Kripke ρ → t ∈ T'⟦A⟧ρ#ε → t' ∈ T'⟦◯ A.sig⟧ρ#ε →
    Term.sig (A.substAll ρ.types) t t' ∈ T'⟦A.sig⟧ρ#ε := by
  intros W WS IH1 IH2 ε1 S
  obtain ⟨ v, ε2 , R1 , U1 ⟩ := (IH1 S).elim
  have S1 := Eval.incr R1
  obtain ⟨ w, ε3 , R2 , U2 ⟩ := (IH2 (S.trans S1)).elim
  rcases ε3 with ⟨σ , Δ⟩
  let s : Sig := ⟨ A.substAll ρ.types , v , false, w ⟩
  let ε4 := σ.insert σ.alloc s σ.alloc_fresh ⧸ Δ
  have S3 := Eval.incr R2
  refine TRel.intro (Eval.sig R1 R2) ?_
  vrel
  exists σ.alloc; split_ands
  . rfl
  . exists s; split_ands
    . simp[Store.insert,Env.now]
      apply AList.lookup_cons
    . unfold s; simp
    . unfold s; simp
      refine VRel.kripke WS U1 ?_
      apply S3.trans
      constructor
      case store => simp[Store.le.insert]
      case chans => rfl

lemma TRel.head : t ∈ T⟦A.sig⟧ρ#ε → t.head ∈ T⟦A⟧ρ#ε := by
  intro h
  obtain ⟨ v, ε2 , R , U ⟩ := h.elim
  vrel at U
  rcases U with ⟨ l , rfl , s , L , E , U ⟩
  exact TRel.intro (Eval.head R L) U

lemma TRel.appE :
    t ∈ T'⟦□ (A ⟶ B)⟧ρ#ε → t' ∈ T'⟦◯ A⟧ρ#ε → t.appE t' ∈ T'⟦◯ B⟧ρ#ε := by
  intros IH1 IH2 ε1 S
  obtain ⟨ v, ε2 , R1 , U1 ⟩ := (IH1 S).elim
  vrel at U1
  have S1 := Eval.incr R1
  obtain ⟨ w, ε3 , R2 , U2 ⟩ := (IH2 (S.trans S1)).elim
  vrel at U2
  have S3 := Eval.incr R2
  have U1' := U1.le' S3
  refine TRel.intro (Eval.appE R1 R2) ?_
  vrel
  exact HasType.appE U1' U2

lemma VRel.appE :  LRelSubs.Kripke ρ →
    ⟨v,p⟩ ∈ V⟦□ (A ⟶ B)⟧ρ#ε → ⟨w,q⟩ ∈ V⟦◯ A⟧ρ#ε → ⟨v.appE w, r⟩ ∈ V⟦◯ B⟧ρ#ε := by
  intros WS IH1 IH2
  apply TRel'.VRel WS at IH1
  apply TRel'.VRel WS at IH2
  apply TRel.appE IH1 at IH2
  apply TRel.fromTRel' at IH2
  apply VRel.IsValue_TRel IH2

lemma TRel.tail {A : Typ} : t ∈ T'⟦A.sig⟧ρ#ε → t.tail ∈ T'⟦◯ A.sig⟧ρ#ε := by
  intros IH ε1 S
  obtain ⟨ v, ε2 , R , U ⟩ := (IH S).elim
  vrel at U
  rcases U with ⟨l, rfl, s, L, Q, U⟩
  refine TRel.intro (Eval.tail R) ?_
  vrel
  constructor; constructor
  rw[Heap.type_lookup]; simp
  exists s

lemma VRel.tail {A : Typ} : LRelSubs.Kripke ρ → ⟨v,p⟩ ∈ V⟦A.sig⟧ρ#ε → ⟨v.tail, q⟩ ∈ V⟦◯ A.sig⟧ρ#ε := by
  intros WS IH
  apply TRel'.VRel WS at IH
  apply TRel.tail at IH
  apply TRel.fromTRel' at IH
  apply VRel.IsValue_TRel IH

----------------------------------------------------------------------
-- Eval-surgery helpers                                              --
----------------------------------------------------------------------

lemma TRel.app_beta {D ρ} {body mf : Term}
    {mfv rest : MVal} {ε} :
    (mf, ε) ⇓ (mfv, ε) →
    (body.sub mfv.val).app rest.val ∈ T⟦D⟧ρ#ε →
    ((Term.lam body).app mf).app rest.val ∈ T⟦D⟧ρ#ε := by
  intro Rmf P
  obtain ⟨w, εw, Rw, Vw⟩ := P.elim
  cases Rw with
  | value V => nomatch V
  | app R1 R2 R3 =>
      exact TRel.intro (Eval.app (Eval.app (Eval.value IsMValue.lam) Rmf R1) R2 R3) Vw

lemma TRel.fix_beta {D ρ} {t : Term} {x : MVal} {ε} :
    (t.sub (Term.delay (Term.fix t))).app x.val ∈ T⟦D⟧ρ#ε →
    (Term.fix t).app x.val ∈ T⟦D⟧ρ#ε := by
  intro P
  obtain ⟨w, εw, Rw, Vw⟩ := P.elim
  cases Rw with
  | value V => nomatch V
  | app R1 R2 R3 => exact TRel.intro (Eval.app (Eval.fix R1) R2 R3) Vw

lemma TRel.app_lam_value {D ρ} {body : Term} {x : MVal} {ε} :
    body.sub x.val ∈ T⟦D⟧ρ#ε →
    (Term.lam body).app x.val ∈ T⟦D⟧ρ#ε := by
  intro P
  obtain ⟨w, εw, Rw, Vw⟩ := P.elim
  exact TRel.intro (Eval.app (Eval.value IsMValue.lam) (Eval.value x.2) Rw) Vw

----------------------------------------------------------------------
-- Signal map (`smap`)                                               --
----------------------------------------------------------------------

/-- Mapping a function over a signal, two-environment form (the `sig`
case of the functorial-map lemma): the map function sends heads at `A`
over `ρin` into `B` over `ρout`; the mapped signal is then a signal of
`B` over `ρout`. -/
lemma VRel.smap_full {A B : Typ} {ρin ρout} {ε : Env}
    {mf} {mfv x : MVal} :
    LRelSubs.Kripke ρin → LRelSubs.Kripke ρout →
    ρin.Closed → ρout.Closed →
    A.Wf ρin.length → B.Wf ρout.length →
    (∀ {ε'}, ε.le ε' → (mf, ε') ⇓ (mfv, ε')) →
    ⊢{ε} mfv.val ∷ A.substAll ρin.types ⟶ B.substAll ρout.types →
    (∀ {ε' t} {y : MVal}, ε.le ε' → (t, ε') ⇓ (y, ε') →
        y ∈ V⟦A⟧ρin#ε' → mfv.val.app t ∈ T⟦B⟧ρout#ε') →
    x ∈ V⟦A.sig⟧ρin#ε →
    ((Term.smap (B.substAll ρout.types)).app mf).app x.val ∈ T⟦B.sig⟧ρout#ε := by
  intro WSin WSout hρin hρout hA hB Rmf Tmfv hHead hx
  have hAcl : (A.substAll ρin.types).Closed :=
    Typ.substAll_Wf_closed (by simpa using hA) hρin.types
  have hBcl : (B.substAll ρout.types).Closed :=
    Typ.substAll_Wf_closed (by simpa using hB) hρout.types
  have Tsmap : ⊢{ε} Term.smap (B.substAll ρout.types)
      ∷ (A.substAll ρin.types ⟶ B.substAll ρout.types)
        ⟶ (A.substAll ρin.types).sig ⟶ (B.substAll ρout.types).sig :=
    HasType.smap hAcl hBcl
  unfold Term.smap at Tsmap ⊢
  cases Tsmap with | lam _ Tsmap =>
  have hxloc : ∃ l, x.val = Term.loc l := by
    vrel at hx; obtain ⟨l, rfl, _⟩ := hx; exact ⟨l, rfl⟩
  obtain ⟨l, hxl⟩ := hxloc
  apply TRel.app_beta (Rmf (Env.refl ε))
  apply TRel.fix_beta
  apply TRel.app_lam_value
  have hmfvcl : ∀ (σ : Subs) (k : Nat), mfv.val.subs σ k = mfv.val :=
    fun σ k => HasType.closed Tmfv
  simp only [Term.sub, Term.subs, hmfvcl, hxl, Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd,
    List.length_singleton, Nat.lt_irrefl, List.get_eq_getElem, List.getElem_singleton,
    reduceDIte]
  apply TRel.fromTRel'
  apply TRel.sig hB WSout
  · -- head: the map applied to the current head of `x`
    intro ε' Sub
    have hx' := VRel.kripke WSin hx Sub
    vrel at hx'
    obtain ⟨l', hxl', s', hs'l, hs'type, hs'head⟩ := hx'
    have hll : Term.loc l = Term.loc l' := by rw [← hxl]; exact congrArg Subtype.val hxl'
    obtain rfl := (Term.loc.inj hll).symm
    exact hHead Sub (Eval.head (Eval.value IsMValue.loc) hs'l) hs'head
  · -- tail: a pure `◯`-typing leg through the empty environment
    have conv : ∀ {X Y : Typ} {ρ₁ ρ₂ : LRelSubs} {t : Term},
        X.substAll ρ₁.types = Y.substAll ρ₂.types →
        t ∈ T'⟦◯ X⟧ρ₁#ε → t ∈ T'⟦◯ Y⟧ρ₂#ε := by
      intro X Y ρ₁ ρ₂ t hXY h ε1 S
      obtain ⟨v, ε2, R, V⟩ := (h S).elim
      refine TRel.intro R ?_
      vrel at V ⊢
      rw [← hXY]
      exact V
    apply conv (X := (B.substAll ρout.types).sig) (ρ₁ := ρ0)
      (by simp only [Typ.substAll, LRelSubs.types_nil, Typ.substAll_nil])
    apply TRel.appE (A := (A.substAll ρin.types).sig)
      (B := (B.substAll ρout.types).sig)
    · refine TRel'.VRel LRelSubs.Kripke.nil
        (show (⟨_, IsMValue.delay⟩ : MVal) ∈
          V⟦□ ((A.substAll ρin.types).sig ⟶ (B.substAll ρout.types).sig)⟧ρ0#ε from ?_)
      vrel
      simp only [Typ.substAll, LRelSubs.types_nil, Typ.substAll_nil]
      exact HasType.delay (HasType.sub Tmfv Tsmap)
    · rw [← hxl]
      exact conv (Y := (A.substAll ρin.types).sig) (ρ₂ := ρ0)
        (by simp only [Typ.substAll, LRelSubs.types_nil, Typ.substAll_nil])
        (TRel.tail (TRel'.VRel WSin hx))

--------------------------------------------
-- Term-level plumbing for the N-ary fmap --
--------------------------------------------

lemma Typ.funcsTo_substAll : ∀ {Ss Cs T D},
    (Typ.funcsTo Ss Cs T).substAll D
      = Typ.funcsTo (Ss.map (·.substAll D)) (Cs.map (·.substAll D)) (T.substAll D) := by
  intro Ss
  induction Ss with
  | nil => intro Cs T D; rfl
  | cons S Ss' ih =>
      intro Cs T D
      cases Cs with
      | nil => rfl
      | cons C Cs' => simp only [Typ.funcsTo, Typ.substAll, List.map_cons]; rw [ih]

-- `Term.nlam` is injective in its body argument.
lemma Term.nlam_inj : ∀ {m t t'}, Term.nlam m t = Term.nlam m t' → t = t' := by
  intro m
  induction m with
  | zero => intro t t' h; exact h
  | succ k ih => intro t t' h; exact ih (Term.lam.inj h)

lemma Term.nlam_lam_inj {m a b} :
    Term.nlam m (Term.lam a) = Term.nlam m (Term.lam b) → a = b :=
  fun h => Term.lam.inj (Term.nlam_inj h)

-- `Term.fmap A Cs` is `nlam`-headed; expose its under-the-lambdas body.
-- (`Term.fmap` is recursive on `A`, so `isDefEq` will not unfold it for an
-- abstract `A`, but the equational lemma does.)
lemma Term.fmap_nlam (A : Typ) (Cs : List Typ) :
    ∃ b, Term.fmap A Cs = Term.nlam Cs.length (Term.lam b) := by
  unfold Term.fmap; exact ⟨_, rfl⟩

-- Substitution-composition for closed-entry substitutions: substituting `γ` at
-- offset `i+1` and then a single `s` at offset `i` equals one substitution of
-- `s :: γ` at offset `i`.
lemma Term.subs_subs_closed {γ : List Term} {s} :
    (∀ g ∈ γ, ∀ (σ : Subs) (k : Nat), g.subs σ k = g) →
    ∀ {t : Term} {i}, (t.subs γ (i+1)).subs [s] i = t.subs (s :: γ) i := by
  intro hγ t
  induction t <;> intro i
  case var x =>
    by_cases h1 : x < i + 1
    · rw [show (Term.var x).subs γ (i+1) = Term.var x from by simp only [Term.subs, dif_pos h1]]
      by_cases h2 : x < i
      · simp only [Term.subs, dif_pos h2]
      · have hxi : x = i := by omega
        subst hxi
        rw [show (Term.var x).subs [s] x = s from by
              simp only [Term.subs, dif_neg (Nat.lt_irrefl x)]
              rw [dif_pos (show x - x < [s].length by simp)]; simp [List.get_eq_getElem],
            show (Term.var x).subs (s :: γ) x = s from by
              simp only [Term.subs, dif_neg (Nat.lt_irrefl x)]
              rw [dif_pos (show x - x < (s :: γ).length by simp)]; simp [List.get_eq_getElem]]
    · by_cases h3 : x - (i + 1) < γ.length
      · rw [show (Term.var x).subs γ (i+1) = γ.get ⟨x - (i+1), h3⟩ from by
              simp only [Term.subs, dif_neg h1, dif_pos h3],
            hγ _ (List.get_mem _ _),
            show (Term.var x).subs (s :: γ) i = γ.get ⟨x - (i+1), h3⟩ from by
              simp only [Term.subs, dif_neg (show ¬ x < i by omega)]
              rw [dif_pos (show x - i < (s :: γ).length by simp only [List.length_cons]; omega)]
              simp [List.get_eq_getElem, show x - i = (x - (i+1)) + 1 by omega,
                List.getElem_cons_succ]]
      · rw [show (Term.var x).subs γ (i+1) = Term.var x from by
              simp only [Term.subs, dif_neg h1, dif_neg h3],
            show (Term.var x).subs [s] i = Term.var x from by
              simp only [Term.subs, dif_neg (show ¬ x < i by omega)]
              rw [dif_neg (show ¬ x - i < [s].length by simp; omega)],
            show (Term.var x).subs (s :: γ) i = Term.var x from by
              simp only [Term.subs, dif_neg (show ¬ x < i by omega)]
              rw [dif_neg (show ¬ x - i < (s :: γ).length by simp only [List.length_cons]; omega)]]
  all_goals (simp only [Term.subs]; try (congr 1 <;> simp_all))

-- Inversion of `HasType.nlam_funcsTo`: a `fmap`-shaped value `nlam (lam body)`
-- typed at `funcsTo Ss Cs (Sx ⟶ Tx)` exposes its body typed in the peeled
-- context (the `m` function binders, reversed, plus the value binder `Sx`).
lemma HasType.nlam_funcsTo_inv {H Δ} :
    ∀ {Ss Cs : List Typ} {body Sx Tx Γ},
    Ss.length = Cs.length →
    Γ ⊢[Δ, H] Term.nlam Cs.length (Term.lam body) ∷ Typ.funcsTo Ss Cs (Sx ⟶ Tx) →
    (Sx :: (List.zipWith (fun S C => S ⟶ C) Ss Cs).reverse ++ Γ) ⊢[Δ, H] body ∷ Tx := by
  intro Ss
  induction Ss with
  | nil =>
      intro Cs body Sx Tx Γ hlen hb
      cases Cs with
      | nil =>
          simp only [Term.nlam, Typ.funcsTo] at hb
          cases hb with | lam _ hb => simpa using hb
      | cons => simp at hlen
  | cons S Ss' ih =>
      intro Cs body Sx Tx Γ hlen hb
      cases Cs with
      | nil => simp at hlen
      | cons C Cs' =>
          simp only [Term.nlam, Typ.funcsTo] at hb
          cases hb with | lam _ hb =>
          have := ih (by simpa using hlen) hb
          simpa [List.zipWith_cons_cons, List.reverse_cons, List.append_assoc] using this

-- Append an element to the end of a `SubsType` (mirrors `List.concat`/snoc).
lemma SubsType.snoc {H Δ} {γ : List Term} {Γ t A} :
    ⊢C[Δ, H] γ ∷ Γ → (⊢[Δ, H] t ∷ A) → ⊢C[Δ, H] (γ ++ [t]) ∷ (Γ ++ [A]) := by
  intro G hT
  induction G with
  | nil => exact SubsType.cons hT SubsType.nil
  | cons hh _ ih => exact SubsType.cons hh ih

-- The reversed list of fmap function-VALUES is a well-typed substitution for the
-- reversed `funcsTo` context, given each value is typed at its `Ssᵢ ⟶ Csᵢ`.
lemma SubsType.of_fns {H Δ} :
    ∀ {Ss Cs : List Typ} {fns : List MVal},
    Ss.length = Cs.length → fns.length = Cs.length →
    (∀ i (hiS : i < Ss.length) (hiC : i < Cs.length) (hif : i < fns.length),
        (⊢[Δ, H] (fns[i]'hif).val ∷ Ss[i]'hiS ⟶ Cs[i]'hiC)) →
    ⊢C[Δ, H] (fns.reverse.map Subtype.val) ∷ (List.zipWith (fun S C => S ⟶ C) Ss Cs).reverse := by
  intro Ss
  induction Ss with
  | nil =>
      intro Cs fns hlen hflen _
      cases Cs with
      | nil => cases fns with
        | nil => exact SubsType.nil
        | cons => simp at hflen
      | cons => simp at hlen
  | cons S Ss' ih =>
      intro Cs fns hlen hflen hg
      cases Cs with
      | nil => simp at hlen
      | cons C Cs' =>
          cases fns with
          | nil => simp at hflen
          | cons f fns' =>
              simp only [List.zipWith_cons_cons, List.reverse_cons, List.map_append, List.map_cons,
                List.map_nil]
              refine SubsType.snoc (ih (by simpa using hlen) (by simpa using hflen) ?_) ?_
              · intro i hiS hiC hif
                have := hg (i + 1) (by simp only [List.length_cons]; omega)
                  (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
                simpa using this
              · have := hg 0 (by simp) (by simp) (by simp); simpa using this

-- Typing of the fmap-applied VALUE (the map function after its `|Cs|` function
-- arguments are supplied): `fmap A Cs` applied to `fns` β-reduces to
-- `lam (body.subs fns.reverse 1)`, which is typed `A.substAll Ss ⟶ A.substAll Cs`.
lemma HasType.fmap_value_typed {H Δ} {A : Typ} {Ss Cs : List Typ}
    {fns : List MVal} {body} :
    A.Wf Cs.length → Ss.length = Cs.length →
    (∀ S ∈ Ss, S.Closed) → (∀ C ∈ Cs, C.Closed) →
    Term.fmap A Cs = Term.nlam Cs.length (Term.lam body) →
    fns.length = Cs.length →
    (∀ i (hiS : i < Ss.length) (hiC : i < Cs.length) (hif : i < fns.length),
        (⊢[Δ, H] (fns[i]'hif).val ∷ Ss[i]'hiS ⟶ Cs[i]'hiC)) →
    (⊢[Δ, H] Term.lam (body.subs (fns.reverse.map Subtype.val) 1) ∷
      (A.substAll Ss ⟶ A.substAll Cs)) := by
  intro hWf hSlen hSc hCc hbody hflen hfns
  have Tg : (⊢[Δ, H] Term.fmap A Cs ∷
      Typ.funcsTo Ss Cs (A.substAll Ss ⟶ A.substAll Cs)) := HasType.fmap hWf hSlen hSc hCc
  rw [hbody] at Tg
  have Tbody := HasType.nlam_funcsTo_inv hSlen Tg
  apply HasType.lam (Typ.substAll_Wf_closed (by rw [hSlen]; exact hWf) hSc)
  have := HasType.subs (Γ := [A.substAll Ss]) (SubsType.of_fns hSlen hflen hfns)
    (by simpa using Tbody)
  simpa using this

-- Operational multi-β peeling for the `fmap` value: applying the `nlam`-headed
-- body to its function values peels the `|fns|` function lambdas, leaving the
-- value lambda with the (reversed) functions substituted at offset `1`.
lemma Eval.apps_nlam : ∀ {fns : List MVal} {body ε hd},
    (∀ fn ∈ fns, ∀ (σ : Subs) (k : Nat), fn.val.subs σ k = fn.val) →
    (hd, ε) ⇓ (⟨Term.nlam fns.length (Term.lam body), IsMValue.nlam_lam⟩, ε) →
    (hd.apps (fns.map Subtype.val), ε)
      ⇓ (⟨Term.lam (body.subs (fns.reverse.map Subtype.val) 1), IsMValue.lam⟩, ε) := by
  intro fns
  induction fns with
  | nil =>
      intro body ε hd hfcl Rhd
      simp only [Term.nlam, List.map_nil, Term.apps, List.reverse_nil,
        Subs.empty] at Rhd ⊢
      exact Rhd
  | cons fn fns' ih =>
      intro body ε hd hfcl Rhd
      simp only [List.map_cons, Term.apps]
      have hlen' : (fns'.reverse.map Subtype.val).length = fns'.length := by simp
      have hbeq : body.subs ((fn :: fns').reverse.map Subtype.val) 1
            = (body.subs [fn.val] (fns'.length + 1)).subs (fns'.reverse.map Subtype.val) 1 := by
        rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
          ← Term.subs_one_append (hfcl fn (by simp))
            (δ := fns'.reverse.map Subtype.val) (j := 1), hlen', Nat.add_comm 1 fns'.length]
      rw [hbeq]
      refine ih (body := body.subs [fn.val] (fns'.length + 1))
        (fun f hf => hfcl f (List.mem_cons_of_mem _ hf)) ?_
      refine Eval.app Rhd (Eval.value fn.2) ?_
      rw [show (Term.nlam fns'.length (Term.lam body)).sub fn.val
            = Term.nlam fns'.length (Term.lam (body.subs [fn.val] (fns'.length + 1))) by
          simp only [Term.sub, Term.subs_nlam, Term.subs, Nat.zero_add]]
      exact Eval.value IsMValue.nlam_lam

-- Applying `fmap F Cs'` via `apps` to its function values and then to an
-- argument that evaluates to `y` lands wherever the peeled body-substitution
-- lands.  Lets a peeled recursive hypothesis discharge `apps`-application
-- forms produced by the `fmap` constructor cases.
lemma TRel.fmap_apps_app {F Cs'} {fns : List MVal} {body}
    {y : MVal} {tgt ρ ε ε' t} :
    Term.fmap F Cs' = Term.nlam Cs'.length (Term.lam body) →
    fns.length = Cs'.length →
    (∀ fn ∈ fns, ∀ (σ : Subs) (k : Nat), fn.val.subs σ k = fn.val) →
    (t, ε) ⇓ (y, ε') →
    body.subs (y.val :: fns.reverse.map Subtype.val) 0 ∈ T⟦tgt⟧ ρ # ε' →
    ((Term.fmap F Cs').apps (fns.map Subtype.val)).app t ∈ T⟦tgt⟧ ρ # ε := by
  intro hbody hflen hfcl Rt h
  have hσ : ∀ g ∈ fns.reverse.map Subtype.val, ∀ (σ : Subs) (k : Nat), g.subs σ k = g := by
    intro g hg σ k
    simp only [List.mem_map, List.mem_reverse] at hg
    obtain ⟨fn, hfn, rfl⟩ := hg
    exact hfcl fn hfn σ k
  obtain ⟨w, εw, Rw, Vw⟩ := h.elim
  rw [hbody, ← hflen]
  refine TRel.intro (Eval.app (Eval.apps_nlam hfcl (Eval.value IsMValue.nlam_lam)) Rt ?_) Vw
  simp only [Term.sub]
  rw [Term.subs_subs_closed hσ]
  exact Rw

-- Value-level counterpart of `HasType.nlam_funcsTo` over an arbitrary
-- well-formed semantic environment: to place `nlam m (lam body)` in
-- `V⟦funcsTo Ss Cs (Sx ⟶ Tx)⟧ρ`, peel the `m` function arguments and the value
-- argument; the body must relate at `Tx` once the value and the reversed
-- function list are substituted in.  The typing hypothesis is at the
-- *collapsed* `funcsTo` type, matching what the `arr` case of `VRel` stores.
lemma VRel.nlam_funcsTo_env {ρ} (WS : LRelSubs.Kripke ρ) :
    ∀ {Ss Cs : List Typ} {body Sx Tx ε m},
    m = Cs.length →
    Ss.length = Cs.length →
    ⊢{ε} Term.nlam m (Term.lam body) ∷ (Typ.funcsTo Ss Cs (Sx ⟶ Tx)).substAll ρ.types →
    (∀ {ε'} (fns : List MVal) (x : MVal), ε.le ε' → fns.length = Cs.length →
        (∀ i (hiS : i < Ss.length) (hiC : i < Cs.length) (hif : i < fns.length),
            fns[i] ∈ V⟦Ss[i]'hiS ⟶ Cs[i]'hiC⟧ ρ # ε') →
        x ∈ V⟦Sx⟧ ρ # ε' →
        body.subs (x.val :: fns.reverse.map Subtype.val) 0 ∈ T⟦Tx⟧ ρ # ε') →
    (⟨Term.nlam m (Term.lam body), IsMValue.nlam_lam⟩ : MVal)
      ∈ V⟦Typ.funcsTo Ss Cs (Sx ⟶ Tx)⟧ ρ # ε := by
  intro Ss
  induction Ss with
  | nil =>
      intro Cs body Sx Tx ε m hm hlen T P
      subst hm
      cases Cs with
      | cons => simp at hlen
      | nil =>
          simp only [Term.nlam, Typ.funcsTo] at T
          show MVal.lam body ∈ V⟦Sx ⟶ Tx⟧ ρ # ε
          vrel
          refine ⟨T, body, rfl, ?_⟩
          intro ε' hsub v1 V1
          have := P [] v1 hsub rfl (by intro i hiS; simp at hiS) V1
          simpa [Term.sub] using this
  | cons S Ss' ih =>
      intro Cs body Sx Tx ε m hm hlen T P
      subst hm
      cases Cs with
      | nil => simp at hlen
      | cons C Cs' =>
          have hlen' : Ss'.length = Cs'.length := by simpa using hlen
          show MVal.lam (Term.nlam Cs'.length (Term.lam body))
              ∈ V⟦(S ⟶ C) ⟶ Typ.funcsTo Ss' Cs' (Sx ⟶ Tx)⟧ ρ # ε
          vrel
          refine ⟨by simpa [Typ.funcsTo, Term.nlam, List.length_cons] using T, _, rfl, ?_⟩
          intro ε' hsub f0 Vf0
          have Vf0' : f0 ∈ V⟦S ⟶ C⟧ ρ # ε' := by
            vrel
            exact Vf0
          have Tf0 : ⊢{ε'} f0.val ∷ (S ⟶ C).substAll ρ.types := Vf0.1
          have Tbody : [(S ⟶ C).substAll ρ.types] ⊢{ε'}
              Term.nlam Cs'.length (Term.lam body) ∷ (Typ.funcsTo Ss' Cs' (Sx ⟶ Tx)).substAll ρ.types := by
            have := (HasType.lam_inv (by simpa [Term.nlam, Typ.funcsTo, List.length_cons] using T)).le' hsub
            simpa [Term.nlam] using this
          have Tsub : ⊢{ε'} Term.nlam Cs'.length (Term.lam (body.subs [f0.val] (Cs'.length + 1)))
              ∷ (Typ.funcsTo Ss' Cs' (Sx ⟶ Tx)).substAll ρ.types := by
            have := HasType.sub Tf0 Tbody
            rwa [show (Term.nlam Cs'.length (Term.lam body)).sub f0.val
                  = Term.nlam Cs'.length (Term.lam (body.subs [f0.val] (Cs'.length + 1))) by
                simp only [Term.sub, Term.subs_nlam, Term.subs, Nat.zero_add]] at this
          have hf0cl : ∀ s k, f0.val.subs s k = f0.val := fun s k => HasType.closed Tf0
          rw [show (Term.nlam Cs'.length (Term.lam body)).sub f0.val
                = Term.nlam Cs'.length (Term.lam (body.subs [f0.val] (Cs'.length + 1))) by
              simp only [Term.sub, Term.subs_nlam, Term.subs, Nat.zero_add]]
          have key := ih (ε := ε') rfl hlen' Tsub ?_
          · exact TRel.intro (Eval.value IsMValue.nlam_lam) key
          · intro ε'' fns' x S' hflen' hg' Vx
            rw [show (body.subs [f0.val] (Cs'.length + 1)).subs (x.val :: fns'.reverse.map Subtype.val) 0
                  = body.subs (x.val :: (f0 :: fns').reverse.map Subtype.val) 0 by
                have hδ : (x.val :: fns'.reverse.map Subtype.val).length = Cs'.length + 1 := by
                  simp only [List.length_cons, List.length_map, List.length_reverse, hflen']
                rw [show Cs'.length + 1 = 0 + (x.val :: fns'.reverse.map Subtype.val).length by
                      rw [hδ]; omega,
                    Term.subs_one_append hf0cl]
                simp [List.reverse_cons]]
            refine P (f0 :: fns') x (hsub.trans S') (by simpa using hflen') ?_ Vx
            intro i hiS hiC hif
            cases i with
            | zero =>
                simp only [List.getElem_cons_zero]
                exact VRel.kripke WS Vf0' S'
            | succ j =>
                simp only [List.getElem_cons_succ]
                have := hg' j (by simpa using hiS) (by simpa using hiC) (by simpa using hif)
                simpa using this

-- Substituting a list `Fs` into the identity variables reproduces `Fs`.
lemma rangeVar_map_substAll (Fs : List Typ) :
    ((List.range Fs.length).map Typ.var).map (·.substAll Fs) = Fs := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, Typ.substAll, List.getD_eq_getElem?_getD,
               List.getElem?_eq_getElem h2, Option.getD_some]

-- Substituting a shifted type along a list with one extra entry at the shift
-- position skips that entry (the type-level "dead environment entry" lemma;
-- the relation-level counterpart is `VRel.shift_insert`).
lemma Typ.substAll_shift_insert : ∀ {A : Typ} {c} {L1 L2 : List Typ} {X},
    c = L1.length → A.Wf (L1.length + L2.length) →
    (A.shift c).substAll (L1 ++ X :: L2) = A.substAll (L1 ++ L2) := by
  intro A
  induction A with
  | unit => intro c L1 L2 X hc _; rfl
  | prod A1 A2 ih1 ih2 =>
      intro c L1 L2 X hc hW; cases hW with | prod h1 h2 =>
      simp only [Typ.shift, Typ.substAll]; rw [ih1 hc h1, ih2 hc h2]
  | sum A1 A2 ih1 ih2 =>
      intro c L1 L2 X hc hW; cases hW with | sum h1 h2 =>
      simp only [Typ.shift, Typ.substAll]; rw [ih1 hc h1, ih2 hc h2]
  | arr A1 A2 ih1 ih2 =>
      intro c L1 L2 X hc hW; cases hW with | arr h1 h2 =>
      simp only [Typ.shift, Typ.substAll]
      rw [ih1 hc (h1.mono (Nat.zero_le _)), ih2 hc h2]
  | delayA A' ih =>
      intro c L1 L2 X hc hW; cases hW with | delayA h =>
      simp only [Typ.shift, Typ.substAll]; rw [ih hc (h.mono (Nat.zero_le _))]
  | delayE A' ih =>
      intro c L1 L2 X hc hW; cases hW with | delayE h =>
      simp only [Typ.shift, Typ.substAll]; rw [ih hc (h.mono (Nat.zero_le _))]
  | chan A' ih =>
      intro c L1 L2 X hc hW; cases hW with | chan h =>
      simp only [Typ.shift, Typ.substAll]; rw [ih hc (h.mono (Nat.zero_le _))]
  | sig A' ih =>
      intro c L1 L2 X hc hW; cases hW with | sig h =>
      simp only [Typ.shift, Typ.substAll]; rw [ih hc h]
  | var i =>
      intro c L1 L2 X hc hW; cases hW with | var hi' =>
      subst hc
      simp only [Typ.shift]
      by_cases hi : i < L1.length
      · simp only [if_pos hi, Typ.substAll, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hi]
      · have hlt : i - L1.length < L2.length := by omega
        simp only [if_neg hi, Typ.substAll, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show L1.length ≤ i + 1 by omega),
          List.getElem?_append_right (show L1.length ≤ i by omega),
          show i + 1 - L1.length = (i - L1.length) + 1 by omega,
          List.getElem?_cons_succ, List.getElem?_eq_getElem hlt, Option.getD_some]
  | mu A' ih =>
      intro c L1 L2 X hc hW; cases hW with | mu h =>
      simp only [Typ.shift, Typ.substAll]
      rw [List.map_append, List.map_cons, ← List.cons_append,
          ih (show c + 1 = (Typ.var 0 :: L1.map (Typ.shift 0)).length by simp [hc])
             (show A'.Wf ((Typ.var 0 :: L1.map (Typ.shift 0)).length
                  + (L2.map (Typ.shift 0)).length) by
                rw [show (Typ.var 0 :: L1.map (Typ.shift 0)).length
                      + (L2.map (Typ.shift 0)).length = L1.length + L2.length + 1 by
                    simp; omega]
                exact h),
          List.map_append, List.cons_append]

/-- Iterated `shift 0`: `Typ.shiftN p Y` raises every free variable of
`Y` by `p` — the form a type written over a suffix environment takes
when it sits below a prefix of `p` entries. -/
def Typ.shiftN (p : Nat) (Y : Typ) : Typ :=
  match p with
  | 0 => Y
  | p + 1 => (Typ.shiftN p Y).shift 0

@[simp] lemma Typ.shiftN_zero {Y} : Typ.shiftN 0 Y = Y := rfl

lemma Typ.shiftN_succ {p Y} :
    Typ.shiftN (p + 1) Y = (Typ.shiftN p Y).shift 0 := rfl

lemma Typ.shiftN_Wf : ∀ {p k} {Y : Typ}, Y.Wf k → (Typ.shiftN p Y).Wf (p + k) := by
  intro p
  induction p with
  | zero => intro k Y h; simpa using h
  | succ p ih =>
      intro k Y h
      rw [Typ.shiftN_succ, show p + 1 + k = p + k + 1 from by omega]
      exact (ih h).shift (Nat.zero_le _)

-- Substituting an iterated shift along `Ds ++ L` skips the `Ds` prefix.
lemma Typ.shiftN_substAll_append : ∀ {Ds : List Typ} {Y : Typ} {L : List Typ},
    Y.Wf L.length →
    (Typ.shiftN Ds.length Y).substAll (Ds ++ L) = Y.substAll L := by
  intro Ds
  induction Ds with
  | nil => intro Y L _; simp
  | cons D Ds' ih =>
      intro Y L hY
      have h := Typ.substAll_shift_insert (A := Typ.shiftN Ds'.length Y) (c := 0) (L1 := [])
        (L2 := Ds' ++ L) (X := D) rfl
        (by simpa using Typ.shiftN_Wf (p := Ds'.length) hY)
      simp only [List.nil_append] at h
      rw [List.length_cons, Typ.shiftN_succ, List.cons_append, h]
      exact ih hY

/-- Relation-level dead-entry lemma: an entry inserted at position
`Δ.length` is invisible to (the shift at that cutoff of) a type that does
not mention it. -/
lemma VRel.shift_insert : ∀ {A : Typ} {Δ ρt : LRelSubs} {s ε v},
    A.Wf (Δ.length + ρt.length) →
    (v ∈ V⟦A.shift Δ.length⟧(Δ ++ s :: ρt)#ε ↔ v ∈ V⟦A⟧(Δ ++ ρt)#ε) := by
  intro A
  induction A with
  | unit => intro Δ ρt s ε v _; simp only [Typ.shift, _root_.VRel]
  | prod A1 A2 ih1 ih2 =>
      intro Δ ρt s ε v hW
      cases hW with | prod h1 h2 =>
      simp only [Typ.shift]
      exact VRel.prod_congr (fun _ => ih1 h1) (fun _ => ih2 h2)
  | sum A1 A2 ih1 ih2 =>
      intro Δ ρt s ε v hW
      cases hW with | sum h1 h2 =>
      simp only [Typ.shift]
      exact VRel.sum_congr (fun _ => ih1 h1) (fun _ => ih2 h2)
  | arr A1 A2 ih1 ih2 =>
      intro Δ ρt s ε v hW
      cases hW with | arr h1 h2 =>
      have hty : ((A1 ⟶ A2).shift Δ.length).substAll (Δ ++ s :: ρt).types
          = (A1 ⟶ A2).substAll (Δ ++ ρt).types := by
        rw [LRelSubs.types_append, LRelSubs.types_cons, LRelSubs.types_append]
        exact Typ.substAll_shift_insert (by simp) (by simpa using Typ.Wf.arr h1 h2)
      have hsh1 : A1.shift Δ.length = A1 := Typ.shift_closed h1
      simp only [Typ.shift] at hty ⊢
      refine VRel.arr_congr hty ?_ (fun _ _ => ih2 h2)
      intro ε'' v1
      rw [hsh1]
      exact ⟨fun h => VRel.type_closed h1 h, fun h => VRel.type_closed h1 h⟩
  | delayA B _ =>
      intro Δ ρt s ε v hW
      have hCcl : (□ B).Closed := by cases hW with | delayA h => exact .delayA h
      rw [Typ.shift_closed hCcl]
      exact ⟨VRel.type_closed hCcl, VRel.type_closed hCcl⟩
  | delayE B _ =>
      intro Δ ρt s ε v hW
      have hCcl : (◯ B).Closed := by cases hW with | delayE h => exact .delayE h
      rw [Typ.shift_closed hCcl]
      exact ⟨VRel.type_closed hCcl, VRel.type_closed hCcl⟩
  | chan B _ =>
      intro Δ ρt s ε v hW
      have hCcl : (Typ.chan B).Closed := by cases hW with | chan h => exact .chan h
      rw [Typ.shift_closed hCcl]
      exact ⟨VRel.type_closed hCcl, VRel.type_closed hCcl⟩
  | sig B ih =>
      intro Δ ρt s ε v hW
      cases hW with | sig hB =>
      have hty : (B.shift Δ.length).substAll (Δ ++ s :: ρt).types
          = B.substAll (Δ ++ ρt).types := by
        rw [LRelSubs.types_append, LRelSubs.types_cons, LRelSubs.types_append]
        exact Typ.substAll_shift_insert (by simp) (by simpa using hB)
      simp only [Typ.shift]
      exact VRel.sig_congr hty (fun _ => ih hB)
  | var i =>
      intro Δ ρt s ε v hW
      cases hW with | var hi =>
      simp only [Typ.shift]
      by_cases hic : i < Δ.length
      · rw [if_pos hic]
        vrel
        rw [List.getElem?_append_left hic, List.getElem?_append_left hic]
      · rw [if_neg hic]
        vrel
        rw [List.getElem?_append_right (show Δ.length ≤ i + 1 by omega),
            List.getElem?_append_right (show Δ.length ≤ i by omega),
            show i + 1 - Δ.length = (i - Δ.length) + 1 by omega,
            List.getElem?_cons_succ]
  | mu B ih =>
      intro Δ ρt s ε v hW
      cases hW with | mu hB =>
      have hB' : B.Wf (Δ.length + 1 + ρt.length) := by
        rw [show Δ.length + 1 + ρt.length = Δ.length + ρt.length + 1 by omega]
        exact hB
      have hlabel : (B.shift (Δ.length + 1)).substAll
            (Typ.var 0 :: (Δ ++ s :: ρt).types.map (Typ.shift 0))
          = B.substAll (Typ.var 0 :: (Δ ++ ρt).types.map (Typ.shift 0)) := by
        simp only [LRelSubs.types_append, LRelSubs.types_cons, List.map_append, List.map_cons]
        rw [← List.cons_append, ← List.cons_append]
        exact Typ.substAll_shift_insert (by simp) (by simpa using hB')
      have hentry : (μ (B.shift (Δ.length + 1))).substAll (Δ ++ s :: ρt).types
          = (μ B).substAll (Δ ++ ρt).types := by
        simp only [Typ.substAll]
        exact congrArg Typ.mu hlabel
      have hq : LRel.lfp (VRel.muOper (B.shift (Δ.length + 1)) (Δ ++ s :: ρt))
          = LRel.lfp (VRel.muOper B (Δ ++ ρt)) := by
        apply LRel.lfp.congr_oper_iff
        intro X ε'' w
        simp only [VRel.muOper]
        constructor
        · rintro ⟨v', rfl, V⟩
          refine ⟨v', by rw [hlabel], ?_⟩
          rw [hentry] at V
          exact (ih (Δ := ⟨(μ B).substAll (Δ ++ ρt).types, X⟩ :: Δ)
            (by simpa using hB')).mp V
        · rintro ⟨v', rfl, V⟩
          refine ⟨v', by rw [hlabel], ?_⟩
          have V' := (ih (Δ := ⟨(μ B).substAll (Δ ++ ρt).types, X⟩ :: Δ) (s := s)
            (by simpa using hB')).mpr V
          rw [← hentry] at V'
          exact V'
      show v ∈ V⟦(μ B).shift Δ.length⟧(Δ ++ s :: ρt)#ε ↔ v ∈ V⟦μ B⟧(Δ ++ ρt)#ε
      simp only [Typ.shift]
      rw [VRel.mu_def, VRel.mu_def, hq]

/-- Iterated dead-entry elimination: a type written over the suffix `ρt`,
shifted past an entire prefix `Δ`, ignores the prefix. -/
lemma VRel.shiftN_insert : ∀ {Δ ρt : LRelSubs} {Y : Typ} {ε v},
    Y.Wf ρt.length →
    (v ∈ V⟦Typ.shiftN Δ.length Y⟧(Δ ++ ρt)#ε ↔ v ∈ V⟦Y⟧ρt#ε) := by
  intro Δ
  induction Δ with
  | nil => intro ρt Y ε v _; simp
  | cons s Δ' ih =>
      intro ρt Y ε v hY
      rw [List.length_cons, Typ.shiftN_succ, List.cons_append]
      constructor
      · intro h
        exact (ih hY).mp
          ((VRel.shift_insert (Δ := []) (by simpa using Typ.shiftN_Wf (p := Δ'.length) hY)).mp h)
      · intro h
        exact (VRel.shift_insert (Δ := [])
          (by simpa using Typ.shiftN_Wf (p := Δ'.length) hY)).mpr ((ih hY).mpr h)

-- Pushing `shift 0` through a `range'`-variable block bumps the start.
lemma Typ.range'_var_shift : ∀ {m k},
    ((List.range' k m).map Typ.var).map (Typ.shift 0) = (List.range' (k+1) m).map Typ.var := by
  intro m
  induction m with
  | zero => intro k; rfl
  | succ m ih =>
      intro k
      simp only [List.range'_succ, List.map_cons, ih, Typ.shift, if_neg (Nat.not_lt_zero k)]

-- A closed list is unaffected by `shift`.
lemma map_shift_closed {L : List Typ} :
    (∀ E ∈ L, E.Closed) → L.map (Typ.shift 0) = L := by
  intro h
  conv_rhs => rw [← List.map_id L]
  apply List.map_congr_left
  intro E hE
  exact Typ.shift_closed (h E hE)

-- Substituting the identity-variable prefix along `Fs` yields the prefix of `Fs`.
lemma rangeVar_map_substAll_take {c} {Fs : List Typ} :
    c ≤ Fs.length →
    ((List.range c).map Typ.var).map (·.substAll Fs) = Fs.take c := by
  intro hc
  apply List.ext_getElem
  · simp [Nat.min_eq_left hc]
  · intro j h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_take,
      Typ.substAll, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show j < Fs.length by omega), Option.getD_some]

-- Substituting the offset-variable suffix along `Fs` yields the suffix of `Fs`.
lemma rangeVar'_map_substAll_drop {c m} {Fs : List Typ} :
    Fs.length = c + m →
    ((List.range' c m).map Typ.var).map (·.substAll Fs) = Fs.drop c := by
  intro hlen
  apply List.ext_getElem
  · simp [hlen]
  · intro j h1 h2
    simp only [List.length_map, List.length_range'] at h1
    simp only [List.getElem_map, List.getElem_range', List.getElem_drop, Nat.one_mul,
      Typ.substAll, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < Fs.length by omega), Option.getD_some]

-- Composing the open-slot internalization list with a tail substitution
-- `Ds ++ L`: the prefix collapses into `Ds`, the (shifted) slot skips `Ds`
-- and composes into `Y.substAll L`, the suffix collapses into `L`.
lemma internalize_type_gen {C Y : Typ} {c m} {Ds L : List Typ} :
    C.Wf (c + 1 + m) → Y.Wf L.length → Ds.length = c → L.length = m →
    (C.substAll ((List.range c).map Typ.var
        ++ Typ.shiftN c Y :: (List.range' c m).map Typ.var)).substAll (Ds ++ L)
      = C.substAll (Ds ++ Y.substAll L :: L) := by
  intro hC hY hDs hL
  rw [Typ.substAll_substAll
        (by rw [show ((List.range c).map Typ.var
                  ++ Typ.shiftN c Y :: (List.range' c m).map Typ.var).length
                  = c + 1 + m from by
                simp only [List.length_append, List.length_map, List.length_range,
                  List.length_cons, List.length_range']
                omega]
            exact hC)]
  congr 1
  rw [List.map_append, List.map_cons, ← hDs, Typ.shiftN_substAll_append hY,
      rangeVar_map_substAll_take (by rw [List.length_append, hL]; omega),
      rangeVar'_map_substAll_drop (Fs := Ds ++ L) (by rw [List.length_append, hL]),
      List.take_left, List.drop_left]

/-- Compositionality (open-slot mid-position internalization): a type
`Y` written over the suffix `ρt`, substituted into the variable slot at
position `Δ.length`, is interpreted exactly as the pushed semantic
entry `⟨Y.substAll ρt.types, VRel Y ρt⟩`.  The µ-case is pure operator
congruence (no strong induction, no monotonicity). -/
lemma VRel.internalize : ∀ {C : Typ} {Y : Typ} {Δ ρt : LRelSubs} {ε v},
    Δ.Closed → ρt.Closed → Y.Wf ρt.length →
    C.Wf (Δ.length + 1 + ρt.length) →
    (v ∈ V⟦C.substAll ((List.range Δ.length).map Typ.var
          ++ Typ.shiftN Δ.length Y
            :: (List.range' Δ.length ρt.length).map Typ.var)⟧(Δ ++ ρt)#ε
     ↔ v ∈ V⟦C⟧(Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt)#ε) := by
  intro C
  induction C with
  | unit =>
      intro Y Δ ρt ε v _ _ _ _
      simp only [_root_.VRel, Typ.substAll]
  | prod C1 C2 ih1 ih2 =>
      intro Y Δ ρt ε v hΔcl hρtcl hYwf hC
      cases hC with | prod h1 h2 =>
      simp only [Typ.substAll]
      exact VRel.prod_congr (fun _ => ih1 hΔcl hρtcl hYwf h1) (fun _ => ih2 hΔcl hρtcl hYwf h2)
  | sum C1 C2 ih1 ih2 =>
      intro Y Δ ρt ε v hΔcl hρtcl hYwf hC
      cases hC with | sum h1 h2 =>
      simp only [Typ.substAll]
      exact VRel.sum_congr (fun _ => ih1 hΔcl hρtcl hYwf h1) (fun _ => ih2 hΔcl hρtcl hYwf h2)
  | arr C1 C2 ih1 ih2 =>
      intro Y Δ ρt ε v hΔcl hρtcl hYwf hC
      cases hC with | arr h1 h2 =>
      have hsub1 : C1.substAll ((List.range Δ.length).map Typ.var
            ++ Typ.shiftN Δ.length Y
              :: (List.range' Δ.length ρt.length).map Typ.var) = C1 :=
        Typ.substAll_closed h1 _
      have h1eq : (C1.substAll ((List.range Δ.length).map Typ.var
            ++ Typ.shiftN Δ.length Y
              :: (List.range' Δ.length ρt.length).map Typ.var)).substAll (Δ ++ ρt).types
          = C1.substAll
              (Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt).types := by
        rw [LRelSubs.types_append,
            internalize_type_gen (h1.mono (Nat.zero_le _)) (by simpa using hYwf)
              (by simp) (by simp),
            LRelSubs.types_append, LRelSubs.types_cons]
      have h2eq : (C2.substAll ((List.range Δ.length).map Typ.var
            ++ Typ.shiftN Δ.length Y
              :: (List.range' Δ.length ρt.length).map Typ.var)).substAll (Δ ++ ρt).types
          = C2.substAll
              (Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt).types := by
        rw [LRelSubs.types_append,
            internalize_type_gen h2 (by simpa using hYwf)
              (by simp) (by simp),
            LRelSubs.types_append, LRelSubs.types_cons]
      simp only [Typ.substAll]
      refine VRel.arr_congr ?_ ?_ (fun _ _ => ih2 hΔcl hρtcl hYwf h2)
      · simp only [Typ.substAll]; rw [h1eq, h2eq]
      · intro ε'' v1
        rw [hsub1]
        exact ⟨fun h => VRel.type_closed h1 h, fun h => VRel.type_closed h1 h⟩
  | delayA B _ =>
      intro Y Δ ρt ε v _ _ _ hC
      have hCcl : (□ B).Closed := by cases hC with | delayA h => exact .delayA h
      rw [Typ.substAll_closed hCcl]
      exact ⟨VRel.type_closed hCcl, VRel.type_closed hCcl⟩
  | delayE B _ =>
      intro Y Δ ρt ε v _ _ _ hC
      have hCcl : (◯ B).Closed := by cases hC with | delayE h => exact .delayE h
      rw [Typ.substAll_closed hCcl]
      exact ⟨VRel.type_closed hCcl, VRel.type_closed hCcl⟩
  | chan B _ =>
      intro Y Δ ρt ε v _ _ _ hC
      have hCcl : (Typ.chan B).Closed := by cases hC with | chan h => exact .chan h
      rw [Typ.substAll_closed hCcl]
      exact ⟨VRel.type_closed hCcl, VRel.type_closed hCcl⟩
  | sig B ih =>
      intro Y Δ ρt ε v hΔcl hρtcl hYwf hC
      cases hC with | sig hB =>
      have hsigty : (B.substAll ((List.range Δ.length).map Typ.var
            ++ Typ.shiftN Δ.length Y
              :: (List.range' Δ.length ρt.length).map Typ.var)).substAll (Δ ++ ρt).types
          = B.substAll (Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt).types := by
        rw [LRelSubs.types_append,
            internalize_type_gen hB (by simpa using hYwf) (by simp) (by simp),
            LRelSubs.types_append, LRelSubs.types_cons]
      simp only [Typ.substAll]
      exact VRel.sig_congr hsigty (fun _ => ih hΔcl hρtcl hYwf hB)
  | var i =>
      intro Y Δ ρt ε v hΔcl hρtcl hYwf hC
      cases hC with | var hi =>
      by_cases hiΔ : i < Δ.length
      · have hty : (Typ.var i).substAll ((List.range Δ.length).map Typ.var
              ++ Typ.shiftN Δ.length Y
                :: (List.range' Δ.length ρt.length).map Typ.var) = Typ.var i := by
          simp only [Typ.substAll, List.getD_eq_getElem?_getD, Typ.getElem?_rangeVar_append,
                     if_pos hiΔ, Option.getD_some]
        rw [hty]
        vrel
        rw [List.getElem?_append_left hiΔ, List.getElem?_append_left hiΔ]
      · by_cases hieq : i = Δ.length
        · subst hieq
          have hty : (Typ.var Δ.length).substAll ((List.range Δ.length).map Typ.var
                ++ Typ.shiftN Δ.length Y
                  :: (List.range' Δ.length ρt.length).map Typ.var)
              = Typ.shiftN Δ.length Y := by
            simp only [Typ.substAll, List.getD_eq_getElem?_getD, Typ.getElem?_rangeVar_append,
                       if_neg (Nat.lt_irrefl Δ.length), Nat.sub_self,
                       List.getElem?_cons_zero, Option.getD_some]
          rw [hty]
          constructor
          · intro hv
            have hvY : v ∈ V⟦Y⟧ρt#ε := (VRel.shiftN_insert hYwf).mp hv
            have T : ⊢{ε} v ∷ Y.substAll ρt.types :=
              VRel.HasType_open hρtcl hYwf hvY
            vrel
            refine ⟨⟨Y.substAll ρt.types, VRel Y ρt⟩, ?_, T, hvY⟩
            rw [List.getElem?_append_right (Nat.le_refl Δ.length), Nat.sub_self,
                List.getElem?_cons_zero]
          · intro hv
            vrel at hv
            obtain ⟨s, hs, T, R⟩ := hv
            rw [List.getElem?_append_right (Nat.le_refl Δ.length), Nat.sub_self,
                List.getElem?_cons_zero] at hs
            obtain rfl := Option.some.inj hs
            exact (VRel.shiftN_insert hYwf).mpr R
        · have hi1 : Δ.length < i := by omega
          have hjm : i - Δ.length - 1 < ρt.length := by omega
          have hty : (Typ.var i).substAll ((List.range Δ.length).map Typ.var
                ++ Typ.shiftN Δ.length Y
                  :: (List.range' Δ.length ρt.length).map Typ.var) = Typ.var (i - 1) := by
            simp only [Typ.substAll, List.getD_eq_getElem?_getD, Typ.getElem?_rangeVar_append,
                       if_neg hiΔ]
            rw [show i - Δ.length = (i - Δ.length - 1) + 1 from by omega,
                List.getElem?_cons_succ, List.getElem?_map, List.getElem?_range' hjm,
                Option.map_some, Option.getD_some,
                show Δ.length + 1 * (i - Δ.length - 1) = i - 1 from by omega]
          rw [hty]
          vrel
          rw [List.getElem?_append_right (show Δ.length ≤ i - 1 by omega),
              List.getElem?_append_right (show Δ.length ≤ i by omega),
              show i - Δ.length = (i - Δ.length - 1) + 1 from by omega,
              List.getElem?_cons_succ,
              show i - 1 - Δ.length = i - Δ.length - 1 from by omega]
  | mu B ih =>
      intro Y Δ ρt ε v hΔcl hρtcl hYwf hC
      cases hC with | mu hB =>
      have hB' : B.Wf (Δ.length + 1 + 1 + ρt.length) := by
        rw [show Δ.length + 1 + 1 + ρt.length = Δ.length + 1 + ρt.length + 1 by omega]
        exact hB
      have hYscl : (Y.substAll ρt.types).Closed :=
        Typ.substAll_Wf_closed (by simpa using hYwf) hρtcl.types
      have hcl' : ∀ E ∈ Δ.types ++ ρt.types, E.Closed := by
        intro E hE
        rcases List.mem_append.mp hE with hE | hE
        exacts [hΔcl.types E hE, hρtcl.types E hE]
      have hallcl : ∀ E ∈ Δ.types ++ (Y.substAll ρt.types) :: ρt.types, E.Closed := by
        intro E hE
        rcases List.mem_append.mp hE with hE | hE
        · exact hΔcl.types E hE
        · headTail hE
          exacts [hYscl, hρtcl.types E hE]
      have htypesL : (Δ ++ ρt).types = Δ.types ++ ρt.types := LRelSubs.types_append _ _
      have htypesR : (Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt).types
          = Δ.types ++ (Y.substAll ρt.types) :: ρt.types := by
        rw [LRelSubs.types_append, LRelSubs.types_cons]
      -- the pushed list is again of (open-slot) internalization shape
      have hlist : Typ.var 0 :: ((List.range Δ.length).map Typ.var
            ++ Typ.shiftN Δ.length Y
              :: (List.range' Δ.length ρt.length).map Typ.var).map (Typ.shift 0)
          = (List.range (Δ.length + 1)).map Typ.var
            ++ Typ.shiftN (Δ.length + 1) Y
              :: (List.range' (Δ.length + 1) ρt.length).map Typ.var := by
        rw [List.map_append, List.map_cons, ← List.cons_append, Typ.var0_cons_rangeVar_shift,
            ← Typ.shiftN_succ, Typ.range'_var_shift]
      have hBseq : B.substAll (Typ.var 0 :: ((List.range Δ.length).map Typ.var
            ++ Typ.shiftN Δ.length Y
              :: (List.range' Δ.length ρt.length).map Typ.var).map (Typ.shift 0))
          = B.substAll ((List.range (Δ.length + 1)).map Typ.var
            ++ Typ.shiftN (Δ.length + 1) Y
              :: (List.range' (Δ.length + 1) ρt.length).map Typ.var) :=
        congrArg (fun L => B.substAll L) hlist
      -- the cons-label / entry-type equalities
      have hlabel : (B.substAll ((List.range (Δ.length + 1)).map Typ.var
            ++ Typ.shiftN (Δ.length + 1) Y
              :: (List.range' (Δ.length + 1) ρt.length).map Typ.var)).substAll
              (Typ.var 0 :: (Δ ++ ρt).types.map (Typ.shift 0))
          = B.substAll (Typ.var 0
              :: (Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt).types.map
                  (Typ.shift 0)) := by
        rw [htypesL, htypesR, map_shift_closed hallcl, map_shift_closed hcl',
            ← List.cons_append, ← List.cons_append]
        exact internalize_type_gen hB' (by simpa using hYwf) (by simp) (by simp)
      have hentry : (μ (B.substAll ((List.range (Δ.length + 1)).map Typ.var
            ++ Typ.shiftN (Δ.length + 1) Y
              :: (List.range' (Δ.length + 1) ρt.length).map Typ.var))).substAll
              (Δ ++ ρt).types
          = (μ B).substAll (Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt).types := by
        simp only [Typ.substAll]
        exact congrArg Typ.mu hlabel
      have hμBcl : ((μ B).substAll
          (Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt).types).Closed := by
        rw [htypesR]
        refine Typ.substAll_Wf_closed ?_ hallcl
        refine Typ.Wf.mu ?_
        rw [show (Δ.types ++ (Y.substAll ρt.types) :: ρt.types).length + 1
              = Δ.length + 1 + ρt.length + 1 from by
              simp only [List.length_append, List.length_cons, LRelSubs.types_length]
              omega]
        exact hB
      have hq : LRel.lfp (VRel.muOper (B.substAll ((List.range (Δ.length + 1)).map Typ.var
            ++ Typ.shiftN (Δ.length + 1) Y
              :: (List.range' (Δ.length + 1) ρt.length).map Typ.var)) (Δ ++ ρt))
          = LRel.lfp (VRel.muOper B
              (Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt)) := by
        apply LRel.lfp.congr_oper_iff
        intro X ε'' w
        simp only [VRel.muOper]
        constructor
        · rintro ⟨w', rfl, hw'⟩
          refine ⟨w', by rw [hlabel], ?_⟩
          rw [hentry] at hw'
          exact (ih (Δ := ⟨(μ B).substAll
              (Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt).types, X⟩ :: Δ)
            (fun s hs => by
              headTail hs
              · exact hμBcl
              · exact hΔcl s hs)
            hρtcl hYwf (by simpa using hB')).mp hw'
        · rintro ⟨w', rfl, hw'⟩
          refine ⟨w', by rw [hlabel], ?_⟩
          have hw'' := (ih (Δ := ⟨(μ B).substAll
              (Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt).types, X⟩ :: Δ)
            (fun s hs => by
              headTail hs
              · exact hμBcl
              · exact hΔcl s hs)
            hρtcl hYwf (by simpa using hB')).mpr hw'
          rw [← hentry] at hw''
          exact hw''
      show VRel ((μ B).substAll ((List.range Δ.length).map Typ.var
            ++ Typ.shiftN Δ.length Y
              :: (List.range' Δ.length ρt.length).map Typ.var)) (Δ ++ ρt) ε v
          ↔ VRel (μ B) (Δ ++ (⟨Y.substAll ρt.types, VRel Y ρt⟩ : LRelOf) :: ρt) ε v
      simp only [Typ.substAll]
      rw [hBseq, VRel.mu_def, VRel.mu_def, hq]
