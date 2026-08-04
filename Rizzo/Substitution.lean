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
  | watch t' => watch (t'.subs s m)
  | newchan A => newchan A
  | chan κ => chan κ
  | select t1 t2 => select (t1.subs s m) (t2.subs s m)
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

inductive SubsType (H : HeapTy) (Δ : ChanCtx) : Subs → Ctx → Prop where
| nil : SubsType H Δ [] []
| cons : ⊢[Δ, H] t ∷ A → SubsType H Δ γ Γ → SubsType H Δ (t :: γ) (A :: Γ)

-- Substitution typing: `⊢C[Δ, H] γ ∷ Γ` types each term of substitution
-- `γ` against the matching type in `Γ` (under heap typing `H`, channels
-- `Δ`); `⊢C{ε}` takes `H`, `Δ` from the environment `ε`.
notation:50 (name := subs_type_notation) " ⊢C[" Δ ", " H "] " γ:60 " ∷ " Γ:60 => SubsType H Δ γ Γ
notation:50 (name := subs_type_env_notation) " ⊢C{" ε "} " γ:60 " ∷ " Γ:60 => SubsType (Heap.type (Env.now ε)) (Env.chans ε) γ Γ



--------------------------------
-- Lemmas about substitutions --
--------------------------------

lemma Subs.empty {t : Term} : t.subs [] i = t := by
  revert i
  induction t <;> intro i <;> try simp <;> try grind

-- Pushing a substitution through `nlam`'s `k` leading lambdas: the offset is
-- raised by `k` (used by the N-ary `fmap` value-relation peeler).
lemma Term.subs_nlam {t s} : ∀ {k m},
    (Term.nlam k t).subs s m = Term.nlam k (t.subs s (m + k)) := by
  intro k
  induction k with
  | zero => intro m; simp only [Term.nlam, Nat.add_zero]
  | succ k ih =>
      intro m
      simp only [Term.nlam, Term.subs]
      rw [ih, show m + 1 + k = m + (k + 1) from by omega]


lemma HasType.closed' :  Γ ⊢[Δ, H] t ∷ A → i ≥ Γ.length → t.subs γ i = t := by
  intros T; revert γ; revert i
  induction T <;> intro i γ L <;> simp <;> grind



lemma HasType.closed :  ⊢[Δ, H] t ∷ A → t.subs γ i = t := by
  intros T
  apply HasType.closed' T; grind


@[simp]
lemma Term.fmap₁_subs : 1 ⊢ A ∷type → ⊢ C ∷type → (Term.fmap₁ A C).subs s n = Term.fmap₁ A C := by
  intro W hC
  exact HasType.closed (H := ∅) (Δ := ∅) (HasType.fmap₁ (B := 𝟭) W Typ.Wf.unit hC)

@[simp]
lemma Term.smap_subs : (Term.smap B).subs s n = Term.smap B := by
  have h0 : 0 < n + 3 := by omega
  have h1 : 1 < n + 3 := by omega
  have h2 : 2 < n + 3 := by omega
  simp [Term.smap, h0, h1, h2]

------------------------------------------
-- Lemmas about typing of substitutions --
------------------------------------------


lemma SubsType.HasType {t} {γ : List Term} {Γ} {i : Nat}   :
  ⊢C[Δ, H] γ ∷ Γ → t ∈ γ[i]? → ∃ A : Typ , A ∈ Γ[i]? /\ ⊢[Δ, H] t ∷ A := by
  intros G L
  revert i
  induction G <;> intro i L
  case nil => simp at *
  case cons IH =>
    cases i
    case zero => simp at L;grind
    case succ => simp at *; apply IH L;

lemma SubsType.HasType' {t} {γ : List Term} {Γ} {i : Nat} :
  ⊢C[Δ, H] γ ∷ Γ → t ∈ γ[i]? → A ∈ Γ[i]? →  ⊢[Δ, H] t ∷ A := by
  intros G L L'
  apply SubsType.HasType G at L
  rcases L with ⟨A, E, T⟩
  rw [E] at L'
  cases L'
  assumption


lemma SubsType.length : ⊢C[Δ, H] γ ∷ Γ → γ.length = Γ.length := by
  intros G
  induction G <;> simp
  assumption




lemma SubsType.closed' {t} {γ'} {γ : List Term} {i : Nat} :
  ⊢C[Δ, H] γ ∷ Γ → γ[i]? = some t → t.subs γ' j = t := by
  intros T G
  have S := SubsType.HasType T G
  rcases S with ⟨A, T1, T2⟩
  apply HasType.closed<;> assumption





lemma SubsType.closed {γ'} {γ : List Term} {i}
  {p : i < γ.length} :  ⊢C[Δ, H] γ ∷ Γ → γ[i].subs γ' j = γ[i] := by
    intros T
    apply SubsType.closed'; assumption
    rw[getElem?_pos]


/-
Lemma for combining two substitutions
-/

lemma Term.subs_subs {t : Term} : ⊢C[Δ, H] γ ∷ Γ → (t.subs γ i.succ).subs [s] i = t.subs (s::γ) i := by
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

lemma Term.subs_one_append {f : Term} :
    (∀ s k, f.subs s k = f) →
    ∀ {t : Term} {δ : List Term} {j},
    (t.subs [f] (j + δ.length)).subs δ j = t.subs (δ ++ [f]) j := by
  intro hf t
  induction t with
  | var x =>
      intro δ j
      by_cases h1 : x < j + δ.length
      · have hin : (var x).subs [f] (j + δ.length) = var x := by simp [Term.subs, h1]
        rw [hin]
        by_cases h2 : x < j
        · simp [Term.subs, h2]
        · have e1 : x - j < δ.length := by omega
          have e1' : x - j < (δ ++ [f]).length := by simp; omega
          simp only [Term.subs, dif_neg h2, dif_pos e1, dif_pos e1']
          simp [List.get_eq_getElem, List.getElem_append_left e1]
      · by_cases h2 : x = j + δ.length
        · subst h2
          have hin : (var (j + δ.length)).subs [f] (j + δ.length) = f := by
            simp [Term.subs]
          rw [hin, hf]
          have e2 : ¬ j + δ.length < j := by omega
          have e2' : j + δ.length - j < (δ ++ [f]).length := by simp
          simp only [Term.subs, dif_neg e2, dif_pos e2']
          simp [List.get_eq_getElem]
        · have hin : (var x).subs [f] (j + δ.length) = var x := by
            simp only [Term.subs, dif_neg h1]
            rw [dif_neg (show ¬ x - (j + δ.length) < [f].length by simp; omega)]
          rw [hin]
          have e3 : ¬ x < j := by omega
          have e3' : ¬ x - j < (δ ++ [f]).length := by simp; omega
          simp only [Term.subs, dif_neg e3, dif_neg (show ¬ x - j < δ.length by omega), dif_neg e3']
  | lam u ih =>
      intro δ j
      simp only [Term.subs]
      rw [show j + δ.length + 1 = (j + 1) + δ.length from by omega, ih]
  | fix u ih =>
      intro δ j
      simp only [Term.subs]
      rw [show j + δ.length + 1 = (j + 1) + δ.length from by omega, ih]
  | recur B t1 t2 ih1 ih2 =>
      intro δ j
      simp only [Term.subs]
      rw [show j + δ.length + 1 = (j + 1) + δ.length from by omega, ih1, ih2]
  | case t1 t2 t3 ih1 ih2 ih3 =>
      intro δ j
      simp only [Term.subs]
      rw [ih1, show j + δ.length + 1 = (j + 1) + δ.length from by omega, ih2, ih3]
  | unit => intro δ j; rfl
  | newchan A => intro δ j; rfl
  | chan κ => intro δ j; rfl
  | loc l => intro δ j; rfl
  | never => intro δ j; rfl
  | pair t1 t2 ih1 ih2 => intro δ j; simp only [Term.subs]; rw [ih1, ih2]
  | app t1 t2 ih1 ih2 => intro δ j; simp only [Term.subs]; rw [ih1, ih2]
  | select t1 t2 ih1 ih2 => intro δ j; simp only [Term.subs]; rw [ih1, ih2]
  | appE t1 t2 ih1 ih2 => intro δ j; simp only [Term.subs]; rw [ih1, ih2]
  | appA t1 t2 ih1 ih2 => intro δ j; simp only [Term.subs]; rw [ih1, ih2]
  | sig A t1 t2 ih1 ih2 => intro δ j; simp only [Term.subs]; rw [ih1, ih2]
  | in1 t ih => intro δ j; simp only [Term.subs]; rw [ih]
  | in2 t ih => intro δ j; simp only [Term.subs]; rw [ih]
  | pr1 t ih => intro δ j; simp only [Term.subs]; rw [ih]
  | pr2 t ih => intro δ j; simp only [Term.subs]; rw [ih]
  | delay t ih => intro δ j; simp only [Term.subs]; rw [ih]
  | wait t ih => intro δ j; simp only [Term.subs]; rw [ih]
  | watch t ih => intro δ j; simp only [Term.subs]; rw [ih]
  | head t ih => intro δ j; simp only [Term.subs]; rw [ih]
  | tail t ih => intro δ j; simp only [Term.subs]; rw [ih]
  | cons A t ih => intro δ j; simp only [Term.subs]; rw [ih]

-- Substitution distributes over the N-ary application `apps f as`.
lemma Term.subs_apps {f as σ n} :
    (Term.apps f as).subs σ n = Term.apps (f.subs σ n) (as.map (·.subs σ n)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp only [Term.apps, List.map_cons, ih, Term.subs]

@[simp high] lemma Term.subs_var0 {a σ'} : (Term.var 0).subs (a :: σ') 0 = a := by
  simp [Term.subs]

@[simp high] lemma Term.subs_var_lt {i m σ} :
    i < m → (Term.var i).subs σ m = Term.var i := by intro h; simp [Term.subs, h]

-- `fmap A Cs` is closed (typeable in the empty context), so its term
-- substitution is the identity.
lemma Term.fmap_subs {A : Typ} {Cs : List Typ} {s n} :
    A.Wf Cs.length → (∀ C ∈ Cs, C.Closed) → (Term.fmap A Cs).subs s n = Term.fmap A Cs :=
  fun hWf hCc => HasType.closed (H := ∅) (Δ := ∅) (HasType.fmap hWf rfl hCc hCc)

-- The lookup performed by the `nlam_funcsTo` substitution on the `fmap`
-- function arguments: `var (m - i)` resolves to the `i`-th function value.
private lemma Term.sigma_lookup {m} (xt : Term) {fv : List MVal} (h : fv.length = m)
    {i} (hi : i < m) :
    (xt :: fv.reverse.map Subtype.val)[m - i]? = some (fv[i]'(by omega)).val := by
  have hmi : m - i = (m - i - 1) + 1 := by omega
  rw [hmi, List.getElem?_cons_succ, List.getElem?_map,
      List.getElem?_reverse (by rw [h]; omega)]
  have hidx : fv.length - 1 - (m - i - 1) = i := by omega
  rw [hidx, List.getElem?_eq_getElem (show i < fv.length by omega)]; rfl

-- A single `fmap` function argument `var (m - i)` (offset 0) resolves to the
-- `i`-th function value (used by the `var` case of the value-relation `fmap`).
lemma Term.subs_var_fns0 {m i xt} {fv : List MVal} (h : fv.length = m) (hi : i < m) :
    (Term.var (m - i)).subs (xt :: fv.reverse.map Subtype.val) 0 = (fv[i]'(by omega)).val := by
  have e2 : m - i < (xt :: fv.reverse.map Subtype.val).length := by
    simp only [List.length_cons, List.length_map, List.length_reverse, h]; omega
  simp only [Term.subs, Nat.sub_zero, dif_neg (show ¬ (m - i < 0) from by omega), dif_pos e2]
  have hlk := Term.sigma_lookup xt h hi
  rw [List.getElem?_eq_getElem e2] at hlk
  simp only [Option.some.injEq] at hlk
  rw [List.get_eq_getElem]; exact hlk

-- The `fmap` function-argument list `[var m, …, var 1]` (at offset 0) becomes the
-- actual function values once `nlam_funcsTo`'s substitution is applied.
lemma Term.fmap_fns_subs0 {m xt} {fv : List MVal} :
    fv.length = m →
    ((List.range m).map (fun j => Term.var (m - j))).map (·.subs (xt :: fv.reverse.map Subtype.val) 0)
      = fv.map Subtype.val := by
  intro h
  apply List.ext_getElem
  · simp [h]
  · intro i h1 _
    have hi : i < m := by simp only [List.length_map, List.length_range] at h1; exact h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_map]
    have e2 : m - i < (xt :: fv.reverse.map Subtype.val).length := by
      simp only [List.length_cons, List.length_map, List.length_reverse, h]; omega
    simp only [Term.subs, Nat.sub_zero, dif_neg (show ¬ (m - i < 0) from by omega), dif_pos e2]
    have hlk := Term.sigma_lookup xt h hi
    rw [List.getElem?_eq_getElem e2] at hlk
    simp only [Option.some.injEq] at hlk
    rw [List.get_eq_getElem]; exact hlk

-- The same, at offset 1 (`[var (m+1), …, var 2]`, inside a one-binder context
-- such as a `case` branch or a `recur` step).
lemma Term.fmap_fns_subs1 {m xt} {fv : List MVal} :
    fv.length = m →
    ((List.range m).map (fun j => Term.var (m + 1 - j))).map (·.subs (xt :: fv.reverse.map Subtype.val) 1)
      = fv.map Subtype.val := by
  intro h
  apply List.ext_getElem
  · simp [h]
  · intro i h1 _
    have hi : i < m := by simp only [List.length_map, List.length_range] at h1; exact h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_map]
    have e2 : m - i < (xt :: fv.reverse.map Subtype.val).length := by
      simp only [List.length_cons, List.length_map, List.length_reverse, h]; omega
    simp only [Term.subs, dif_neg (show ¬ (m + 1 - i < 1) from by omega),
      show m + 1 - i - 1 = m - i from by omega, dif_pos e2, List.get_eq_getElem]
    have hlk := Term.sigma_lookup xt h hi
    rw [List.getElem?_eq_getElem e2] at hlk
    simp only [Option.some.injEq] at hlk
    exact hlk


---------------------------------------------------
-- Typing judgement is closed under substitution --
---------------------------------------------------





lemma HasType.subs  :
  ⊢C[Δ, H] γ ∷ Γ' →
  (T : Γ ++ Γ' ⊢[Δ, H] t ∷ A) → Γ ⊢[Δ, H] t.subs γ Γ.length ∷  A  := by
  intros G T
  revert A Γ
  induction t <;> intros Γ A T <;> simp <;> try {cases T; constructor <;> grind}
  case app IH1 IH2 | appA IH1 IH2 =>
    cases T; constructor; apply IH1; assumption; apply IH2;assumption
  case appE IH1 IH2 =>
    cases T; constructor; apply IH1; assumption; apply IH2;assumption
  case recur IH1 IH2 =>
    cases T; constructor; assumption; assumption; apply IH1; assumption; apply IH2;assumption
  case pr1 IH1 | pr2 IH1 => cases T; constructor; apply IH1; assumption
  case case IH1 IH2 IH3 =>
    cases T with | case W1 W2 T1 T2 T3 =>
    exact HasType.case W1 W2 (IH1 T1) (IH2 T2) (IH3 T3)
  case var =>
    cases T with | var T
    split
    . constructor; apply List.isElem?_cons <;> assumption
    . split
      . apply HasType.weaken_closed; apply SubsType.HasType' G; rw[getElem?_pos];rfl;apply List.isElem?_cons' <;> assumption
      . constructor; apply SubsType.length at G; grind


lemma HasType.sub  :
  ⊢[Δ, H] s ∷ B →
  [B] ⊢[Δ, H] t ∷ A → ⊢[Δ, H] t.sub s ∷ A  := by
    intros T1 T2
    apply T2.subs
    solve_by_elim

lemma HasType.subs_top  :
  ⊢C[Δ, H] γ ∷ Γ →
  Γ ⊢[Δ, H] t ∷ A → ⊢[Δ, H] t.subs γ 0 ∷  A  := by
    intros G T
    apply HasType.subs ; assumption; simp; assumption

---------------------------
-- location substitution --
---------------------------

def Term.locSigSub (t : Term) (l : Loc) (A : Typ) (hd tl : Term) : Term :=
  match t with
  | tail (loc l') => if l' = l then tl else tail (loc l')
  | unit => unit
  | pair t1 t2 => pair (t1.locSigSub l A hd tl) (t2.locSigSub l A hd tl)
  | in1 t' => in1 (t'.locSigSub l A hd tl)
  | in2 t' => in2 (t'.locSigSub l A hd tl)
  | lam u => lam (u.locSigSub l A hd tl)
  | app t1 t2 => app (t1.locSigSub l A hd tl) (t2.locSigSub l A hd tl)
  | case t1 t2 t3 => case (t1.locSigSub l A hd tl) (t2.locSigSub l A hd tl) (t3.locSigSub l A hd tl)
  | pr1 t' => pr1 (t'.locSigSub l A hd tl)
  | pr2 t' => pr2 (t'.locSigSub l A hd tl)
  | delay t' => delay (t'.locSigSub l A hd tl)
  | never => never
  | wait t' => wait (t'.locSigSub l A hd tl)
  | watch t' => watch (t'.locSigSub l A hd tl)
  | newchan A' => newchan A'
  | chan κ => chan κ
  | select t1 t2 => select (t1.locSigSub l A hd tl) (t2.locSigSub l A hd tl)
  | appE t1 t2 => appE (t1.locSigSub l A hd tl) (t2.locSigSub l A hd tl)
  | appA t1 t2 => appA (t1.locSigSub l A hd tl) (t2.locSigSub l A hd tl)
  | head t' => head (t'.locSigSub l A hd tl)
  | tail t' => tail (t'.locSigSub l A hd tl)
  | sig A' t1 t2 => sig A' (t1.locSigSub l A hd tl) (t2.locSigSub l A hd tl)
  | cons A' t' => cons A' (t'.locSigSub l A hd tl)
  | recur B t1 t2 => recur B (t1.locSigSub l A hd tl) (t2.locSigSub l A hd tl)
  | var x => var x
  | loc l' => if l' = l then sig A hd tl else loc l'
  | fix u => fix (u.locSigSub l A hd tl)

@[simp] lemma Term.locSigSub_loc {l' l A hd tl} :
    (Term.loc l').locSigSub l A hd tl = if l' = l then Term.sig A hd tl else Term.loc l' := rfl

@[simp] lemma Term.locSigSub_tail_loc {l' l A hd tl} :
    (Term.tail (Term.loc l')).locSigSub l A hd tl
      = if l' = l then tl else Term.tail (Term.loc l') := rfl

-- Unfolding equation for `locSigSub` on a `tail`: it peels a `tail (loc l')`
-- specially and otherwise recurses under the `tail`.
lemma Term.locSigSub_tail {t' l A hd tl} :
    (Term.tail t').locSigSub l A hd tl =
      match t' with
      | Term.loc l' => if l' = l then tl else Term.tail (Term.loc l')
      | _ => Term.tail (t'.locSigSub l A hd tl) := by
  cases t' <;> rfl

lemma HasType.locSigSub :
    Γ ⊢[Δ, ⟪ ⟨ l , A ⟩  :: H , N ⟫] t ∷ B →
    ⊢[Δ, ⟪ H , N' ⟫] hd ∷ A →
    ⊢[Δ, ⟪ H , N' ⟫] tl ∷ ◯ (Typ.sig A) →
    Γ ⊢[Δ, ⟪ H , N' ⟫] t.locSigSub l A hd tl ∷ B := by
  generalize M : ⟪ ⟨ l , A ⟩  :: H , N ⟫ = H'
  intros Tt Thd Ttl
  induction Tt <;> try solve_by_elim
  case loc l' A' Γ' E =>
    subst M
    simp only [Term.locSigSub_loc]
    by_cases h : l' = l
    · simp only [if_pos h]
      rw [h] at E
      simp only [AList.lookup, List.dlookup_cons_eq, Option.mem_def] at E
      obtain rfl := Option.some.inj E
      exact (HasType.sig Thd Ttl).weaken_closed
    · simp only [if_neg h]
      apply HasType.loc
      simp [AList.lookup, h] at E ⊢
      exact E
  case tail t' C T' IH =>
    subst M
    cases t'
    case loc l' =>
      simp only [Term.locSigSub_tail_loc]
      cases T' with | loc E =>
      by_cases h : l' = l
      · simp only [if_pos h]
        rw [h] at E
        simp only [AList.lookup, List.dlookup_cons_eq, Option.mem_def] at E
        obtain rfl := Option.some.inj E
        exact Ttl.weaken_closed
      · simp only [if_neg h]
        apply HasType.tail; apply HasType.loc
        simp [AList.lookup, h] at E ⊢
        exact E
    all_goals (simp only [Term.locSigSub]; exact HasType.tail (by assumption))
  case case W1 W2 T1 T2 T3 IH1 IH2 IH3 =>
    subst M; simp only [Term.locSigSub]
    exact HasType.case ‹_› ‹_› IH1 IH2 IH3
  case recur W1 W2 T1 T2 IH1 IH2 =>
    subst M; simp only [Term.locSigSub]
    exact HasType.recur ‹_› ‹_› IH1 IH2

def Term.heapSub (t : Term) (η : Heap) : Term  :=
  match η with
  | ⟨ [], _ ⟩ => t
  | ⟨ ⟨ l, ⟨ A , hd , a , tl⟩ ⟩ :: η', N ⟩
    => (t.locSigSub l A hd tl).heapSub ⟪ η', List.cons_NodupKeys N ⟫


lemma HasType.heapSub :
    ⊢[Δ, η.type] t ∷ A →
    ⊢[Δ] η ∷now →
    ⊢[Δ] t.heapSub η ∷ A := by
  intros T H
  induction H generalizing t A
  case nil =>
    have htype : (∅ : Heap).type = ∅ := by simp [Heap.type]; rfl
    have hheap : t.heapSub (∅ : Heap) = t := by
      have h : (∅ : Heap) = ⟨[], by simp [List.NodupKeys]⟩ := AList.ext (by simp)
      simp only [h, Term.heapSub]
    rw [htype] at T; rw [hheap]; exact T
  case cons η M hd_v A_tp tl_v l a N H_sub hd_T tl_T IH =>
    simp only [Term.heapSub]
    have heq : (⟨η, List.cons_NodupKeys N⟩ : Heap) = ⟨η, M⟩ := AList.ext rfl
    rw [heq]
    apply IH
    exact HasType.locSigSub T hd_T tl_T

----------------------------------------------------------
-- Heap substitution turns a machine value into a value --
----------------------------------------------------------

-- `IsGValue` ('general' value) is the common closure of the machine
-- values `IsMValue` and the values `IsValue`
open Term in
inductive IsGValue : Term → Prop
| unit : IsGValue .unit
| loc : IsGValue (loc l)
| chan : IsGValue (chan κ)
| lam : IsGValue (lam t)
| in1 : IsGValue t → IsGValue (in1 t)
| in2 : IsGValue t → IsGValue (in2 t)
| pair : IsGValue s → IsGValue t → IsGValue (pair s t)
| wait : IsGValue (wait (chan κ))
| appE : IsGValue s → IsGValue t → IsGValue (appE s t)
| delay : IsGValue (delay t)
| never : IsGValue never
| tailLoc : IsGValue (tail (loc l))
| select : IsGValue s → IsGValue t → IsGValue (select s t)
| cons : IsGValue t → IsGValue (cons A t)
| watch : IsGValue t → IsGValue (watch t)
| sig : IsGValue v → IsGValue w → IsGValue (sig A v w)

-- Every machine value is a general value.
lemma IsMValue.gvalue : IsMValue t → IsGValue t := by
  intro h; induction h with
  | watch => exact IsGValue.watch IsGValue.loc
  | _ => constructor <;> assumption

-- Substituting the stored signal at `l` for a general value preserves general
-- values: a `loc l` becomes the value signal, and `tail (loc l)` becomes the
-- (general-value) stored tail.
lemma IsGValue.locSigSub (hhd : IsGValue hd) (htl : IsGValue tl) :
    IsGValue t → IsGValue (t.locSigSub l A hd tl) := by
  intro ht
  induction ht with
  | loc =>
      simp only [Term.locSigSub_loc]
      split
      · exact IsGValue.sig hhd htl
      · exact IsGValue.loc
  | tailLoc =>
      simp only [Term.locSigSub_tail_loc]
      split
      · exact htl
      · exact IsGValue.tailLoc
  | _ => simp only [Term.locSigSub]; constructor <;> assumption

-- A general value that type-checks against the empty heap type contains
-- no unresolved locations, hence is a real value.
lemma IsGValue.isValue_emptyH : IsGValue t → ⊢[Δ] t ∷ A → IsValue t := by
  intro hg hT
  induction hg generalizing A with
  | loc => cases hT with | loc mem => simp [AList.lookup] at mem
  | tailLoc => cases hT with | tail hT' => cases hT' with | loc mem => simp [AList.lookup] at mem
  | unit => exact IsValue.unit
  | chan => exact IsValue.chan
  | lam => exact IsValue.lam
  | delay => exact IsValue.delay
  | never => exact IsValue.never
  | in1 _ ih => cases hT; exact IsValue.in1 (ih (by assumption))
  | in2 _ ih => cases hT; exact IsValue.in2 (ih (by assumption))
  | pair _ _ ih1 ih2 => cases hT; exact IsValue.pair (ih1 (by assumption)) (ih2 (by assumption))
  | wait => exact IsValue.wait
  | appE _ _ ih1 ih2 => cases hT; exact IsValue.appE (ih1 (by assumption)) (ih2 (by assumption))
  | select _ _ ih1 ih2 => cases hT; exact IsValue.select (ih1 (by assumption)) (ih2 (by assumption))
  | cons _ ih => cases hT; exact IsValue.cons (ih (by assumption))
  | watch _ ih => cases hT; exact IsValue.watch (ih (by assumption))
  | sig _ _ ih1 ih2 => cases hT; exact IsValue.sig (ih1 (by assumption)) (ih2 (by assumption))

-- Heap substitution turns a (general) value into a real value.  This is the
-- value-level counterpart of `HasType.heapSub`: it justifies that `Reacts`
-- produces a real `Val`.
lemma IsValue.heapSub :
    IsGValue t → ⊢[Δ, η.type] t ∷ A → ⊢[Δ] η ∷now → IsValue (t.heapSub η) := by
  intro hg T H
  induction H generalizing t A
  case nil =>
    have hheap : t.heapSub (∅ : Heap) = t := by
      have h : (∅ : Heap) = ⟨[], by simp [List.NodupKeys]⟩ := AList.ext (by simp)
      simp only [h, Term.heapSub]
    have htype : (∅ : Heap).type = ∅ := by simp [Heap.type]; rfl
    rw [hheap]; rw [htype] at T
    exact hg.isValue_emptyH T
  case cons η M A l hd a tl N H_sub hd_T tl_T IH =>
    simp only [Term.heapSub]
    have heq : (⟨η, List.cons_NodupKeys N⟩ : Heap) = ⟨η, M⟩ := AList.ext rfl
    rw [heq]
    apply IH
    · exact IsGValue.locSigSub hd.property.gvalue tl.property.gvalue hg
    · exact HasType.locSigSub T hd_T tl_T
