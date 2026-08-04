import Rizzo.LogicalRelation.Core

open Term
open MVal
open Typ
open List

------------------------------------------------
-- Per-connective congruence                   --
------------------------------------------------

/-! Transport a `VRel`/`TRel` membership across a change of type and
environment that agrees component-wise.  The locality lemmas (`env_eq`,
`shift_insert`, `internalize`) share these once the per-case type
equalities are in hand. -/

lemma TRel.congr_iff {A A' ρ ρ' ε t} :
    (∀ (ε' : Env) (w : MVal), w ∈ V⟦A⟧ρ#ε' ↔ w ∈ V⟦A'⟧ρ'#ε') →
    (t ∈ T⟦A⟧ρ#ε ↔ t ∈ T⟦A'⟧ρ'#ε) := by
  intro h
  simp only [TRel]
  exact ⟨fun ⟨w, εw, R, V⟩ => ⟨w, εw, R, (h εw w).mp V⟩,
         fun ⟨w, εw, R, V⟩ => ⟨w, εw, R, (h εw w).mpr V⟩⟩

lemma VRel.prod_congr {A1 A2 A1' A2' ρ ρ' ε v} :
    (∀ (w : MVal), w ∈ V⟦A1⟧ρ#ε ↔ w ∈ V⟦A1'⟧ρ'#ε) →
    (∀ (w : MVal), w ∈ V⟦A2⟧ρ#ε ↔ w ∈ V⟦A2'⟧ρ'#ε) →
    (v ∈ V⟦A1 ⨂ A2⟧ρ#ε ↔ v ∈ V⟦A1' ⨂ A2'⟧ρ'#ε) := by
  intro h1 h2
  simp only [_root_.VRel]
  exact ⟨fun ⟨v1, v2, e, V1, V2⟩ => ⟨v1, v2, e, (h1 v1).mp V1, (h2 v2).mp V2⟩,
         fun ⟨v1, v2, e, V1, V2⟩ => ⟨v1, v2, e, (h1 v1).mpr V1, (h2 v2).mpr V2⟩⟩

lemma VRel.sum_congr {A1 A2 A1' A2' ρ ρ' ε v} :
    (∀ (w : MVal), w ∈ V⟦A1⟧ρ#ε ↔ w ∈ V⟦A1'⟧ρ'#ε) →
    (∀ (w : MVal), w ∈ V⟦A2⟧ρ#ε ↔ w ∈ V⟦A2'⟧ρ'#ε) →
    (v ∈ V⟦.sum A1 A2⟧ρ#ε ↔ v ∈ V⟦.sum A1' A2'⟧ρ'#ε) := by
  intro h1 h2
  simp only [_root_.VRel]
  constructor
  · rintro (⟨v1, rfl, V⟩ | ⟨v2, rfl, V⟩)
    · exact Or.inl ⟨v1, rfl, (h1 v1).mp V⟩
    · exact Or.inr ⟨v2, rfl, (h2 v2).mp V⟩
  · rintro (⟨v1, rfl, V⟩ | ⟨v2, rfl, V⟩)
    · exact Or.inl ⟨v1, rfl, (h1 v1).mpr V⟩
    · exact Or.inr ⟨v2, rfl, (h2 v2).mpr V⟩

lemma VRel.arr_congr {A1 A2 A1' A2'} {ρ ρ' : LRelSubs} {ε v} :
    (A1 ⟶ A2).substAll ρ.types = (A1' ⟶ A2').substAll ρ'.types →
    (∀ (ε' : Env) (w : MVal), w ∈ V⟦A1⟧ρ#ε' ↔ w ∈ V⟦A1'⟧ρ'#ε') →
    (∀ (ε' : Env) (w : MVal), w ∈ V⟦A2⟧ρ#ε' ↔ w ∈ V⟦A2'⟧ρ'#ε') →
    (v ∈ V⟦A1 ⟶ A2⟧ρ#ε ↔ v ∈ V⟦A1' ⟶ A2'⟧ρ'#ε) := by
  intro htyp hdom hcod
  have hcodT : ∀ (ε' : Env) (u : Term), u ∈ T⟦A2⟧ρ#ε' ↔ u ∈ T⟦A2'⟧ρ'#ε' :=
    fun _ _ => TRel.congr_iff hcod
  simp only [_root_.VRel, htyp]
  constructor
  · rintro ⟨T, t, rfl, P⟩
    exact ⟨T, t, rfl, fun ε' S v1 V1 => (hcodT ε' _).mp (P ε' S v1 ((hdom ε' v1).mpr V1))⟩
  · rintro ⟨T, t, rfl, P⟩
    exact ⟨T, t, rfl, fun ε' S v1 V1 => (hcodT ε' _).mpr (P ε' S v1 ((hdom ε' v1).mp V1))⟩

lemma VRel.sig_congr {B B' : Typ} {ρ ρ' : LRelSubs} {ε v} :
    B.substAll ρ.types = B'.substAll ρ'.types →
    (∀ (w : MVal), w ∈ V⟦B⟧ρ#ε ↔ w ∈ V⟦B'⟧ρ'#ε) →
    (v ∈ V⟦.sig B⟧ρ#ε ↔ v ∈ V⟦.sig B'⟧ρ'#ε) := by
  intro htyp h
  simp only [_root_.VRel, htyp]
  constructor
  · rintro ⟨l, rfl, sg, L, T, hh⟩
    exact ⟨l, rfl, sg, L, T, (h sg.head).mp hh⟩
  · rintro ⟨l, rfl, sg, L, T, hh⟩
    exact ⟨l, rfl, sg, L, T, (h sg.head).mpr hh⟩

------------------------------------------------
-- Locality in the semantic environment       --
------------------------------------------------

/-- The relation `V⟦A⟧ρ` only depends on the first `k` entries of `ρ`
when `A.Wf k`. -/
lemma VRel.env_eq : ∀ {A : Typ} {k} {ρ ρ' : LRelSubs} {ε v},
    A.Wf k → (∀ j, j < k → ρ[j]? = ρ'[j]?) →
    (v ∈ V⟦A⟧ρ#ε ↔ v ∈ V⟦A⟧ρ'#ε) := by
  intro A
  induction A with
  | unit => intro k ρ ρ' ε v _ _; simp [VRel]
  | prod A1 A2 ih1 ih2 =>
      intro k ρ ρ' ε v W h
      cases W with | prod W1 W2 =>
      exact VRel.prod_congr (fun _ => ih1 W1 h) (fun _ => ih2 W2 h)
  | sum A1 A2 ih1 ih2 =>
      intro k ρ ρ' ε v W h
      cases W with | sum W1 W2 =>
      exact VRel.sum_congr (fun _ => ih1 W1 h) (fun _ => ih2 W2 h)
  | arr A1 A2 ih1 ih2 =>
      intro k ρ ρ' ε v W h
      cases W with | arr W1 W2 =>
      exact VRel.arr_congr
        (Typ.substAll_eq (Typ.Wf.arr W1 W2) (LRelSubs.types_getElem?_congr h))
        (fun _ _ => ih1 (W1.mono (Nat.zero_le k)) h) (fun _ _ => ih2 W2 h)
  | delayA B _ =>
      intro k ρ ρ' ε v W h
      cases W with | delayA W' =>
      simp only [VRel, Typ.substAll_closed W']
  | delayE B _ =>
      intro k ρ ρ' ε v W h
      cases W with | delayE W' =>
      simp only [VRel, Typ.substAll_closed W']
  | chan B ih =>
      intro k ρ ρ' ε v W h
      cases W with | chan W' =>
      simp only [VRel, Typ.substAll_closed W']
  | sig B ih =>
      intro k ρ ρ' ε v W h
      cases W with | sig W' =>
      exact VRel.sig_congr (Typ.substAll_eq W' (LRelSubs.types_getElem?_congr h))
        (fun _ => ih W' h)
  | var i =>
      intro k ρ ρ' ε v W h
      cases W with | var hi =>
      vrel
      rw [h i hi]
  | mu B ih =>
      intro k ρ ρ' ε v W h
      cases W with | mu W' =>
      have htypes := LRelSubs.types_getElem?_congr h
      have elabel : B.substAll (Typ.var 0 :: ρ.types.map (Typ.shift 0))
          = B.substAll (Typ.var 0 :: ρ'.types.map (Typ.shift 0)) := by
        apply Typ.substAll_eq W'
        intro j hj
        cases j with
        | zero => rfl
        | succ m =>
            simp only [List.getElem?_cons_succ, List.getElem?_map, htypes m (by omega)]
      have emu : (μ B).substAll ρ.types = (μ B).substAll ρ'.types :=
        Typ.substAll_eq (Typ.Wf.mu W') htypes
      have hq : LRel.lfp (VRel.muOper B ρ) = LRel.lfp (VRel.muOper B ρ') := by
        apply LRel.lfp.congr_oper_iff
        intro X ε'' w
        simp only [VRel.muOper]
        have hent : ∀ j, j < k + 1 →
            ((⟨(μ B).substAll ρ.types, X⟩ : LRelOf) :: ρ)[j]?
              = ((⟨(μ B).substAll ρ'.types, X⟩ : LRelOf) :: ρ')[j]? := by
          intro j hj
          cases j with
          | zero => simp only [List.getElem?_cons_zero, emu]
          | succ m => simp only [List.getElem?_cons_succ]; exact h m (by omega)
        constructor
        · rintro ⟨v', rfl, V⟩
          exact ⟨v', by rw [elabel], (ih W' hent).mp V⟩
        · rintro ⟨v', rfl, V⟩
          exact ⟨v', by rw [elabel], (ih W' hent).mpr V⟩
      show v ∈ V⟦μ B⟧ρ#ε ↔ v ∈ V⟦μ B⟧ρ'#ε
      rw [VRel.mu_def, VRel.mu_def, hq]

/-- A relation at a closed type ignores the semantic environment. -/
lemma VRel.type_closed : A.Closed → v ∈ V⟦A⟧ρ # ε → v ∈ V⟦A⟧ρ' # ε :=
  fun W V => (VRel.env_eq W (fun j hj => absurd hj (by omega))).mp V

lemma TRel.type_closed : A.Closed → t ∈ T⟦A⟧ρ # ε → t ∈ T⟦A⟧ρ' # ε := by
  intro WF T
  obtain ⟨v, ε', R, V⟩ := T.elim
  exact TRel.intro R (V.type_closed WF)

------------------------------------------------
-- Monotonicity in the environment entries     --
------------------------------------------------

/-- Monotonicity in the environment entries — *the* positivity lemma.
Under the `Wf` discipline arrow domains are closed, so every variable
occurrence is covariant and growing the entries grows the relation.
This is what makes the µ-body operators monotone (`VRel.mu_unfold`). -/
lemma VRel.mono_env : ∀ {A : Typ} {ρ ρ' ε v},
    LRelSubs.Le ρ ρ' → A.Wf ρ.length →
    v ∈ V⟦A⟧ρ#ε → v ∈ V⟦A⟧ρ'#ε := by
  intro A
  induction A with
  | unit => intro ρ ρ' ε v _ _ V; simpa [VRel] using V
  | prod A1 A2 ih1 ih2 =>
      intro ρ ρ' ε v hρ W V
      cases W with | prod W1 W2 =>
      vrel at V ⊢
      obtain ⟨v1, v2, rfl, V1, V2⟩ := V
      exact ⟨v1, v2, rfl, ih1 hρ W1 V1, ih2 hρ W2 V2⟩
  | sum A1 A2 ih1 ih2 =>
      intro ρ ρ' ε v hρ W V
      cases W with | sum W1 W2 =>
      vrel at V ⊢
      rcases V with ⟨v1, rfl, V⟩ | ⟨v2, rfl, V⟩
      · exact Or.inl ⟨v1, rfl, ih1 hρ W1 V⟩
      · exact Or.inr ⟨v2, rfl, ih2 hρ W2 V⟩
  | arr A1 A2 ih1 ih2 =>
      intro ρ ρ' ε v hρ W V
      cases W with | arr W1 W2 =>
      simp only [VRel, hρ.1] at V ⊢
      obtain ⟨T, t, rfl, P⟩ := V
      refine ⟨T, t, rfl, ?_⟩
      intro ε'' S v1 V1
      -- the domain is closed, so its interpretation ignores the entries
      have V1' : v1 ∈ V⟦A1⟧ρ#ε'' :=
        (VRel.env_eq (k := 0) W1 (fun j hj => absurd hj (by omega))).mpr V1
      have hP := P ε'' S v1 V1'
      simp only [TRel] at hP ⊢
      obtain ⟨w, εw, R, Vw⟩ := hP
      exact ⟨w, εw, R, ih2 hρ W2 Vw⟩
  | delayA B ih =>
      intro ρ ρ' ε v hρ W V; simpa only [VRel, hρ.1] using V
  | delayE B ih =>
      intro ρ ρ' ε v hρ W V; simpa only [VRel, hρ.1] using V
  | chan B ih =>
      intro ρ ρ' ε v hρ W V; simpa only [VRel, hρ.1] using V
  | sig B ih =>
      intro ρ ρ' ε v hρ W V
      cases W with | sig W' =>
      simp only [VRel, hρ.1] at V ⊢
      obtain ⟨l, rfl, s, L, E, V⟩ := V
      exact ⟨l, rfl, s, L, E, ih hρ W' V⟩
  | var i =>
      intro ρ ρ' ε v hρ W V
      cases W with | var hi =>
      vrel at V ⊢
      obtain ⟨s, hs, T, R⟩ := V
      have hi' : i < ρ'.length := by rw [← hρ.length]; exact hi
      obtain ⟨s', hs'⟩ : ∃ s', ρ'[i]? = some s' :=
        ⟨ρ'[i], List.getElem?_eq_getElem hi'⟩
      have htype : s.type = s'.type := by
        have h1 : ρ.types[i]? = some s.type := by
          simp [LRelSubs.types, List.getElem?_map, hs]
        have h2 : ρ'.types[i]? = some s'.type := by
          simp [LRelSubs.types, List.getElem?_map, hs']
        rw [hρ.1] at h1
        rw [h1] at h2
        exact Option.some.inj h2
      exact ⟨s', hs', htype ▸ T, hρ.2 i s s' hs hs' _ _ R⟩
  | mu B ih =>
      intro ρ ρ' ε v hρ W V
      cases W with | mu W' =>
      have elabel : B.substAll (Typ.var 0 :: ρ.types.map (Typ.shift 0))
          = B.substAll (Typ.var 0 :: ρ'.types.map (Typ.shift 0)) := by
        rw [hρ.1]
      have emu : (μ B).substAll ρ.types = (μ B).substAll ρ'.types := by
        rw [hρ.1]
      rw [VRel.mu_def] at V ⊢
      refine LRel.lfp.mono_oper ?_ ε v V
      intro X ε'' w hw
      simp only [VRel.muOper] at hw ⊢
      obtain ⟨v', rfl, hv'⟩ := hw
      refine ⟨v', by rw [elabel], ?_⟩
      have hle : LRelSubs.Le (⟨(μ B).substAll ρ.types, X⟩ :: ρ)
          (⟨(μ B).substAll ρ'.types, X⟩ :: ρ') :=
        hρ.cons emu (fun ε₀ u h => h)
      exact ih hle (by simpa using W') hv'

/-- The µ-body operator is monotone — positivity, specialised to the
head entry. -/
lemma VRel.muOper_mono {B : Typ} {ρ : LRelSubs} :
    B.Wf (ρ.length + 1) → LRel.Mono (VRel.muOper B ρ) := by
  intro W X Y hXY ε v hv
  simp only [VRel.muOper] at hv ⊢
  obtain ⟨v', rfl, hv'⟩ := hv
  refine ⟨v', rfl, ?_⟩
  have hle : LRelSubs.Le (⟨(μ B).substAll ρ.types, X⟩ :: ρ)
      (⟨(μ B).substAll ρ.types, Y⟩ :: ρ) :=
    (LRelSubs.Le.refl ρ).cons rfl (fun ε₀ u h => hXY ε₀ u h)
  exact VRel.mono_env hle (by simpa using W) hv'

------------------------------------------------
-- Monotonicity in the runtime environment    --
------------------------------------------------

/-- Monotonicity in the runtime environment, `Wf`-free (it is applied
at administrative types with open arrow domains).  The µ-case is where
the Kripke-constrained `LRel.lfp` pays off: the fixed point is monotone
with no conditions (`LRel.lfp.kripke`). -/
lemma VRel.kripke' : ∀ {A ρ ε ε' v},
    (∀ s ∈ ρ, ∀ v, s.rel ε v → s.rel ε' v) →
    v ∈ V⟦A⟧ρ#ε → ε.le ε' → v ∈ V⟦A⟧ρ#ε' := by
  intro A
  induction A with
  | unit => intro ρ ε ε' v C V S; simpa [VRel] using V
  | prod A1 A2 ih1 ih2 =>
      intro ρ ε ε' v C V S
      vrel at V ⊢
      obtain ⟨v1, v2, rfl, V1, V2⟩ := V
      exact ⟨v1, v2, rfl, ih1 C V1 S, ih2 C V2 S⟩
  | sum A1 A2 ih1 ih2 =>
      intro ρ ε ε' v C V S
      vrel at V ⊢
      rcases V with ⟨v1, rfl, V⟩ | ⟨v2, rfl, V⟩
      · exact Or.inl ⟨v1, rfl, ih1 C V S⟩
      · exact Or.inr ⟨v2, rfl, ih2 C V S⟩
  | arr A1 A2 ih1 ih2 =>
      intro ρ ε ε' v C V S
      vrel at V ⊢
      obtain ⟨T, t, rfl, P⟩ := V
      exact ⟨T.le' S, t, rfl, fun ε'' S' v1 V1 => P ε'' (S.trans S') v1 V1⟩
  | delayA B ih => intro ρ ε ε' v C V S; vrel at V ⊢; exact V.le' S
  | delayE B ih => intro ρ ε ε' v C V S; vrel at V ⊢; exact V.le' S
  | chan B ih => intro ρ ε ε' v C V S; vrel at V ⊢; exact V.le' S
  | sig B ih =>
      intro ρ ε ε' v C V S
      vrel at V ⊢
      obtain ⟨l, rfl, s, L, E, V⟩ := V
      exact ⟨l, rfl, s, AList.le.lookup S.store.now L, E, ih C V S⟩
  | var i =>
      intro ρ ε ε' v C V S
      vrel at V ⊢
      obtain ⟨s, hs, T, R⟩ := V
      exact ⟨s, hs, T.le' S, C s (List.mem_of_getElem? hs) _ R⟩
  | mu B ih =>
      intro ρ ε ε' v C V S
      rw [VRel.mu_def] at V ⊢
      exact LRel.lfp.kripke ε ε' v S V

lemma VRel.kripke : ρ.Kripke → v ∈ V⟦A⟧ρ # ε → ε.le ε' → v ∈ V⟦A⟧ρ # ε' :=
  fun W V S => VRel.kripke' (fun s hs v R => W s hs _ _ v S R) V S

/-- The unfolding of the µ-relation is Kripke-monotone over a
well-formed environment (the side condition of `LRel.lfp.unfold`). -/
lemma VRel.muOper_kripke {B} {ρ : LRelSubs} (WS : ρ.Kripke) {X : LRel} :
    X.Kripke → (VRel.muOper B ρ X).Kripke := by
  intro hX ε₀ ε₁ w S hw
  simp only [VRel.muOper] at hw ⊢
  obtain ⟨v', rfl, hv'⟩ := hw
  refine ⟨v', rfl, ?_⟩
  refine VRel.kripke' ?_ hv' S
  intro s hs u R
  headTail hs
  · exact hX _ _ _ S R
  · exact WS s hs _ _ u S R

/-- The fixed-point equation for µ (Knaster–Tarski).  Monotonicity of the
body operator is positivity (`W`); the Kripke side condition needs a
well-formed environment. -/
lemma VRel.mu_unfold {B : Typ} {ρ : LRelSubs} {ε v} :
    B.Wf (ρ.length + 1) → ρ.Kripke →
    (v ∈ V⟦μ B⟧ρ#ε ↔ ∃ (v' : MVal),
      v = MVal.cons (B.substAll (Typ.var 0 :: ρ.types.map (Typ.shift 0))) v' ∧
      v' ∈ V⟦B⟧(LRelOf.mu B ρ :: ρ)#ε) := by
  intro W WS
  rw [VRel.mu_def,
      LRel.lfp.unfold (VRel.muOper_mono W) (VRel.muOper_kripke WS LRel.lfp.kripke)]
  simp only [VRel.muOper, LRelOf.mu, VRel.mu_def]

------------------------
-- Lemma 5.8 (part 1) --
------------------------

lemma VRel.le' : v ∈ V⟦A⟧ ε → ε.le ε' → v ∈ V⟦A⟧ ε' :=
  fun V S => VRel.kripke LRelSubs.Kripke.nil V S

------------------------
-- Lemma 5.8 (part 2) --
------------------------

lemma CRel.le' : γ ∈ C⟦Γ⟧ε → ε.le ε' → γ ∈ C⟦Γ⟧ε' := by
  intros G S
  induction G
  case nil => constructor
  case cons V G IH =>
    constructor
    . apply VRel.le' V S
    . apply IH ; assumption

lemma CRel.VRel {t} {γ : List Term} {Γ} {i : Nat} :
   γ ∈ C⟦Γ⟧ε → t ∈ γ[i]? → ∃ A : Typ, ∃  p , A ∈ Γ[i]? /\ ⟨ t, p ⟩ ∈ V⟦A⟧ε := by
  intros G L
  revert i
  induction G <;> intro i L
  case nil => simp at *
  case cons IH =>
    cases i
    case zero => simp at L;grind
    case succ => simp at *; apply IH L;

lemma CRel.VRel' {t} {γ : List Term} {Γ} {i : Nat}:
  γ ∈ C⟦Γ⟧ε → t ∈ γ[i]? → A ∈ Γ[i]? → ∃ p, ⟨ t, p ⟩ ∈ V⟦A⟧ε := by
  intros G L L'
  apply CRel.VRel G at L
  rcases L with ⟨ A, V, E, T ⟩
  rw [E] at L'
  cases L'
  constructor; assumption

lemma CRel.length : γ ∈ C⟦Γ⟧ε → γ.length = Γ.length := by
  intros G
  induction G <;> simp
  assumption

----------------------------------------
-- Typing from the logical relation   --
----------------------------------------

/-- Members of `V⟦A⟧ρ` are well-typed (at the substituted type). -/
lemma VRel.HasType_open : ∀ {A : Typ} {ρ : LRelSubs} {ε v},
    ρ.Closed → A.Wf ρ.length → v ∈ V⟦A⟧ρ # ε → ⊢{ε} v ∷ A.substAll ρ.types := by
  intro A
  induction A with
  | unit =>
      intro ρ ε v hρ W V
      vrel at V
      subst V
      exact .unit
  | prod A1 A2 ih1 ih2 =>
      intro ρ ε v hρ W V
      cases W with | prod W1 W2 =>
      vrel at V
      obtain ⟨v1, v2, rfl, V1, V2⟩ := V
      exact .pair (ih1 hρ W1 V1) (ih2 hρ W2 V2)
  | sum A1 A2 ih1 ih2 =>
      intro ρ ε v hρ W V
      cases W with | sum W1 W2 =>
      vrel at V
      rcases V with ⟨v1, rfl, V⟩ | ⟨v2, rfl, V⟩
      · exact .in1 (Typ.substAll_Wf_closed (by simpa using W2) hρ.types) (ih1 hρ W1 V)
      · exact .in2 (Typ.substAll_Wf_closed (by simpa using W1) hρ.types) (ih2 hρ W2 V)
  | arr A1 A2 ih1 ih2 =>
      intro ρ ε v hρ W V
      vrel at V
      exact V.1
  | delayA B ih =>
      intro ρ ε v hρ W V
      vrel at V
      simp only [Typ.substAll]
      exact V
  | delayE B ih =>
      intro ρ ε v hρ W V
      vrel at V
      simp only [Typ.substAll]
      exact V
  | chan B ih =>
      intro ρ ε v hρ W V
      vrel at V
      simp only [Typ.substAll]
      exact V
  | var i =>
      intro ρ ε v hρ W V
      cases W with | var hi =>
      vrel at V
      obtain ⟨s, hs, T, _⟩ := V
      have e : (Typ.var i).substAll ρ.types = s.type := by
        simp only [Typ.substAll, List.getD_eq_getElem?_getD, LRelSubs.types,
          List.getElem?_map, hs, Option.map_some, Option.getD_some]
      rw [e]; exact T
  | sig B ih =>
      intro ρ ε v hρ W V
      cases W with | sig W' =>
      vrel at V
      rcases V with ⟨l, rfl, s, L, E, V⟩
      simp only [Typ.substAll]
      constructor
      rw [Heap.type_lookup]
      simp
      exists s
  | mu B ih =>
      intro ρ ε v hρ W V
      cases W with | mu W' =>
      have hmuC : ((μ B).substAll ρ.types).Closed :=
        Typ.substAll_Wf_closed (by simpa using Typ.Wf.mu W') hρ.types
      rw [VRel.mu_def] at V
      refine LRel.lfp.le_prefixed
        (X := fun ε₀ (w : MVal) => ⊢{ε₀} w ∷ (μ B).substAll ρ.types) ?_ ?_ ε v V
      · intro ε₀ ε₁ w S hT
        exact hT.le' S
      · intro ε₀ w hw
        simp only [VRel.muOper] at hw
        obtain ⟨v', rfl, V'⟩ := hw
        have hρ' : LRelSubs.Closed
            (⟨(μ B).substAll ρ.types,
              fun ε₁ (w : MVal) => ⊢{ε₁} w ∷ (μ B).substAll ρ.types⟩ :: ρ) := by
          intro s hs
          headTail hs
          · exact hmuC
          · exact hρ s hs
        have T := ih hρ' (by simpa using W') V'
        have hcomm := Typ.substAll_subAt_comm (A := B) (k := 0) (pre := [])
          (L := ρ.types) (X := (μ B).substAll ρ.types)
          (by simpa using W') rfl (fun i h => absurd h (by omega)) hρ.types
        simp only [List.nil_append] at hcomm
        have hlab : μ (B.substAll (Typ.var 0 :: ρ.types)) = (μ B).substAll ρ.types := by
          simp only [Typ.substAll]
          rw [hρ.types_shift]
        show ⊢{ε₀} MVal.cons (B.substAll (Typ.var 0 :: ρ.types.map (Typ.shift 0))) v'
            ∷ (μ B).substAll ρ.types
        simp only [hρ.types_shift]
        rw [← hlab]
        refine HasType.cons ?_ ?_
        · rw [hlab]; exact hmuC
        · simp only [Typ.sub]
          rw [hlab, hcomm]
          simpa using T

lemma VRel.HasType : A.Closed → v ∈ V⟦A⟧ ε → ⊢{ε} v ∷ A := by
  intro W V
  have T := V.HasType_open (by simp) (by simpa using W)
  simpa using T

lemma CRel.SubsType : γ ∈ C⟦Γ⟧ε → (∀ A ∈ Γ, A.Closed) → ⊢C{ε} γ ∷ Γ := by
  intros G hΓ
  induction G
  case nil => constructor
  case cons V G IH =>
    constructor
    . apply VRel.HasType (hΓ _ (by simp)) V
    . apply IH
      intro A hA
      exact hΓ _ (by simp [hA])

lemma HasType.subs_CRel : γ ∈ C⟦Γ⟧ε → (∀ A ∈ Γ, A.Closed) →
  Γ ⊢{ε} t ∷ A → ⊢{ε} t.subs γ 0 ∷  A := by
  intros G hΓ T
  apply CRel.SubsType G at hΓ
  apply HasType.subs_top <;> assumption

-------------------------------
-- The heap logical relation --
-- Fig. 10                   --
-------------------------------

inductive HRel : Env → Heap → Prop where
| nil : HRel ε ∅
| cons :
  HRel ε ⟨ η , M ⟩ →
  hd ∈ V⟦A⟧ε →
  HRel ε ⟨ ⟨ l, ⟨ A , hd , cl , tl⟩ ⟩ :: η , N ⟩

lemma HRel.lookup_VRel : HRel ε η → s ∈ AList.lookup l η → s.head ∈ V⟦s.type⟧ε := by
  intros H L'
  simp[AList.lookup] at L'
  have L : s ∈ List.dlookup l η.entries := by apply L';
  rewrite [List.mem_dlookup_iff η.nodupKeys] at L
  clear L'
  induction H
  case nil => contradiction
  case cons η M A hd l θ tl N H V IH =>
    cases L
    case head => apply V
    case tail L =>
      apply IH; apply L

------------------------
-- Lemma 5.8 (part 3) --
------------------------

lemma HRel.le : HRel ε η → ε.le ε' → HRel ε' η := by
  intros H S
  revert ε'
  induction H <;> intros ε' S
  case nil => constructor
  case cons V IH =>
    constructor
    . apply IH; assumption
    . apply V.le' S
