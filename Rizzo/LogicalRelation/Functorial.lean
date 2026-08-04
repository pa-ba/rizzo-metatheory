import Rizzo.LogicalRelation.Fundamental

open Term
open MVal
open Typ
open List

/-
This file proves the semantic counterpart of the `recur` typing rule.
-/

------------------------------------------------------------------
-- Semantic environment entries (cap, pairE)                     --
------------------------------------------------------------------

/-- The canonical entry interpreting an open type `X` over its own
environment.  `LRelOf.mu B ρ` is the `X := μ B` instance
(definitionally). -/
def LRelOf.cap (X : Typ) (ρ : LRelSubs) : LRelOf :=
  ⟨X.substAll ρ.types, VRel X ρ⟩

@[simp] lemma LRelOf.cap_type {X ρ} :
    (LRelOf.cap X ρ).type = X.substAll ρ.types := rfl

@[simp] lemma LRelOf.cap_rel {X ρ ε} {w : MVal} :
    (LRelOf.cap X ρ).rel ε w ↔ VRel X ρ ε w := Iff.rfl

lemma LRelOf.mu_eq_cap {B ρ} :
    LRelOf.mu B ρ = LRelOf.cap (μ B) ρ := rfl

/-- Conjunctive pair entry: relates `pair a b` iff the components are
in the component entries.  This is the fmap₁-step's output entry in the
µ-case of the fmap lemma. -/
def LRelOf.pairE (e₁ e₂ : LRelOf) : LRelOf :=
  ⟨e₁.type ⨂ e₂.type,
   fun ε v => ∃ a b, v = MVal.pair a b ∧ e₁.rel ε a ∧ e₂.rel ε b⟩

@[simp] lemma LRelOf.pairE_type {e₁ e₂} :
    (LRelOf.pairE e₁ e₂).type = e₁.type ⨂ e₂.type := rfl

@[simp] lemma LRelOf.pairE_rel {e₁ e₂ ε} {v : MVal} :
    (LRelOf.pairE e₁ e₂).rel ε v ↔
      ∃ a b, v = MVal.pair a b ∧ e₁.rel ε a ∧ e₂.rel ε b := Iff.rfl

------------------------------------------------------------------
-- Semantic rebuild evidence                                     --
------------------------------------------------------------------

/-- Entry hygiene: the type is closed, the relation is Kripke-monotone,
and members are typed at the entry's type. -/
structure LRelOf.Good (s : LRelOf) : Prop where
  closed : s.type.Closed
  wf : LRelOf.Kripke s
  hasType : ∀ {ε : Env} {w : MVal}, s.rel ε w → ⊢{ε} w.val ∷ s.type

/-- One fmap-rebuild step at the closed type `T`: the value `w` runs
through the body of an identity `fmap` instance at `T`, applied with
arbitrary *dead* functions (typed, substitution-invariant).  This is the
step relation whose reflexive-transitive closure grounds the
descendant-closed Park predicates of the µ-cases. -/
def RebStep (T : Typ) (ε₀ : Env) (w : MVal) (ε₁ : Env) (w' : MVal) : Prop :=
  ∃ (Ss_t Cs_t : List Typ) (fns : List MVal) (body' : Term),
    Ss_t.length = Cs_t.length ∧
    fns.length = Cs_t.length ∧
    (∀ S ∈ Ss_t, S.Closed) ∧
    (∀ T' ∈ Cs_t, T'.Closed) ∧
    (∀ j (hjS : j < Ss_t.length) (hjC : j < Cs_t.length) (hjf : j < fns.length),
        ⊢{ε₀} (fns[j]'hjf).val ∷ Ss_t[j]'hjS ⟶ Cs_t[j]'hjC) ∧
    (∀ fn ∈ fns, ∀ (σs : Subs) (k : Nat), fn.val.subs σs k = fn.val) ∧
    Term.fmap T Cs_t = Term.nlam Cs_t.length (Term.lam body') ∧
    (body'.subs (w.val :: fns.reverse.map Subtype.val) 0, ε₀) ⇓ (w', ε₁)

/-- Finitely many rebuild steps, interleaved with runtime-environment
extensions (values persist across extensions, so descendant chains may
move forward in the environment order between steps). -/
inductive RebStar (T : Typ) : Env → MVal → Env → MVal → Prop
  | refl {ε : Env} {v : MVal} : RebStar T ε v ε v
  | tail {ε ε₁ ε₂ : Env} {v w u : MVal} :
      RebStar T ε v ε₁ w → RebStep T ε₁ w ε₂ u → RebStar T ε v ε₂ u
  | weak {ε ε₁ ε₂ : Env} {v w : MVal} :
      RebStar T ε v ε₁ w → ε₁.le ε₂ → RebStar T ε v ε₂ w

lemma RebStar.single {T ε ε₁} {v w : MVal}
    (h : RebStep T ε v ε₁ w) : RebStar T ε v ε₁ w :=
  RebStar.tail RebStar.refl h

lemma RebStar.trans {T ε ε₁ ε₂} {v w u : MVal}
    (h1 : RebStar T ε v ε₁ w) (h2 : RebStar T ε₁ w ε₂ u) : RebStar T ε v ε₂ u := by
  revert h1
  induction h2 with
  | refl => exact fun h1 => h1
  | tail _ hstep ih => exact fun h1 => RebStar.tail (ih h1) hstep
  | weak _ S ih => exact fun h1 => RebStar.weak (ih h1) S

/-- `s` rebuilds into `t`: every fmap-rebuild instance on an `s`-member
evaluates and lands in `t` (the types agree).  Frozen positions of the
mapped fmap lemma consume this clause. -/
def LRelOf.RebuildsInto (s t : LRelOf) : Prop :=
  s.type = t.type ∧
  ∀ {Ss_t Cs_t : List Typ} {fns : List MVal} {ε₀ : Env} {w : MVal} {body' : Term},
    Ss_t.length = Cs_t.length →
    fns.length = Cs_t.length →
    (∀ S ∈ Ss_t, S.Closed) →
    (∀ T' ∈ Cs_t, T'.Closed) →
    (∀ j (hjS : j < Ss_t.length) (hjC : j < Cs_t.length) (hjf : j < fns.length),
        ⊢{ε₀} (fns[j]'hjf).val ∷ Ss_t[j]'hjS ⟶ Cs_t[j]'hjC) →
    (∀ fn ∈ fns, ∀ (σs : Subs) (k : Nat), fn.val.subs σs k = fn.val) →
    s.rel ε₀ w →
    Term.fmap s.type Cs_t = Term.nlam Cs_t.length (Term.lam body') →
    ∃ (w' : MVal) (ε₁ : Env),
      (body'.subs (w.val :: fns.reverse.map Subtype.val) 0, ε₀) ⇓ (w', ε₁) ∧
      t.rel ε₁ w'

/-- Rebuild-stable: rebuilds into itself. -/
def LRelOf.Stable (s : LRelOf) : Prop := LRelOf.RebuildsInto s s

/-- Weakening in the source entry. -/
lemma LRelOf.RebuildsInto.mono_left {s₀ s : LRelOf} {t} :
    s₀.type = s.type → (∀ ε w, s₀.rel ε w → s.rel ε w) →
    LRelOf.RebuildsInto s t → LRelOf.RebuildsInto s₀ t := by
  intro hty hle h
  refine ⟨hty.trans h.1, ?_⟩
  intro Ss_t Cs_t fns ε₀ w body' h1 h2 h3 h4 h5 h6 hw hbody
  exact h.2 h1 h2 h3 h4 h5 h6 (hle _ _ hw) (by rwa [hty] at hbody)

/-- Cap entries over pointwise-Good environments are Good. -/
lemma LRelOf.Good.cap {Y : Typ} {σ : LRelSubs}
    (hY : Y.Wf σ.length) (hG : ∀ s ∈ σ, LRelOf.Good s) :
    LRelOf.Good (LRelOf.cap Y σ) where
  closed := Typ.substAll_Wf_closed (by simpa using hY) (fun C hC => by
    simp only [LRelSubs.types, List.mem_map] at hC
    obtain ⟨u, hu, rfl⟩ := hC
    exact (hG u hu).closed)
  wf := fun ε ε' v S R => by
    simp only [LRelOf.cap_rel] at R ⊢
    exact VRel.kripke (fun s hs => (hG s hs).wf) R S
  hasType := fun {ε w} R => by
    simp only [LRelOf.cap_rel] at R
    simp only [LRelOf.cap_type]
    exact VRel.HasType_open (fun s hs => (hG s hs).closed) hY R

/-- Conjunctive pair entries of Good entries are Good. -/
lemma LRelOf.Good.pairE {e₁ e₂}
    (h₁ : LRelOf.Good e₁) (h₂ : LRelOf.Good e₂) :
    LRelOf.Good (LRelOf.pairE e₁ e₂) where
  closed := Typ.Wf.prod h₁.closed h₂.closed
  wf := fun ε ε' v S R => by
    simp only [LRelOf.pairE_rel] at R ⊢
    obtain ⟨a, b, rfl, R₁, R₂⟩ := R
    exact ⟨a, b, rfl, h₁.wf ε ε' a S R₁, h₂.wf ε ε' b S R₂⟩
  hasType := fun {ε w} R => by
    simp only [LRelOf.pairE_rel] at R
    obtain ⟨a, b, rfl, R₁, R₂⟩ := R
    simp only [LRelOf.pairE_type]
    exact HasType.pair (h₁.hasType R₁) (h₂.hasType R₂)

/-- Stability composes over conjunctive pair entries: a pair value
rebuilds componentwise (the `fmap` product case), each component
through its own entry's stability. -/
lemma LRelOf.Stable.pairE {e₁ e₂} :
    LRelOf.Good e₁ → LRelOf.Good e₂ →
    LRelOf.Stable e₁ → LRelOf.Stable e₂ →
    LRelOf.Stable (LRelOf.pairE e₁ e₂) := by
  intro hG₁ hG₂ h₁ h₂
  refine ⟨rfl, ?_⟩
  intro Ss_t Cs_t fns ε₀ w body' hSClen hflen hScl hCcl hfnsT hfcl R hbody
  have hσs : ∀ g ∈ fns.reverse.map Subtype.val, ∀ (σs : Subs) (k : Nat), g.subs σs k = g := by
    intro g hg σs k
    simp only [List.mem_map, List.mem_reverse] at hg
    obtain ⟨fn, hfn, rfl⟩ := hg
    exact hfcl fn hfn σs k
  have comp_eval : ∀ {T : Typ} {bodyT : Term},
      Term.fmap T Cs_t = Term.nlam Cs_t.length (Term.lam bodyT) →
      ∀ {t : Term} {u : MVal} {εa εm : Env}, (t, εa) ⇓ (u, εm) →
      ∀ {u' : MVal} {εb : Env},
        (bodyT.subs (u.val :: fns.reverse.map Subtype.val) 0, εm) ⇓ (u', εb) →
      ((Term.apps (Term.fmap T Cs_t) (fns.map Subtype.val)).app t, εa) ⇓ (u', εb) := by
    intro T bodyT hbodyT t u εa εm Rt u' εb Rb
    rw [hbodyT, ← hflen]
    refine Eval.app (Eval.apps_nlam hfcl (Eval.value IsMValue.nlam_lam)) Rt ?_
    simp only [Term.sub]
    rw [Term.subs_subs_closed hσs]
    exact Rb
  simp only [LRelOf.pairE_rel] at R
  obtain ⟨a, b, rfl, R₁, R₂⟩ := R
  have hT₁F : e₁.type.Wf Cs_t.length := hG₁.closed.mono (Nat.zero_le _)
  have hT₂F : e₂.type.Wf Cs_t.length := hG₂.closed.mono (Nat.zero_le _)
  simp only [LRelOf.pairE_type] at hbody
  rw [Term.fmap] at hbody
  obtain rfl := Term.nlam_lam_inj hbody.symm
  simp only [Term.subs, Term.subs_apps, Term.fmap_subs hT₁F hCcl,
    Term.fmap_subs hT₂F hCcl, Term.fmap_fns_subs0 hflen]
  obtain ⟨body₁, hbody₁⟩ := Term.fmap_nlam e₁.type Cs_t
  obtain ⟨body₂, hbody₂⟩ := Term.fmap_nlam e₂.type Cs_t
  obtain ⟨a', ε₁, Ra', Rel₁⟩ := h₁.2 hSClen hflen hScl hCcl hfnsT hfcl R₁ hbody₁
  have hSub₁ : ε₀.le ε₁ := Ra'.incr
  obtain ⟨b', ε₂', Rb', Rel₂⟩ := h₂.2 hSClen hflen hScl hCcl
    (fun j hjS hjC hjf => (hfnsT j hjS hjC hjf).le' hSub₁) hfcl
    (hG₂.wf ε₀ ε₁ b hSub₁ R₂) hbody₂
  have hSub₂ : ε₁.le ε₂' := Rb'.incr
  refine ⟨MVal.pair a' b', ε₂', ?_, ?_⟩
  · exact Eval.pair
      (comp_eval hbody₁ (Eval.pr1 (Eval.value (MVal.pair a b).2)) Ra')
      (comp_eval hbody₂ (Eval.pr2 (Eval.value (MVal.pair a b).2)) Rb')
  · simp only [LRelOf.pairE_rel]
    exact ⟨a', b', rfl, hG₁.wf ε₁ ε₂' a' hSub₂ Rel₁, Rel₂⟩

-- The uniform typing bridge for the peeled `fmap` lemmas: the collapsed `fmap`
-- is typed by `HasType.fmap` at source `ρ.types`, and that type equals the
-- collapse of the open `funcsTo` goal type.
lemma VRel.fmap_eval_typing {F : Typ} {Cs : List Typ} {ρ : LRelSubs} {ε} :
    F.Wf ρ.length → Cs.length = ρ.length → (∀ C ∈ Cs, C.Wf ρ.length) →
    ρ.Closed →
    ⊢{ε} Term.fmap F (Cs.map (·.substAll ρ.types))
      ∷ (Typ.funcsTo ((List.range ρ.length).map Typ.var) Cs (F ⟶ F.substAll Cs)).substAll ρ.types := by
  intro hFWf hlen hCc hρcl
  have htlen : (LRelSubs.types ρ).length = ρ.length := by simp [LRelSubs.types]
  have hρcm : ∀ C ∈ Cs.map (·.substAll ρ.types), C.Closed := by
    intro C hC; simp only [List.mem_map] at hC; obtain ⟨C', hC', rfl⟩ := hC
    exact Typ.substAll_Wf_closed (by rw [htlen]; exact hCc C' hC') hρcl.types
  have hfmap := HasType.fmap (H := ε.now.type) (Δ := ε.chans) (Γ := [])
    (A := F) (Cs := Cs.map (·.substAll ρ.types)) (Ss := LRelSubs.types ρ)
    (by rw [List.length_map, hlen]; exact hFWf) (by simp only [List.length_map, htlen, hlen])
    (fun S hS => hρcl.types S hS) hρcm
  have htgt : (Typ.funcsTo ((List.range ρ.length).map Typ.var) Cs (F ⟶ F.substAll Cs)).substAll ρ.types
      = Typ.funcsTo (LRelSubs.types ρ) (Cs.map (·.substAll ρ.types))
          (F.substAll (LRelSubs.types ρ) ⟶ F.substAll (Cs.map (·.substAll ρ.types))) := by
    rw [Typ.funcsTo_substAll]
    have hrv : ((List.range ρ.length).map Typ.var).map (·.substAll ρ.types) = LRelSubs.types ρ := by
      conv_lhs => rw [show ρ.length = (LRelSubs.types ρ).length from htlen.symm]
      exact rangeVar_map_substAll _
    rw [hrv]
    congr 1
    simp only [Typ.substAll]
    rw [Typ.substAll_substAll (by rw [hlen]; exact hFWf)]
  rw [htgt]; exact hfmap

/-! Fold/unfold for the canonical µ-environment (compositionality at `Δ = ρt = []`). -/

-- A closed list is unaffected by parallel substitution.
lemma map_substAll_closed {Es : List Typ} (h : ∀ E ∈ Es, E.Closed) (Fs : List Typ) :
    Es.map (·.substAll Fs) = Es := by
  conv_rhs => rw [← List.map_id Es]
  apply List.map_congr_left
  intro E hE
  exact Typ.substAll_closed (h E hE) Fs

@[simp] lemma LRelOf.mu_type_nil {A} : (LRelOf.mu A ρ0).type = μ A := by
  simp [LRelOf.mu]

/-- Unfolding: the relation at an open type over the canonical
µ-environment coincides with the relation at the substituted type (the
`Δ = ρt = []` instance of compositionality). -/
lemma VRel.VRelMu_sub_iff :
    1 ⊢ A ∷type → 1 ⊢ B ∷type →
    (v ∈ V⟦B⟧ (LRelOf.mu A ρ0 :: ρ0) # ε ↔ v ∈ V⟦B.sub (μ A)⟧ ε) := by
  intro hA hB
  have h := VRel.internalize (C := B) (Y := μ A) (Δ := ρ0) (ρt := ρ0) (ε := ε) (v := v)
    (by simp) (by simp) (by simpa using Typ.Wf.mu hA) (by simpa using hB)
  rw [show ((List.range (ρ0 : LRelSubs).length).map Typ.var
        ++ Typ.shiftN (ρ0 : LRelSubs).length (μ A)
          :: (List.range' (ρ0 : LRelSubs).length (ρ0 : LRelSubs).length).map Typ.var)
        = [μ A] from by simp,
      Typ.substAll_singleton hB] at h
  exact h.symm

lemma VRel.VRelMu_sub :
    1 ⊢ A ∷type → 1 ⊢ B ∷type →
    v ∈ V⟦B⟧ (LRelOf.mu A ρ0 :: ρ0) # ε → v ∈ V⟦B.sub (μ A)⟧ ε :=
  fun hA hB => (VRel.VRelMu_sub_iff hA hB).mp

/-- Folding: a value in the relation at the unfolded type is in the
relation at the recursive type (compositionality + one fold step of the
fixed point). -/
lemma VRel.sub_mu : 1 ⊢ A ∷type → v ∈ V⟦A.sub (μ A)⟧ ε → cons A v ∈ V⟦μ A⟧ ε := by
  intro hA V
  have hin : v ∈ V⟦A⟧ (LRelOf.mu A ρ0 :: ρ0) # ε :=
    (VRel.VRelMu_sub_iff hA hA).mpr V
  have hlab : A.substAll (Typ.var 0 :: (LRelSubs.types ρ0).map (Typ.shift 0)) = A := by
    have := Typ.substAll_rangeVar (A := A) (n := 1)
    simpa [List.range_succ] using this
  show MVal.cons A v ∈ V⟦μ A⟧ ε
  rw [VRel.mu_unfold (by simpa using hA) LRelSubs.Kripke.nil]
  exact ⟨v, by rw [hlab], hin⟩

lemma VRel.isCons {B ρ} :
    v ∈ V⟦μ B⟧ρ#ε →
    ∃ w, v = MVal.cons (B.substAll (Typ.var 0 :: ρ.types.map (Typ.shift 0))) w := by
  intro V
  rw [VRel.mu_def] at V
  refine LRel.lfp.le_prefixed (X := fun _ (u : MVal) =>
      ∃ w, u = MVal.cons (B.substAll (Typ.var 0 :: ρ.types.map (Typ.shift 0))) w)
    ?_ ?_ ε v V
  · intro ε₀ ε₁ w S h
    exact h
  · intro ε₀ w hw
    simp only [VRel.muOper] at hw
    obtain ⟨w', rfl, _⟩ := hw
    exact ⟨w', rfl⟩

/-- A `recur` whose scrutinee evaluates to a related value of the
recursive type can be discharged at the evaluated value. -/
lemma TRel.recur_val {s : Term} {t} : (t, ε1)⇓(v, ε2) → v ∈ V⟦μ A⟧ε2 →
    s.recur B v ∈ T⟦B⟧ε2 → s.recur B t ∈ T⟦B⟧ε1 := by
  intro R1 Vv Vr
  obtain ⟨w, ε3, R2, Vw⟩ := Vr.elim
  cases R2
  case value IV =>
    exfalso
    cases IV
  case recur u _ _ _ R2 R3 R4 =>
    have R3' := Eval.value (ε:=ε2) (v.prop)
    apply R3.determ at R3'
    apply VRel.isCons at Vv
    rcases Vv with ⟨v',rfl⟩
    rcases u with ⟨u, IVu⟩
    injections R3
    subst_eqs
    refine TRel.intro ?_ Vw
    apply Eval.recur <;> assumption
----------------------------------------------------------------------
-- Lemma A: the capped N-ary fmap lemma                              --
----------------------------------------------------------------------

-- Source-side coherence: composing the collapsed functor with the term-side
-- sources recovers the collapse along the environment types.
lemma Typ.fmap_source_coherence {B : Typ} {l} {ρ : LRelSubs} {Ss_t : List Typ} :
    B.Wf ρ.length → l ≤ ρ.length → ρ.Closed →
    l ≤ Ss_t.length →
    (∀ j (_ : j < l) (hjS : j < Ss_t.length) (hjρ : j < ρ.length),
        Ss_t[j]'hjS = (ρ[j]'hjρ).type) →
    (B.substAll ((List.range l).map Typ.var ++ LRelSubs.types (ρ.drop l))).substAll Ss_t
      = B.substAll ρ.types := by
  intro WF hl hρcl hlS hSlive
  have hEslen : ((List.range l).map Typ.var ++ LRelSubs.types (ρ.drop l)).length = ρ.length := by
    simp only [List.length_append, List.length_map, List.length_range, LRelSubs.types_length,
      List.length_drop]
    omega
  rw [Typ.substAll_substAll (by rw [hEslen]; exact WF)]
  apply Typ.substAll_eq WF
  intro j hj
  simp only [List.getElem?_map]
  by_cases hjl : j < l
  · rw [Typ.getElem?_rangeVar_append, if_pos hjl]
    simp only [LRelSubs.types, List.getElem?_map, List.getElem?_eq_getElem hj,
      Option.map_some, Option.some.injEq]
    rw [show (Typ.var j).substAll Ss_t = Ss_t[j]'(by omega) from by
        simp only [Typ.substAll, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show j < Ss_t.length by omega), Option.getD_some]]
    exact hSlive j hjl (by omega) (by omega)
  · rw [Typ.getElem?_rangeVar_append, if_neg hjl]
    simp only [LRelSubs.types, List.getElem?_map, List.getElem?_drop,
      show l + (j - l) = j from by omega, List.getElem?_eq_getElem hj,
      Option.map_some, Option.some.injEq]
    exact Typ.substAll_closed (hρcl _ (List.getElem_mem hj)) _

/-- Free-output-environment target coherence: composing the collapsed
functor with the term-side targets recovers the collapse along an
output environment `σ'` that carries the target types on the mapped
prefix (`Cs_t[j] = σ'[j].type`) and agrees with `σ` in types on the
frozen suffix. -/
lemma Typ.fmap_out_coherence {B : Typ} {d} {σ σ' : LRelSubs} {Cs_t : List Typ} :
    B.Wf σ.length → d ≤ σ.length → σ.Closed →
    σ'.length = σ.length → d ≤ Cs_t.length →
    (∀ j (_ : j < d) (hjC : j < Cs_t.length) (hjσ' : j < σ'.length),
        Cs_t[j]'hjC = (σ'[j]'hjσ').type) →
    (∀ j (_ : d ≤ j) (hjσ : j < σ.length) (hjσ' : j < σ'.length),
        (σ'[j]'hjσ').type = (σ[j]'hjσ).type) →
    (B.substAll ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))).substAll Cs_t
      = B.substAll σ'.types := by
  intro WF hd hσcl hlen hdC hClive hfrty
  have hEslen : ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d)).length = σ.length := by
    simp only [List.length_append, List.length_map, List.length_range, LRelSubs.types_length,
      List.length_drop]
    omega
  rw [Typ.substAll_substAll (by rw [hEslen]; exact WF)]
  apply Typ.substAll_eq WF
  intro j hj
  have hjσ' : j < σ'.length := by omega
  simp only [List.getElem?_map]
  by_cases hjd : j < d
  · rw [Typ.getElem?_rangeVar_append, if_pos hjd]
    simp only [LRelSubs.types, List.getElem?_map, List.getElem?_eq_getElem hjσ',
      Option.map_some, Option.some.injEq]
    rw [show (Typ.var j).substAll Cs_t = Cs_t[j]'(by omega) from by
        simp only [Typ.substAll, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show j < Cs_t.length by omega), Option.getD_some]]
    exact hClive j hjd (by omega) hjσ'
  · rw [Typ.getElem?_rangeVar_append, if_neg hjd]
    simp only [LRelSubs.types, List.getElem?_map, List.getElem?_drop,
      show d + (j - d) = j from by omega, List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem hjσ', Option.map_some, Option.some.injEq]
    rw [Typ.substAll_closed (hσcl _ (List.getElem_mem hj))]
    exact (hfrty j (by omega) hj hjσ').symm

/-- Substitution by any cons-headed list is `sub` by the head, for
types with one free variable. -/
lemma Typ.substAll_cons_wf1 {A : Typ} (hA : A.Wf 1) (Y : Typ) (L : List Typ) :
    A.substAll (Y :: L) = A.sub Y := by
  rw [show A.substAll (Y :: L) = A.substAll [Y] from
      Typ.substAll_eq hA (fun j hj => by
        obtain rfl : j = 0 := by omega
        rfl)]
  exact Typ.substAll_singleton hA _

/-- Substitution by a `var 0`-headed list is the identity for types
with one free variable. -/
lemma Typ.substAll_var0_cons {A : Typ} (hA : A.Wf 1) (L : List Typ) :
    A.substAll (Typ.var 0 :: L) = A := by
  rw [show A.substAll (Typ.var 0 :: L) = A.substAll ((List.range 1).map Typ.var) from
      Typ.substAll_eq hA (fun j hj => by
        obtain rfl : j = 0 := by omega
        rfl)]
  exact Typ.substAll_rangeVar

/-- Every entry of `(range d).map var ++ types (σ.drop d)` is `Wf` at `Cs_t.length`
(the `var`-prefix needs `d ≤ Cs_t.length`; the tail uses closedness of `σ`). -/
lemma Typ.rangeVar_drop_getElem?_Wf {σ : LRelSubs} {d} {Cs_t : List Typ} :
    σ.Closed → d ≤ Cs_t.length →
    ∀ i, i < σ.length →
      ∃ E, ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))[i]? = some E
        ∧ E.Wf Cs_t.length := by
  intro hσcl hdC i hi
  by_cases hid : i < d
  · exact ⟨Typ.var i, by rw [Typ.getElem?_rangeVar_append, if_pos hid],
      Typ.Wf.var (by omega)⟩
  · refine ⟨(σ[i]'hi).type, ?_,
      (hσcl _ (List.getElem_mem hi)).mono (Nat.zero_le _)⟩
    rw [Typ.getElem?_rangeVar_append, if_neg hid]
    simp only [LRelSubs.types, List.getElem?_map, List.getElem?_drop,
      show d + (i - d) = i from by omega, List.getElem?_eq_getElem hi, Option.map_some]

/-- The mapped functor `apps (fmap B' fns…)` is well-typed at the coherent
arrow type `B.substAll σ.types ⟶ B.substAll σ'.types`, bundling the
source/target coherence rewrites shared by the arr/`□`/`◯` cases. -/
lemma HasType.fmap_apps_coherent {B : Typ} {d} {σ σ' : LRelSubs}
    {Ss_t Cs_t : List Typ} {ε'} {fns : List MVal} :
    B.Wf σ.length →
    (B.substAll ((List.range d).map Typ.var
        ++ LRelSubs.types (σ.drop d))).Wf Cs_t.length →
    d ≤ σ.length → σ.Closed → σ'.length = σ.length →
    d ≤ Cs_t.length → Ss_t.length = Cs_t.length →
    (∀ S ∈ Ss_t, S.Closed) → (∀ T' ∈ Cs_t, T'.Closed) →
    fns.length = Cs_t.length →
    (∀ j (_ : j < d) (hjC : j < Cs_t.length) (hjσ' : j < σ'.length),
        Cs_t[j]'hjC = (σ'[j]'hjσ').type) →
    (∀ j (_ : d ≤ j) (hjσ : j < σ.length) (hjσ' : j < σ'.length),
        (σ'[j]'hjσ').type = (σ[j]'hjσ).type) →
    (∀ j (_ : j < d) (hjS : j < Ss_t.length) (hjσ : j < σ.length),
        Ss_t[j]'hjS = (σ[j]'hjσ).type) →
    (∀ j (hjS : j < Ss_t.length) (hjC : j < Cs_t.length) (hjf : j < fns.length),
        ⊢{ε'} (fns[j]'hjf).val ∷ Ss_t[j]'hjS ⟶ Cs_t[j]'hjC) →
    ⊢{ε'} Term.apps (Term.fmap (B.substAll ((List.range d).map Typ.var
        ++ LRelSubs.types (σ.drop d))) Cs_t) (fns.map Subtype.val)
      ∷ B.substAll σ.types ⟶ B.substAll σ'.types := by
  intro WF hBF hd hσcl hσ'len hdC hSClen hScl hCcl hflen hClive hfrty hSlive hfnsT
  have hann := Typ.fmap_out_coherence (B := B) (Cs_t := Cs_t) WF hd hσcl hσ'len hdC hClive hfrty
  have hsrc := Typ.fmap_source_coherence (B := B) (Ss_t := Ss_t) WF hd hσcl (by omega) hSlive
  have h := HasType.apps (HasType.fmap hBF hSClen hScl hCcl) hSClen
    (show (fns.map Subtype.val).length = Cs_t.length by simpa using hflen)
    (fun i hiS hiC hif => by
      rw [List.getElem_map]
      exact hfnsT i hiS hiC (by simpa using hif))
  rwa [hsrc, hann] at h

/-- The statement of the mapped `fmap` lemma (`VRel.fmap_mapped`) for a
fixed body `C0`, abstracted so the µ-case's rebuild lemmas can take it as
a hypothesis. -/
def VRel.FmapMappedIH (C0 : Typ) : Prop :=
  ∀ {d : Nat} {σ σ' : LRelSubs} {Ss_t Cs_t : List Typ} {ε' : Env} {fns : List MVal}
    {x : MVal} {body : Term},
    C0.Wf σ.length →
    d ≤ σ.length →
    σ'.length = σ.length →
    (∀ s ∈ σ, LRelOf.Good s) →
    (∀ s ∈ σ', LRelOf.Good s) →
    Ss_t.length = Cs_t.length →
    fns.length = Cs_t.length →
    d ≤ Cs_t.length →
    (∀ S ∈ Ss_t, S.Closed) →
    (∀ T' ∈ Cs_t, T'.Closed) →
    (∀ j (_ : j < d) (hjS : j < Ss_t.length) (hjσ : j < σ.length),
        Ss_t[j]'hjS = (σ[j]'hjσ).type) →
    (∀ j (_ : j < d) (hjC : j < Cs_t.length) (hjσ' : j < σ'.length),
        Cs_t[j]'hjC = (σ'[j]'hjσ').type) →
    (∀ j (_ : d ≤ j) (hjσ : j < σ.length) (hjσ' : j < σ'.length),
        (σ'[j]'hjσ').type = (σ[j]'hjσ).type) →
    (∀ j (hjS : j < Ss_t.length) (hjC : j < Cs_t.length) (hjf : j < fns.length),
        ⊢{ε'} (fns[j]'hjf).val ∷ Ss_t[j]'hjS ⟶ Cs_t[j]'hjC) →
    (∀ fn ∈ fns, ∀ (σs : Subs) (k : Nat), fn.val.subs σs k = fn.val) →
    (∀ j (_ : j < d) (hjσ : j < σ.length), LRelOf.Stable (σ[j]'hjσ)) →
    (∀ j (_ : j < d) (hjσ : j < σ.length) (hjσ' : j < σ'.length) (hjf : j < fns.length),
        ∀ {ε'' : Env} {a : MVal}, ε'.le ε'' → (σ[j]'hjσ).rel ε'' a →
        ∃ (w : MVal) (ε''' : Env), ((fns[j]'hjf).val.app a.val, ε'') ⇓ (w, ε''') ∧
          (σ'[j]'hjσ').rel ε''' w) →
    (∀ j (_ : d ≤ j) (hjσ : j < σ.length) (hjσ' : j < σ'.length),
        ∀ (ε₀ : Env) (w : MVal), (σ[j]'hjσ).rel ε₀ w → (σ'[j]'hjσ').rel ε₀ w) →
    (∀ j (hjσ' : j < σ'.length), LRelOf.Stable (σ'[j]'hjσ')) →
    Term.fmap (C0.substAll ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))) Cs_t
        = Term.nlam Cs_t.length (Term.lam body) →
    x ∈ V⟦C0⟧σ#ε' →
    body.subs (x.val :: fns.reverse.map Subtype.val) 0 ∈ T⟦C0⟧σ'#ε'

/-- Generalized constructive µ-rebuild: a rebuild instance at the closed
recursive type `(μ C0).substAll σt.types` applied to a folded value
evaluates to a folded value whose body is again over `e :: σt`, for any
Good+Stable var-0 entry `e`.  Generalizes `VRel.mu_rebstep` to arbitrary
Good+Stable tail environments. -/
lemma VRel.mu_fmap_rebuild_eval {C0} {σt : LRelSubs} {e : LRelOf}
    (ihM : VRel.FmapMappedIH C0)
    (WF : C0.Wf (σt.length + 1))
    (hGt : ∀ s ∈ σt, LRelOf.Good s)
    (hstt : ∀ j (hj : j < σt.length), LRelOf.Stable (σt[j]'hj))
    (hety : e.type = (μ C0).substAll (LRelSubs.types σt))
    (hGe : LRelOf.Good e) (hSte : LRelOf.Stable e)
    {Ss_rb Cs_rb : List Typ} {fns_rb : List MVal} {body'} {ε₅} {u₅ : MVal}
    (hSC : Ss_rb.length = Cs_rb.length)
    (hfl : fns_rb.length = Cs_rb.length)
    (hSscl : ∀ S ∈ Ss_rb, S.Closed)
    (hCscl : ∀ T' ∈ Cs_rb, T'.Closed)
    (hfT : ∀ j (hjS : j < Ss_rb.length) (hjC : j < Cs_rb.length) (hjf : j < fns_rb.length),
        ⊢{ε₅} (fns_rb[j]'hjf).val ∷ Ss_rb[j]'hjS ⟶ Cs_rb[j]'hjC)
    (hfcl : ∀ fn ∈ fns_rb, ∀ (σs : Subs) (k : Nat), fn.val.subs σs k = fn.val)
    (hbody : Term.fmap ((μ C0).substAll (LRelSubs.types σt)) Cs_rb
        = Term.nlam Cs_rb.length (Term.lam body'))
    (Hu : u₅ ∈ V⟦C0⟧(e :: σt)#ε₅) :
    ∃ (u₆ : MVal) (ε₆ : Env),
      (body'.subs ((MVal.cons (C0.substAll (Typ.var 0 :: LRelSubs.types σt)) u₅).val
          :: fns_rb.reverse.map Subtype.val) 0, ε₅)
        ⇓ (MVal.cons (C0.substAll (Typ.var 0 :: LRelSubs.types σt)) u₆, ε₆) ∧
      u₆ ∈ V⟦C0⟧(e :: σt)#ε₆ := by
  have hσtcl : σt.Closed := fun s hs => (hGt s hs).closed
  have hLBLwf : (C0.substAll (Typ.var 0 :: LRelSubs.types σt)).Wf 1 := by
    refine Typ.substAll_Wf WF ?_
    intro i hi
    rcases i with _ | k
    · exact ⟨Typ.var 0, rfl, Typ.Wf.var (by omega)⟩
    · refine ⟨(σt[k]'(by omega)).type, ?_,
        ((hGt _ (List.getElem_mem _)).closed).mono (Nat.zero_le _)⟩
      simp only [List.getElem?_cons_succ, LRelSubs.types, List.getElem?_map]
      rw [List.getElem?_eq_getElem (show k < σt.length by omega), Option.map_some]
  have hTμ : (μ C0).substAll (LRelSubs.types σt)
      = μ (C0.substAll (Typ.var 0 :: LRelSubs.types σt)) := by
    simp only [Typ.substAll]
    rw [map_shift_closed hσtcl.types]
  have hμLBLcl : (μ (C0.substAll (Typ.var 0 :: LRelSubs.types σt))).Closed := Typ.Wf.mu hLBLwf
  -- expose the recur shape of the rebuild body
  rw [hTμ] at hbody
  simp only [Term.fmap] at hbody
  rw [map_shift_closed hCscl, Typ.substAll_var0_cons hLBLwf] at hbody
  obtain rfl := Term.nlam_lam_inj hbody.symm
  -- abbreviate the rebuilt body (this subterm recurs ~70× below)
  set Cμ : Typ := C0.substAll (Typ.var 0 :: LRelSubs.types σt) with hCμ
  -- the substituted step term
  set STEPS : Term := Term.cons Cμ
      ((Term.apps (Term.fmap Cμ
          ((μ Cμ) :: Cs_rb))
        ((Term.var 0).pr2.lam :: fns_rb.map Subtype.val)).app (Term.var 0)) with hSTEPS
  have hCc2 : ∀ C ∈ (μ Cμ) :: Cs_rb, C.Closed := by
    intro C hC
    headTail hC
    · exact hμLBLcl
    · exact hCscl C hC
  have hAWfM : Cμ.Wf
      ((μ Cμ) :: Cs_rb).length :=
    hLBLwf.mono (by simp)
  have hbodye : Term.fmap e.type Cs_rb = Term.nlam Cs_rb.length (Term.lam
      (Term.recur (μ Cμ)
        (Term.cons Cμ
          ((Term.apps (Term.fmap Cμ
              ((μ Cμ) :: Cs_rb))
            ((Term.var 0).pr2.lam
              :: (List.range Cs_rb.length).map (fun i => Term.var (Cs_rb.length + 1 - i)))).app
              (Term.var 0)))
        (Term.var 0))) := by
    rw [hety, hTμ]
    simp only [Term.fmap]
    rw [map_shift_closed hCscl, Typ.substAll_var0_cons hLBLwf]
  have hsubst : ∀ (xt : Term),
      (Term.recur (μ Cμ)
        (Term.cons Cμ
          ((Term.apps (Term.fmap Cμ
              ((μ Cμ) :: Cs_rb))
            ((Term.var 0).pr2.lam
              :: (List.range Cs_rb.length).map (fun i => Term.var (Cs_rb.length + 1 - i)))).app
              (Term.var 0)))
        (Term.var 0)).subs (xt :: fns_rb.reverse.map Subtype.val) 0
      = Term.recur (μ Cμ) STEPS xt := by
    intro xt
    simp only [Term.subs, Term.subs_apps, List.map_cons, Term.fmap_subs hAWfM hCc2,
      Term.fmap_fns_subs1 hfl,
      dif_pos (show 0 < (xt :: fns_rb.reverse.map Subtype.val).length by simp),
      Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd,
      reduceDIte, List.get_eq_getElem, List.getElem_cons_zero, hSTEPS]
  rw [hsubst]
  -- the pairing realiser of the rebuild recursion
  set pairfn : Term := Term.lam (Term.pair (Term.var 0)
      (Term.recur (μ Cμ) STEPS (Term.var 0)))
    with hpairfn
  -- typing of the substituted step term (used for the realiser's typing)
  have Tsteps : ∀ {Γ : Ctx},
      (Cμ.sub ((μ Cμ) ⨂ (μ Cμ)) :: Γ) ⊢{ε₅}
        STEPS ∷ μ Cμ := by
    intro Γ
    refine HasType.cons hμLBLcl ?_
    refine HasType.app' (A := Cμ.sub ((μ Cμ) ⨂ (μ Cμ))) ?_ ?_
    · rw [show Cμ.sub ((μ Cμ) ⨂ (μ Cμ))
          = Cμ.substAll ((((μ Cμ) ⨂ (μ Cμ))) :: Ss_rb) from
          (Typ.substAll_cons_wf1 hLBLwf _ _).symm]
      exact HasType.var rfl
    · have happs : (Cμ.sub ((μ Cμ) ⨂ (μ Cμ)) :: Γ) ⊢{ε₅}
          Term.apps (Term.fmap Cμ
              ((μ Cμ) :: Cs_rb))
            ((Term.var 0).pr2.lam :: fns_rb.map Subtype.val)
          ∷ Cμ.substAll ((((μ Cμ) ⨂ (μ Cμ))) :: Ss_rb)
            ⟶ Cμ.substAll ((μ Cμ) :: Cs_rb) :=
        HasType.apps (HasType.fmap hAWfM
          (by simp only [List.length_cons, hSC])
          (fun S hS => by
            headTail hS
            · exact Typ.Wf.prod hμLBLcl hμLBLcl
            · exact hSscl S hS)
          hCc2)
        (by simp only [List.length_cons, hSC])
        (by simp only [List.length_cons, List.length_map, hfl])
        (fun i hiS hiC hif => by
          cases i with
          | zero =>
              simp only [List.getElem_cons_zero]
              exact HasType.lam (Typ.Wf.prod hμLBLcl hμLBLcl)
                (HasType.pr2 (HasType.var rfl))
          | succ j =>
              simp only [List.getElem_cons_succ, List.getElem_map]
              simp only [List.length_cons] at hiS hiC
              simp only [List.length_cons, List.length_map] at hif
              exact HasType.weaken_closed (hfT j (by omega) (by omega) (by omega)))
      rw [Typ.substAll_cons_wf1 hLBLwf, Typ.substAll_cons_wf1 hLBLwf] at happs
      exact happs
  have Tpairfn : ⊢{ε₅} pairfn ∷ (μ Cμ)
      ⟶ ((μ Cμ) ⨂ (μ Cμ)) := by
    refine HasType.lam hμLBLcl (HasType.pair (HasType.var rfl) ?_)
    exact HasType.recur hμLBLcl hμLBLcl Tsteps (HasType.var rfl)
  have hpairfncl : ∀ (σs : Subs) (k : Nat), pairfn.subs σs k = pairfn :=
    fun σs k => HasType.closed Tpairfn
  -- environment facts
  have hGall : ∀ u ∈ (e :: σt : LRelSubs), LRelOf.Good u := by
    intro u hu
    headTail hu
    · exact hGe
    · exact hGt u hu
  have hGpair : LRelOf.Good (LRelOf.pairE e e) := LRelOf.Good.pairE hGe hGe
  have hStpair : LRelOf.Stable (LRelOf.pairE e e) := LRelOf.Stable.pairE hGe hGe hSte hSte
  -- the fmap₁ step: head mapped into the conjunctive pair entry
  obtain ⟨bodyf, hbodyf⟩ := Term.fmap_nlam Cμ
    [(μ Cμ) ⨂ (μ Cμ)]
  have hbodyf' : Term.fmap (C0.substAll ((List.range 1).map Typ.var
        ++ LRelSubs.types ((e :: σt : LRelSubs).drop 1)))
        [(μ Cμ) ⨂ (μ Cμ)]
      = Term.nlam ([(μ Cμ) ⨂ (μ Cμ)] : List Typ).length
          (Term.lam bodyf) := by
    rw [show C0.substAll ((List.range 1).map Typ.var
          ++ LRelSubs.types ((e :: σt : LRelSubs).drop 1))
        = Cμ from by
      simp only [List.range_one, List.map_cons, List.map_nil, List.singleton_append,
        List.drop_succ_cons, List.drop_zero, hCμ]]
    exact hbodyf
  have hstep_rb := ihM (d := 1) (σ := e :: σt) (σ' := LRelOf.pairE e e :: σt)
    (Ss_t := [μ Cμ])
    (Cs_t := [(μ Cμ) ⨂ (μ Cμ)])
    (fns := [⟨pairfn, IsMValue.lam⟩])
    (by simpa using WF) (by simp) (by simp) hGall
    (fun u hu => by
      headTail hu
      · exact hGpair
      · exact hGt u hu)
    rfl rfl (by simp)
    (fun S hS => by rw [List.mem_singleton] at hS; subst hS; exact hμLBLcl)
    (fun T hT => by
      rw [List.mem_singleton] at hT
      subst hT
      exact Typ.Wf.prod hμLBLcl hμLBLcl)
    (fun j hjl hjS hjσ => by
      obtain rfl : j = 0 := by omega
      simp only [List.getElem_cons_zero]
      rw [hety, hTμ])
    (fun j hjl hjC hjσ' => by
      obtain rfl : j = 0 := by omega
      simp only [List.getElem_cons_zero, LRelOf.pairE_type]
      rw [hety, hTμ])
    (fun j hj hjσ hjσ' => by
      cases j with
      | zero => omega
      | succ k => simp only [List.getElem_cons_succ])
    (fun j hjS hjC hjf => by
      obtain rfl : j = 0 := by
        simp only [List.length_singleton] at hjS
        omega
      simpa only [List.getElem_cons_zero] using Tpairfn)
    (fun fn hfn σs k => by
      rw [List.mem_singleton] at hfn
      subst hfn
      exact hpairfncl σs k)
    (fun j hjl hjσ => by
      obtain rfl : j = 0 := by omega
      simpa only [List.getElem_cons_zero] using hSte)
    (fun j hjl hjσ hjσ' hjf {ε₂} {a} S₂ Ra => by
      obtain rfl : j = 0 := by omega
      simp only [List.getElem_cons_zero] at Ra ⊢
      -- rebuild the argument through the entry's stability
      obtain ⟨b, εb, Rb, hbe⟩ := hSte.2 hSC hfl hSscl hCscl
        (fun j hjS hjC hjf => (hfT j hjS hjC hjf).le' S₂) hfcl Ra hbodye
      rw [hsubst a.val] at Rb
      refine ⟨MVal.pair a b, εb, ?_, ?_⟩
      · refine Eval.app (Eval.value IsMValue.lam) (Eval.value a.2) ?_
        rw [show (Term.pair (Term.var 0)
              (Term.recur (μ Cμ) STEPS
                (Term.var 0))).sub a.val
              = Term.pair a.val
                (Term.recur (μ Cμ) STEPS a.val)
            from by
            simp only [Term.sub, Term.subs, hSTEPS, Term.subs_apps,
              List.map_cons, Term.fmap_subs hAWfM hCc2,
              Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd, reduceDIte,
              List.get_eq_getElem, List.getElem_cons_zero,
              List.length_cons, List.length_nil, Nat.lt_irrefl,
              show (fns_rb.map Subtype.val).map (·.subs [a.val] 1) = fns_rb.map Subtype.val
                from by
                  rw [List.map_map]
                  apply List.map_congr_left
                  intro fn hfn
                  exact hfcl fn hfn [a.val] 1]]
        exact Eval.pair (Eval.value a.2) Rb
      · simp only [LRelOf.pairE_rel]
        exact ⟨a, b, rfl, hGe.wf ε₂ εb a Rb.incr Ra, hbe⟩)
    (fun j hj hjσ hjσ' => by
      cases j with
      | zero => omega
      | succ k =>
          intro ε₀ w hw
          simpa only [List.getElem_cons_succ] using hw)
    (fun j hjσ' => by
      cases j with
      | zero => simpa only [List.getElem_cons_zero] using hStpair
      | succ k =>
          simp only [List.length_cons] at hjσ'
          simpa only [List.getElem_cons_succ] using hstt k (by omega))
    hbodyf' Hu
  obtain ⟨w₁, ε_w, R_fmap0, Vw₁⟩ := (TRel.fmap_apps_app hbodyf rfl
    (fun fn hfn σs k => by
      rw [List.mem_singleton] at hfn
      subst hfn
      exact hpairfncl σs k)
    (Eval.value u₅.2) hstep_rb).elim
  -- the layer: pair head mapped through `pr2` back into the entry
  obtain ⟨bodyL, hbodyL⟩ := Term.fmap_nlam Cμ
    ((μ Cμ) :: Cs_rb)
  have hbodyL' : Term.fmap (C0.substAll ((List.range 1).map Typ.var
        ++ LRelSubs.types ((LRelOf.pairE e e :: σt : LRelSubs).drop 1)))
        ((μ Cμ) :: Cs_rb)
      = Term.nlam ((μ Cμ) :: Cs_rb).length
          (Term.lam bodyL) := by
    rw [show C0.substAll ((List.range 1).map Typ.var
          ++ LRelSubs.types ((LRelOf.pairE e e :: σt : LRelSubs).drop 1))
        = Cμ from by
      simp only [List.range_one, List.map_cons, List.map_nil, List.singleton_append,
        List.drop_succ_cons, List.drop_zero, hCμ]]
    exact hbodyL
  have hlayer_rb := ihM (d := 1) (σ := LRelOf.pairE e e :: σt) (σ' := e :: σt)
    (Ss_t := ((μ Cμ) ⨂ (μ Cμ)) :: Ss_rb)
    (Cs_t := (μ Cμ) :: Cs_rb)
    (fns := ⟨(Term.var 0).pr2.lam, IsMValue.lam⟩ :: fns_rb)
    (by simpa using WF) (by simp) (by simp)
    (fun u hu => by
      headTail hu
      · exact hGpair
      · exact hGt u hu)
    hGall
    (by simp only [List.length_cons, hSC]) (by simp only [List.length_cons, hfl])
    (by simp)
    (fun S hS => by
      headTail hS
      · exact Typ.Wf.prod hμLBLcl hμLBLcl
      · exact hSscl S hS)
    hCc2
    (fun j hjl hjS hjσ => by
      obtain rfl : j = 0 := by omega
      simp only [List.getElem_cons_zero, LRelOf.pairE_type]
      rw [hety, hTμ])
    (fun j hjl hjC hjσ' => by
      obtain rfl : j = 0 := by omega
      simp only [List.getElem_cons_zero]
      rw [hety, hTμ])
    (fun j hj hjσ hjσ' => by
      cases j with
      | zero => omega
      | succ k => simp only [List.getElem_cons_succ])
    (fun j hjS hjC hjf => by
      cases j with
      | zero =>
          simp only [List.getElem_cons_zero]
          exact HasType.lam (Typ.Wf.prod hμLBLcl hμLBLcl)
            (HasType.pr2 (HasType.var rfl))
      | succ i =>
          simp only [List.getElem_cons_succ]
          simp only [List.length_cons] at hjS hjC hjf
          exact (hfT i (by omega) (by omega) (by omega)).le' R_fmap0.incr)
    (fun fn hfn σs k => by
      headTail hfn
      · rfl
      · exact hfcl fn hfn σs k)
    (fun j hjl hjσ => by
      obtain rfl : j = 0 := by omega
      simpa only [List.getElem_cons_zero] using hStpair)
    (fun j hjl hjσ hjσ' hjf {ε₂} {p} S₂ Rp => by
      obtain rfl : j = 0 := by omega
      simp only [List.getElem_cons_zero, LRelOf.pairE_rel] at Rp ⊢
      obtain ⟨a, b, rfl, Ra, Rb⟩ := Rp
      refine ⟨b, ε₂, ?_, Rb⟩
      refine Eval.app (Eval.value IsMValue.lam) (Eval.value (MVal.pair a b).2) ?_
      show ((Term.var 0).pr2.subs ((MVal.pair a b).val :: []) 0, ε₂) ⇓ (b, ε₂)
      simp only [Term.subs]
      exact Eval.pr2 (Eval.value (MVal.pair a b).2))
    (fun j hj hjσ hjσ' => by
      cases j with
      | zero => omega
      | succ k =>
          intro ε₀ w hw
          simpa only [List.getElem_cons_succ] using hw)
    (fun j hjσ' => by
      cases j with
      | zero => simpa only [List.getElem_cons_zero] using hSte
      | succ k =>
          simp only [List.length_cons] at hjσ'
          simpa only [List.getElem_cons_succ] using hstt k (by omega))
    hbodyL' Vw₁
  obtain ⟨u₆, ε₆', R_L, Vu₆⟩ := (TRel.fmap_apps_app hbodyL
    (by simp only [List.length_cons, hfl])
    (fun fn hfn σs k => by
      headTail hfn
      · rfl
      · exact hfcl fn hfn σs k)
    (Eval.value w₁.2) hlayer_rb).elim
  -- assemble the recur evaluation
  have R_step : (STEPS.sub w₁.val, ε_w)
      ⇓ (MVal.cons Cμ u₆, ε₆') := by
    rw [show STEPS.sub w₁.val
          = Term.cons Cμ
            ((Term.apps (Term.fmap Cμ
                ((μ Cμ) :: Cs_rb))
              ((Term.var 0).pr2.lam :: fns_rb.map Subtype.val)).app w₁.val) from by
        simp only [hSTEPS, Term.sub, Term.subs, Term.subs_apps, List.map_cons,
          Term.fmap_subs hAWfM hCc2,
          Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd, reduceDIte,
          List.get_eq_getElem, List.getElem_cons_zero, List.length_cons, List.length_nil,
          Nat.lt_irrefl,
          show (fns_rb.map Subtype.val).map (·.subs [w₁.val] 0) = fns_rb.map Subtype.val
            from by
              rw [List.map_map]
              apply List.map_congr_left
              intro fn hfn
              exact hfcl fn hfn [w₁.val] 0]]
    exact Eval.cons R_L
  refine ⟨u₆, ε₆', ?_, Vu₆⟩
  refine Eval.recur (Eval.value (MVal.cons Cμ u₅).2)
    ?_ R_step
  exact R_fmap0

/-- A given rebuild step on a folded value over a Good+Stable var-0
entry lands back in the same shape (determinism matching of
`VRel.mu_fmap_rebuild_eval`; generalizes `VRel.mu_rebstep`). -/
lemma VRel.mu_fmap_rebuild_land {C0} {σt : LRelSubs} {e : LRelOf}
    (ihM : VRel.FmapMappedIH C0)
    (WF : C0.Wf (σt.length + 1))
    (hGt : ∀ s ∈ σt, LRelOf.Good s)
    (hstt : ∀ j (hj : j < σt.length), LRelOf.Stable (σt[j]'hj))
    (hety : e.type = (μ C0).substAll (LRelSubs.types σt))
    (hGe : LRelOf.Good e) (hSte : LRelOf.Stable e)
    {ε₅ ε₆} {u₅ v₆ : MVal}
    (Hu : u₅ ∈ V⟦C0⟧(e :: σt)#ε₅)
    (hstep : RebStep ((μ C0).substAll (LRelSubs.types σt)) ε₅
        (MVal.cons (C0.substAll (Typ.var 0 :: LRelSubs.types σt)) u₅) ε₆ v₆) :
    ∃ u₆, v₆ = MVal.cons (C0.substAll (Typ.var 0 :: LRelSubs.types σt)) u₆ ∧
      u₆ ∈ V⟦C0⟧(e :: σt)#ε₆ := by
  obtain ⟨Ss_rb, Cs_rb, fns_rb, body', hSC, hfl, hSscl, hCscl, hfT, hfcl, hbody, Reval⟩ := hstep
  obtain ⟨u₆, ε₆', Rc, Vu₆⟩ := VRel.mu_fmap_rebuild_eval ihM WF hGt hstt hety hGe hSte
    hSC hfl hSscl hCscl hfT hfcl hbody Hu
  have heq := Eval.determ Reval Rc
  injection heq with heq1 heq2
  subst heq1
  subst heq2
  exact ⟨u₆, rfl, Vu₆⟩

/-- Canonical µ-entries over pointwise-Good, pointwise-Stable
environments are rebuild-stable, by Park induction with the
descendant-closed predicate "all rebuild descendants stay in the fixed
point, and rebuild instances on them evaluate". -/
lemma VRel.mu_fmap_stable {C0} {σt : LRelSubs} :
    VRel.FmapMappedIH C0 →
    C0.Wf (σt.length + 1) →
    (∀ s ∈ σt, LRelOf.Good s) →
    (∀ j (hj : j < σt.length), LRelOf.Stable (σt[j]'hj)) →
    LRelOf.Stable (LRelOf.mu C0 σt) := by
  intro ihM WF hGt hstt
  have hσtcl : σt.Closed := fun s hs => (hGt s hs).closed
  have WSt : LRelSubs.Kripke σt := fun s hs => (hGt s hs).wf
  have hμWf : (μ C0).Wf σt.length := Typ.Wf.mu WF
  have hmono : LRel.Mono (VRel.muOper C0 σt) := VRel.muOper_mono WF
  -- the rebuild-descendant-closed Park predicate
  set X : LRel := fun ε₂ v => ∀ ε₃, ε₂.le ε₃ → ∀ (ε₄ : Env) (v₄ : MVal),
    RebStar ((μ C0).substAll (LRelSubs.types σt)) ε₃ v ε₄ v₄ →
    v₄ ∈ V⟦μ C0⟧σt#ε₄ ∧
    (∀ {Ss_t Cs_t : List Typ} {fns : List MVal} {body' : Term},
      Ss_t.length = Cs_t.length → fns.length = Cs_t.length →
      (∀ S ∈ Ss_t, S.Closed) → (∀ T' ∈ Cs_t, T'.Closed) →
      (∀ j (hjS : j < Ss_t.length) (hjC : j < Cs_t.length) (hjf : j < fns.length),
          ⊢{ε₄} (fns[j]'hjf).val ∷ Ss_t[j]'hjS ⟶ Cs_t[j]'hjC) →
      (∀ fn ∈ fns, ∀ (σs : Subs) (k : Nat), fn.val.subs σs k = fn.val) →
      Term.fmap ((μ C0).substAll (LRelSubs.types σt)) Cs_t
          = Term.nlam Cs_t.length (Term.lam body') →
      ∃ (w' : MVal) (ε₅ : Env),
        (body'.subs (v₄.val :: fns.reverse.map Subtype.val) 0, ε₄) ⇓ (w', ε₅)) with hX
  have hXwf : LRel.Kripke X := by
    intro ε₁ ε₂ v S hv ε₃ S23 ε₄ v₄ hstar
    exact hv ε₃ (S.trans S23) ε₄ v₄ hstar
  -- the Park-meet entry
  set eP : LRelOf := ⟨(μ C0).substAll (LRelSubs.types σt),
    fun ε₂ w => LRel.lfp (VRel.muOper C0 σt) ε₂ w ∧ X ε₂ w⟩ with heP
  have hGeP : LRelOf.Good eP := by
    refine ⟨?_, ?_, ?_⟩
    · exact Typ.substAll_Wf_closed (by simpa using hμWf) hσtcl.types
    · intro v ε₁ ε₂ S hv
      exact ⟨LRel.lfp.kripke _ _ _ S hv.1, hXwf _ _ _ S hv.2⟩
    · intro ε₁ w hw
      have h1 := hw.1
      rw [← VRel.mu_def] at h1
      exact VRel.HasType_open hσtcl hμWf h1
  have hSteP : LRelOf.Stable eP := by
    refine ⟨rfl, ?_⟩
    intro Ss' Cs' fns' ε₀ w body'' h1 h2 h3 h4 h5 h6 hw hbody''
    obtain ⟨w', ε₁, R⟩ := (hw.2 ε₀ (Env.refl ε₀) ε₀ w RebStar.refl).2
      h1 h2 h3 h4 h5 h6 hbody''
    have hstep1 : RebStep ((μ C0).substAll (LRelSubs.types σt)) ε₀ w ε₁ w' :=
      ⟨Ss', Cs', fns', body'', h1, h2, h3, h4, h5, h6, hbody'', R⟩
    refine ⟨w', ε₁, R, ?_, ?_⟩
    · have hmem := (hw.2 ε₀ (Env.refl ε₀) ε₁ w' (RebStar.single hstep1)).1
      rw [VRel.mu_def] at hmem
      exact hmem
    · intro ε₃' S₁₃' ε₄' v₄' hstar'
      exact hw.2 ε₀ (Env.refl ε₀) ε₄' v₄'
        (RebStar.trans (RebStar.weak (RebStar.single hstep1) S₁₃') hstar')
  have WSP : LRelSubs.Kripke (eP :: σt) := by
    intro u hu
    headTail hu
    · exact hGeP.wf
    · exact WSt u hu
  -- entry demotion to the canonical entry
  have hLe : LRelSubs.Le (eP :: σt) (LRelOf.mu C0 σt :: σt) := by
    refine (LRelSubs.Le.refl σt).cons rfl ?_
    intro ε₀ v hv
    simp only [LRelOf.mu_rel]
    rw [VRel.mu_def]
    exact hv.1
  -- the key: every fixed-point member satisfies the Park predicate
  have key : ∀ {ε₂ : Env} {v : MVal}, v ∈ V⟦μ C0⟧σt#ε₂ → X ε₂ v := by
    intro ε₂ v hv
    rw [VRel.mu_def] at hv
    refine LRel.lfp.strong_induction hmono hXwf ?_ ε₂ v hv
    intro ε₂' a ha
    obtain ⟨a', hcons, Ha'⟩ := ha
    rw [show C0.substAll (Typ.var 0 :: (LRelSubs.types σt).map (Typ.shift 0))
          = C0.substAll (Typ.var 0 :: LRelSubs.types σt) from by
        rw [map_shift_closed hσtcl.types]] at hcons
    subst hcons
    intro ε₃ S23 ε₄ v₄ hstar
    have descend : ∀ {εa εb : Env} {va vb : MVal},
        RebStar ((μ C0).substAll (LRelSubs.types σt)) εa va εb vb →
        ∀ {u : MVal}, va = MVal.cons (C0.substAll (Typ.var 0 :: LRelSubs.types σt)) u →
        u ∈ V⟦C0⟧(eP :: σt)#εa →
        ∃ u₄, vb = MVal.cons (C0.substAll (Typ.var 0 :: LRelSubs.types σt)) u₄ ∧
          u₄ ∈ V⟦C0⟧(eP :: σt)#εb := by
      intro εa εb va vb h
      induction h with
      | refl =>
          intro u hva Hu
          exact ⟨u, hva, Hu⟩
      | weak hst S ihd =>
          intro u hva Hu
          obtain ⟨u₄, rfl, Hu₄⟩ := ihd hva Hu
          exact ⟨u₄, rfl, VRel.kripke WSP Hu₄ S⟩
      | tail hst hstep ihd =>
          intro u hva Hu
          obtain ⟨u₄, rfl, Hu₄⟩ := ihd hva Hu
          exact VRel.mu_fmap_rebuild_land ihM WF hGt hstt rfl hGeP hSteP Hu₄ hstep
    obtain ⟨u₄, rfl, Hu₄⟩ := descend hstar rfl (VRel.kripke WSP Ha' S23)
    constructor
    · -- membership of the descendant
      rw [VRel.mu_unfold WF WSt]
      refine ⟨u₄, by rw [map_shift_closed hσtcl.types], ?_⟩
      exact VRel.mono_env hLe (by simpa using WF) Hu₄
    · -- rebuild instances on the descendant evaluate
      intro Ss' Cs' fns' body'' h1 h2 h3 h4 h5 h6 hbody''
      obtain ⟨u₆, ε₆, Rc, _⟩ := VRel.mu_fmap_rebuild_eval ihM WF hGt hstt rfl hGeP hSteP
        h1 h2 h3 h4 h5 h6 hbody'' Hu₄
      exact ⟨_, ε₆, Rc⟩
  -- conclude stability of the canonical entry
  refine ⟨rfl, ?_⟩
  intro Ss' Cs' fns' ε₀ w body'' h1 h2 h3 h4 h5 h6 hw hbody''
  simp only [LRelOf.mu_rel] at hw
  have hXw := key hw
  obtain ⟨w', ε₁, R⟩ := (hXw ε₀ (Env.refl ε₀) ε₀ w RebStar.refl).2
    h1 h2 h3 h4 h5 h6 hbody''
  have hstep1 : RebStep ((μ C0).substAll (LRelSubs.types σt)) ε₀ w ε₁ w' :=
    ⟨Ss', Cs', fns', body'', h1, h2, h3, h4, h5, h6, hbody'', R⟩
  have hmem := (hXw ε₀ (Env.refl ε₀) ε₁ w' (RebStar.single hstep1)).1
  exact ⟨w', ε₁, R, by simpa only [LRelOf.mu_rel] using hmem⟩

/-- full-relation N-ary `fmap` soundness with per-position semantic
  rebuild evidence.  The first `d` variables are mapped — `fns[j]`
  sends the input entry `σ[j]` into the output entry `σ'[j]` — and the
  rest are frozen, rebuilding from `σ[j]` into `σ'[j]` through their
  `RebuildsInto` evidence.  The output is `C` itself over the output
  environment `σ'`.  Mapped input entries must be `Stable` (inner
  µ-cases freeze them and rebuild in place); frozen output entries
  must be `Stable` (the µ-case's layer rebuilds them a second time).
  -/
lemma VRel.fmap_mapped : ∀ {C : Typ} {d} {σ σ' : LRelSubs}
    {Ss_t Cs_t : List Typ} {ε'} {fns : List MVal} {x : MVal} {body},
    C.Wf σ.length →
    d ≤ σ.length →
    σ'.length = σ.length →
    (∀ s ∈ σ, LRelOf.Good s) →
    (∀ s ∈ σ', LRelOf.Good s) →
    Ss_t.length = Cs_t.length →
    fns.length = Cs_t.length →
    d ≤ Cs_t.length →
    (∀ S ∈ Ss_t, S.Closed) →
    (∀ T' ∈ Cs_t, T'.Closed) →
    (∀ j (_ : j < d) (hjS : j < Ss_t.length) (hjσ : j < σ.length),
        Ss_t[j]'hjS = (σ[j]'hjσ).type) →
    (∀ j (_ : j < d) (hjC : j < Cs_t.length) (hjσ' : j < σ'.length),
        Cs_t[j]'hjC = (σ'[j]'hjσ').type) →
    (∀ j (_ : d ≤ j) (hjσ : j < σ.length) (hjσ' : j < σ'.length),
        (σ'[j]'hjσ').type = (σ[j]'hjσ).type) →
    (∀ j (hjS : j < Ss_t.length) (hjC : j < Cs_t.length) (hjf : j < fns.length),
        ⊢{ε'} (fns[j]'hjf).val ∷ Ss_t[j]'hjS ⟶ Cs_t[j]'hjC) →
    (∀ fn ∈ fns, ∀ (σs : Subs) (k : Nat), fn.val.subs σs k = fn.val) →
    (∀ j (_ : j < d) (hjσ : j < σ.length), LRelOf.Stable (σ[j]'hjσ)) →
    (∀ j (_ : j < d) (hjσ : j < σ.length) (hjσ' : j < σ'.length) (hjf : j < fns.length),
        ∀ {ε'' : Env} {a : MVal}, ε'.le ε'' → (σ[j]'hjσ).rel ε'' a →
        ∃ (w : MVal) (ε''' : Env), ((fns[j]'hjf).val.app a.val, ε'') ⇓ (w, ε''') ∧
          (σ'[j]'hjσ').rel ε''' w) →
    (∀ j (_ : d ≤ j) (hjσ : j < σ.length) (hjσ' : j < σ'.length),
        ∀ (ε₀ : Env) (w : MVal), (σ[j]'hjσ).rel ε₀ w → (σ'[j]'hjσ').rel ε₀ w) →
    (∀ j (hjσ' : j < σ'.length), LRelOf.Stable (σ'[j]'hjσ')) →
    Term.fmap (C.substAll ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))) Cs_t
        = Term.nlam Cs_t.length (Term.lam body) →
    x ∈ V⟦C⟧σ#ε' →
    body.subs (x.val :: fns.reverse.map Subtype.val) 0 ∈ T⟦C⟧σ'#ε' := by
  intro C
  induction C with
  | unit =>
      intro d σ σ' Ss_t Cs_t ε' fns x body hWf hd hσ'len hGin hGout hSClen hflen hdC hScl
        hCcl hSlive hClive hfrty hfnsT hfcl hstab hmap hsub hstabout hbody Vx
      simp only [Typ.substAll, Term.fmap] at hbody
      obtain rfl := Term.nlam_lam_inj hbody.symm
      simp only [Term.subs_var0]
      exact TRel.intro (Eval.value x.2) (VRel.type_closed Typ.Wf.unit Vx)
  | arr A1 A2 ih1 ih2 =>
      -- arrows map by post-composition; the mapped value is
      -- `λv. (fmap A2' fns…) (x v)`, its Kripke clause runs the input
      -- arrow's clause and then the structural IH at the codomain.
      intro d σ σ' Ss_t Cs_t ε' fns x body hWf hd hσ'len hGin hGout hSClen hflen hdC hScl
        hCcl hSlive hClive hfrty hfnsT hfcl hstab hmap hsub hstabout hbody Vx
      cases hWf with | arr WF1 WF2 =>
      have hσcl : σ.Closed := fun s hs => (hGin s hs).closed
      have hEs := Typ.rangeVar_drop_getElem?_Wf hσcl hdC
      have hC2F : (A2.substAll ((List.range d).map Typ.var
          ++ LRelSubs.types (σ.drop d))).Wf Cs_t.length := Typ.substAll_Wf WF2 hEs
      have hfnscl0 : ∀ (w : MVal),
          (fns.map Subtype.val).map (·.subs [w.val] 0) = fns.map Subtype.val := by
        intro w
        rw [List.map_map]
        apply List.map_congr_left
        intro fn hfn
        exact hfcl fn hfn [w.val] 0
      -- expose the fmap body (the post-composition lambda)
      simp only [Typ.substAll] at hbody
      rw [Term.fmap] at hbody
      obtain rfl := Term.nlam_lam_inj hbody.symm
      -- destructure the input arrow
      vrel at Vx
      obtain ⟨Tx, t, hxt, harr⟩ := Vx
      have hxval : x.val = Term.lam t := congrArg Subtype.val hxt
      have Tx' : ⊢{ε'} x.val ∷ A1 ⟶ A2.substAll σ.types := by
        have h := Tx
        simp only [Typ.substAll] at h
        rwa [Typ.substAll_closed WF1] at h
      have hxcl : ∀ (σs : Subs) (k : Nat), x.val.subs σs k = x.val :=
        fun σs k => HasType.closed Tx'
      -- compute the substituted body
      simp only [Term.subs, Nat.zero_add, Term.subs_apps, Term.fmap_subs hC2F hCcl,
        Term.fmap_fns_subs1 hflen, List.get_eq_getElem]
      simp only [dif_neg (Nat.lt_irrefl 1),
        dif_pos (show 1 - 1 < (x.val :: fns.reverse.map Subtype.val).length by simp),
        dif_pos (Nat.zero_lt_one), Nat.sub_self, List.getElem_cons_zero]
      obtain ⟨body2, hbody2⟩ := Term.fmap_nlam
        (A2.substAll ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))) Cs_t
      refine TRel.intro (Eval.value IsMValue.lam) ?_
      vrel
      refine ⟨?_, _, rfl, ?_⟩
      · -- typing conjunct
        have e : (A1 ⟶ A2).substAll σ'.types = A1 ⟶ A2.substAll σ'.types := by
          simp only [Typ.substAll]
          rw [Typ.substAll_closed WF1]
        rw [e]
        refine HasType.lam WF1 ?_
        have hgm := HasType.fmap_apps_coherent (B := A2) WF2 hC2F hd hσcl hσ'len hdC
          hSClen hScl hCcl hflen hClive hfrty hSlive hfnsT
        refine HasType.app' ?_ (HasType.weaken_closed hgm)
        exact HasType.app' (HasType.var rfl) (HasType.weaken_closed Tx')
      · -- Kripke clause: post-compose through the structural IH at A2
        intro ε'' S v1 V1
        have V1' : VRel A1 σ ε'' v1 := VRel.type_closed WF1 V1
        have Tt := harr ε'' S v1 V1'
        simp only [TRel] at Tt
        obtain ⟨y, εy, Ry, Vy⟩ := Tt
        have hIH := ih2 WF2 hd hσ'len hGin hGout hSClen hflen hdC hScl hCcl hSlive
          hClive hfrty
          (fun j hjS hjC hjf => (hfnsT j hjS hjC hjf).le' (S.trans Ry.incr)) hfcl
          hstab
          (fun j hj hjσ hjσ' hjf {ε₂} {a} S' R =>
            hmap j hj hjσ hjσ' hjf ((S.trans Ry.incr).trans S') R)
          hsub hstabout
          hbody2 Vy
        have Rxy : (x.val.app v1.val, ε'') ⇓ (y, εy) := by
          rw [hxval]
          exact Eval.app (Eval.value IsMValue.lam) (Eval.value v1.2) Ry
        have hcomp := TRel.fmap_apps_app hbody2 hflen hfcl Rxy hIH
        simp only [Term.sub, Term.subs, Term.subs_apps, Term.fmap_subs hC2F hCcl,
          hfnscl0, hxcl,
          dif_neg (Nat.lt_irrefl 0),
          dif_pos (show 0 - 0 < [v1.val].length by simp),
          Nat.sub_self, List.get_eq_getElem, List.getElem_cons_zero]
        exact hcomp
  | delayA B _ =>
      -- `□ B` is closed (`Typ.Wf`), so `fmap` is the identity `var 0`;
      -- the value is returned unchanged and its type is preserved because
      -- the type is closed.
      intro d σ σ' Ss_t Cs_t ε' fns x body hWf hd hσ'len hGin hGout hSClen hflen hdC hScl
        hCcl hSlive hClive hfrty hfnsT hfcl hstab hmap hsub hstabout hbody Vx
      have hFcl : (□ B).Closed := by cases hWf with | delayA h => exact .delayA h
      simp only [Typ.substAll_closed hFcl, Term.fmap] at hbody
      obtain rfl := Term.nlam_lam_inj hbody.symm
      simp only [Term.subs_var0]
      exact TRel.intro (Eval.value x.2) (VRel.type_closed hFcl Vx)
  | delayE B _ =>
      -- `◯ B` is closed, so `fmap` is the identity `var 0` (as for `□`).
      intro d σ σ' Ss_t Cs_t ε' fns x body hWf hd hσ'len hGin hGout hSClen hflen hdC hScl
        hCcl hSlive hClive hfrty hfnsT hfcl hstab hmap hsub hstabout hbody Vx
      have hFcl : (◯ B).Closed := by cases hWf with | delayE h => exact .delayE h
      simp only [Typ.substAll_closed hFcl, Term.fmap] at hbody
      obtain rfl := Term.nlam_lam_inj hbody.symm
      simp only [Term.subs_var0]
      exact TRel.intro (Eval.value x.2) (VRel.type_closed hFcl Vx)
  | chan B _ =>
      intro d σ σ' Ss_t Cs_t ε' fns x body hWf hd hσ'len hGin hGout hSClen hflen hdC hScl
        hCcl hSlive hClive hfrty hfnsT hfcl hstab hmap hsub hstabout hbody Vx
      have hFcl : (Typ.chan B).Closed := by cases hWf with | chan h => exact .chan h
      simp only [Typ.substAll_closed hFcl, Term.fmap] at hbody
      obtain rfl := Term.nlam_lam_inj hbody.symm
      simp only [Term.subs_var0]
      exact TRel.intro (Eval.value x.2) (VRel.type_closed hFcl Vx)
  | prod C1 C2 ih1 ih2 =>
      intro d σ σ' Ss_t Cs_t ε' fns x body hWf hd hσ'len hGin hGout hSClen hflen hdC hScl
        hCcl hSlive hClive hfrty hfnsT hfcl hstab hmap hsub hstabout hbody Vx
      cases hWf with | prod WF1 WF2 =>
      have WSin : LRelSubs.Kripke σ := fun s hs => (hGin s hs).wf
      have WSout : LRelSubs.Kripke σ' := fun s hs => (hGout s hs).wf
      have hσcl : σ.Closed := fun s hs => (hGin s hs).closed
      have hEs := Typ.rangeVar_drop_getElem?_Wf hσcl hdC
      have hC1F : (C1.substAll ((List.range d).map Typ.var
          ++ LRelSubs.types (σ.drop d))).Wf Cs_t.length := Typ.substAll_Wf WF1 hEs
      have hC2F : (C2.substAll ((List.range d).map Typ.var
          ++ LRelSubs.types (σ.drop d))).Wf Cs_t.length := Typ.substAll_Wf WF2 hEs
      simp only [Typ.substAll] at hbody
      rw [Term.fmap] at hbody
      obtain rfl := Term.nlam_lam_inj hbody.symm
      vrel at Vx
      obtain ⟨v1, v2, rfl, cv1, cv2⟩ := Vx
      simp only [Term.subs, Term.subs_apps, Term.fmap_subs hC1F hCcl,
        Term.fmap_subs hC2F hCcl, Term.fmap_fns_subs0 hflen]
      obtain ⟨body1, hbody1⟩ := Term.fmap_nlam
        (C1.substAll ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))) Cs_t
      obtain ⟨body2, hbody2⟩ := Term.fmap_nlam
        (C2.substAll ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))) Cs_t
      refine TRel.pair WSout ?_ ?_ (Env.refl ε')
      · intro ε'' Sub
        refine TRel.fmap_apps_app hbody1 hflen hfcl
          (Eval.pr1 (Eval.value (MVal.pair v1 v2).2)) ?_
        exact ih1 WF1 hd hσ'len hGin hGout hSClen hflen hdC hScl hCcl hSlive hClive hfrty
          (fun j hjS hjC hjf => (hfnsT j hjS hjC hjf).le' Sub) hfcl hstab
          (fun j hj hjσ hjσ' hjf {ε₂} {a} S' R => hmap j hj hjσ hjσ' hjf (Sub.trans S') R)
          hsub hstabout
          hbody1 (VRel.kripke WSin cv1 Sub)
      · intro ε'' Sub
        refine TRel.fmap_apps_app hbody2 hflen hfcl
          (Eval.pr2 (Eval.value (MVal.pair v1 v2).2)) ?_
        exact ih2 WF2 hd hσ'len hGin hGout hSClen hflen hdC hScl hCcl hSlive hClive hfrty
          (fun j hjS hjC hjf => (hfnsT j hjS hjC hjf).le' Sub) hfcl hstab
          (fun j hj hjσ hjσ' hjf {ε₂} {a} S' R => hmap j hj hjσ hjσ' hjf (Sub.trans S') R)
          hsub hstabout
          hbody2 (VRel.kripke WSin cv2 Sub)
  | sum C1 C2 ih1 ih2 =>
      intro d σ σ' Ss_t Cs_t ε' fns x body hWf hd hσ'len hGin hGout hSClen hflen hdC hScl
        hCcl hSlive hClive hfrty hfnsT hfcl hstab hmap hsub hstabout hbody Vx
      cases hWf with | sum WF1 WF2 =>
      have WSin : LRelSubs.Kripke σ := fun s hs => (hGin s hs).wf
      have hσcl : σ.Closed := fun s hs => (hGin s hs).closed
      have hEs := Typ.rangeVar_drop_getElem?_Wf hσcl hdC
      have hC1F : (C1.substAll ((List.range d).map Typ.var
          ++ LRelSubs.types (σ.drop d))).Wf Cs_t.length := Typ.substAll_Wf WF1 hEs
      have hC2F : (C2.substAll ((List.range d).map Typ.var
          ++ LRelSubs.types (σ.drop d))).Wf Cs_t.length := Typ.substAll_Wf WF2 hEs
      have hfnscl0 : ∀ (w : MVal),
          (fns.map Subtype.val).map (·.subs [w.val] 0) = fns.map Subtype.val := by
        intro w
        rw [List.map_map]
        apply List.map_congr_left
        intro fn hfn
        exact hfcl fn hfn [w.val] 0
      simp only [Typ.substAll] at hbody
      rw [Term.fmap] at hbody
      obtain rfl := Term.nlam_lam_inj hbody.symm
      obtain ⟨body1, hbody1⟩ := Term.fmap_nlam
        (C1.substAll ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))) Cs_t
      obtain ⟨body2, hbody2⟩ := Term.fmap_nlam
        (C2.substAll ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))) Cs_t
      vrel at Vx
      rcases Vx with ⟨v1, rfl, cv1⟩ | ⟨v2, rfl, cv2⟩
      · simp only [Term.subs, Nat.zero_add, Term.subs_apps, Term.fmap_subs hC1F hCcl,
          Term.fmap_subs hC2F hCcl, Term.fmap_fns_subs1 hflen]
        have hin1 : Term.in1 ((Term.apps (Term.fmap (C1.substAll ((List.range d).map Typ.var
              ++ LRelSubs.types (σ.drop d))) Cs_t) (fns.map Subtype.val)).app v1.val)
            ∈ T⟦C1 ⨁ C2⟧σ'#ε' := by
          refine TRel.fromTRel' (TRel.in1 ?_)
          intro ε'' Sub
          refine TRel.fmap_apps_app hbody1 hflen hfcl (Eval.value v1.2) ?_
          exact ih1 WF1 hd hσ'len hGin hGout hSClen hflen hdC hScl hCcl hSlive hClive hfrty
            (fun j hjS hjC hjf => (hfnsT j hjS hjC hjf).le' Sub) hfcl hstab
            (fun j hj hjσ hjσ' hjf {ε₂} {a} S' R => hmap j hj hjσ hjσ' hjf (Sub.trans S') R)
            hsub hstabout
            hbody1 (VRel.kripke WSin cv1 Sub)
        obtain ⟨u, εu, Ru, Vu⟩ := hin1.elim
        refine TRel.intro (Eval.case1 (Eval.value (MVal.in1 v1).2) ?_) Vu
        simpa only [Term.sub, Term.subs, Term.subs_apps, Term.fmap_subs hC1F hCcl, hfnscl0 v1,
          Term.subs_var0] using Ru
      · simp only [Term.subs, Nat.zero_add, Term.subs_apps, Term.fmap_subs hC1F hCcl,
          Term.fmap_subs hC2F hCcl, Term.fmap_fns_subs1 hflen]
        have hin2 : Term.in2 ((Term.apps (Term.fmap (C2.substAll ((List.range d).map Typ.var
              ++ LRelSubs.types (σ.drop d))) Cs_t) (fns.map Subtype.val)).app v2.val)
            ∈ T⟦C1 ⨁ C2⟧σ'#ε' := by
          refine TRel.fromTRel' (TRel.in2 ?_)
          intro ε'' Sub
          refine TRel.fmap_apps_app hbody2 hflen hfcl (Eval.value v2.2) ?_
          exact ih2 WF2 hd hσ'len hGin hGout hSClen hflen hdC hScl hCcl hSlive hClive hfrty
            (fun j hjS hjC hjf => (hfnsT j hjS hjC hjf).le' Sub) hfcl hstab
            (fun j hj hjσ hjσ' hjf {ε₂} {a} S' R => hmap j hj hjσ hjσ' hjf (Sub.trans S') R)
            hsub hstabout
            hbody2 (VRel.kripke WSin cv2 Sub)
        obtain ⟨u, εu, Ru, Vu⟩ := hin2.elim
        refine TRel.intro (Eval.case2 (Eval.value (MVal.in2 v2).2) ?_) Vu
        simpa only [Term.sub, Term.subs, Term.subs_apps, Term.fmap_subs hC2F hCcl, hfnscl0 v2,
          Term.subs_var0] using Ru
  | sig B0 ih =>
      intro d σ σ' Ss_t Cs_t ε' fns x body hWf hd hσ'len hGin hGout hSClen hflen hdC hScl
        hCcl hSlive hClive hfrty hfnsT hfcl hstab hmap hsub hstabout hbody Vx
      cases hWf with | sig WF =>
      have WSin : LRelSubs.Kripke σ := fun s hs => (hGin s hs).wf
      have WSout : LRelSubs.Kripke σ' := fun s hs => (hGout s hs).wf
      have hσcl : σ.Closed := fun s hs => (hGin s hs).closed
      have hσ'cl : σ'.Closed := fun s hs => (hGout s hs).closed
      have hEs := Typ.rangeVar_drop_getElem?_Wf hσcl hdC
      have hBF : (B0.substAll ((List.range d).map Typ.var
          ++ LRelSubs.types (σ.drop d))).Wf Cs_t.length := Typ.substAll_Wf WF hEs
      have hBoutWf : B0.Wf σ'.length := by rw [hσ'len]; exact WF
      have hann := Typ.fmap_out_coherence (B := B0) (Cs_t := Cs_t)
        WF hd hσcl hσ'len hdC hClive hfrty
      have hsrc := Typ.fmap_source_coherence (B := B0) (Ss_t := Ss_t)
        WF hd hσcl (by omega) hSlive
      simp only [Typ.substAll] at hbody
      rw [Term.fmap] at hbody
      obtain rfl := Term.nlam_lam_inj hbody.symm
      simp only [Term.smap_subs, Term.subs_apps, Term.fmap_subs hBF hCcl,
        Term.fmap_fns_subs0 hflen, Term.subs]
      obtain ⟨gbody, hgbody⟩ := Term.fmap_nlam
        (B0.substAll ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))) Cs_t
      rw [hann]
      have Tmfv : ⊢{ε'} Term.lam (gbody.subs (fns.reverse.map Subtype.val) 1)
          ∷ B0.substAll σ.types ⟶ B0.substAll σ'.types := by
        have hv := HasType.fmap_value_typed (Ss := Ss_t) hBF hSClen hScl hCcl hgbody hflen hfnsT
        rw [← hsrc, ← hann]
        exact hv
      refine VRel.smap_full (A := B0) (B := B0) (ρin := σ) (ρout := σ')
        (mfv := ⟨Term.lam (gbody.subs (fns.reverse.map Subtype.val) 1), IsMValue.lam⟩)
        WSin WSout hσcl hσ'cl WF hBoutWf ?_ Tmfv ?_ Vx
      · intro ε'' _
        have hgeq : Term.fmap (B0.substAll ((List.range d).map Typ.var
            ++ LRelSubs.types (σ.drop d))) Cs_t = Term.nlam fns.length (Term.lam gbody) := by
          rw [hgbody, ← hflen]
        exact Eval.apps_nlam hfcl (by rw [hgeq]; exact Eval.value IsMValue.nlam_lam)
      · intro ε'' t y S Rt hy
        have hσs : ∀ g ∈ fns.reverse.map Subtype.val, ∀ (σs : Subs) (k : Nat),
            g.subs σs k = g := by
          intro g hg' σs k
          simp only [List.mem_map, List.mem_reverse] at hg'
          obtain ⟨fn, hfn, rfl⟩ := hg'
          exact hfcl fn hfn σs k
        have hih := ih WF hd hσ'len hGin hGout hSClen hflen hdC hScl hCcl hSlive hClive hfrty
          (fun j hjS hjC hjf => (hfnsT j hjS hjC hjf).le' S) hfcl hstab
          (fun j hj hjσ hjσ' hjf {ε₂} {a} S' R => hmap j hj hjσ hjσ' hjf (S.trans S') R)
          hsub hstabout
          hgbody hy
        obtain ⟨w, εw, Rw, Vw⟩ := hih.elim
        refine TRel.intro (Eval.app (Eval.value IsMValue.lam) Rt ?_) Vw
        rw [show (gbody.subs (fns.reverse.map Subtype.val) 1).sub y.val
              = gbody.subs (y.val :: fns.reverse.map Subtype.val) 0 from by
            simp only [Term.sub]; rw [Term.subs_subs_closed hσs]]
        exact Rw
  | var i =>
      intro d σ σ' Ss_t Cs_t ε' fns x body hWf hd hσ'len hGin hGout hSClen hflen hdC hScl
        hCcl hSlive hClive hfrty hfnsT hfcl hstab hmap hsub hstabout hbody Vx
      cases hWf with | var hi =>
      have hiσ' : i < σ'.length := by omega
      vrel at Vx
      obtain ⟨s, hs, Tx, R⟩ := Vx
      have hsi : s = σ[i]'hi := by
        rw [List.getElem?_eq_getElem hi] at hs
        exact (Option.some.inj hs).symm
      subst hsi
      by_cases hid : i < d
      · -- MAPPED leaf: entry-to-entry through the function
        have hEi : (Typ.var i).substAll ((List.range d).map Typ.var
            ++ LRelSubs.types (σ.drop d)) = Typ.var i := by
          simp only [Typ.substAll, List.getD_eq_getElem?_getD, Typ.getElem?_rangeVar_append,
            if_pos hid, Option.getD_some]
        rw [hEi] at hbody
        have hiC : i < Cs_t.length := by omega
        simp only [Term.fmap] at hbody
        rw [if_pos hiC] at hbody
        obtain rfl := Term.nlam_lam_inj hbody.symm
        rw [show ((Term.var (Cs_t.length - i)).app (Term.var 0)).subs
              (x.val :: fns.reverse.map Subtype.val) 0
              = (fns[i]'(by omega)).val.app x.val from by
            show ((Term.var (Cs_t.length - i)).subs (x.val :: fns.reverse.map Subtype.val) 0).app
                ((Term.var 0).subs (x.val :: fns.reverse.map Subtype.val) 0) = _
            rw [Term.subs_var_fns0 hflen hiC, Term.subs_var0]]
        obtain ⟨w, ε''', Rw, Rel'⟩ := hmap i hid hi hiσ' (by omega) (Env.refl ε') R
        refine TRel.intro Rw ?_
        vrel
        exact ⟨σ'[i]'hiσ', List.getElem?_eq_getElem hiσ',
          (hGout _ (List.getElem_mem hiσ')).hasType Rel', Rel'⟩
      · -- FROZEN leaf: rebuild through the entry's evidence
        have hEi : (Typ.var i).substAll ((List.range d).map Typ.var
            ++ LRelSubs.types (σ.drop d)) = (σ[i]'hi).type := by
          simp only [Typ.substAll, List.getD_eq_getElem?_getD, Typ.getElem?_rangeVar_append,
            if_neg hid]
          simp only [LRelSubs.types, List.getElem?_map, List.getElem?_drop,
            show d + (i - d) = i from by omega, List.getElem?_eq_getElem hi, Option.map_some,
            Option.getD_some]
        rw [hEi] at hbody
        obtain ⟨w', ε₁, Rw', Rel'⟩ := ((hstabout i hiσ').mono_left
          ((hfrty i (by omega) hi hiσ').symm) (hsub i (by omega) hi hiσ')).2
          hSClen hflen hScl hCcl hfnsT hfcl R hbody
        refine TRel.intro Rw' ?_
        vrel
        exact ⟨σ'[i]'hiσ', List.getElem?_eq_getElem hiσ',
          (hGout _ (List.getElem_mem hiσ')).hasType Rel', Rel'⟩
  | mu C0 ih =>
      -- Park induction (`LRel.lfp.strong_induction`) over the mixed
      -- environment σM (σ-entries at mapped positions, σ'-entries at
      -- frozen ones — all Good and Stable) with the descendant-closed
      -- Kripke predicate "every rebuild descendant maps into the target
      -- µ-relation over σ'".  Per descendant, the recur evaluation runs
      -- one fmap₁ step into the conjunctive pair entry ⟨meet, target⟩
      -- (an `ih` instance at d := 1) and one layer through `pr2` (an
      -- `ih` instance at d := d+1, original maps intact because σM
      -- keeps the σ-entries at mapped positions), then folds into σ'.
      -- The descendant dimension is grounded by the generalized rebuild
      -- lemmas (`VRel.mu_fmap_rebuild_land`/`VRel.mu_fmap_stable`),
      -- which take the structural IH as a hypothesis.
      intro d σ σ' Ss_t Cs_t ε' fns x body hWf hd hσ'len hGin hGout hSClen hflen hdC hScl
        hCcl hSlive hClive hfrty hfnsT hfcl hstab hmap hsub hstabout hbody Vx
      cases hWf with | mu WF =>
      have ihM : VRel.FmapMappedIH C0 := ih
      -- ── environment facts ───────────────────────────────────────────
      have hσcl : σ.Closed := fun s hs => (hGin s hs).closed
      have WSout : LRelSubs.Kripke σ' := fun s hs => (hGout s hs).wf
      -- ── the mixed environment ───────────────────────────────────────
      set σM : LRelSubs := σ.take d ++ σ'.drop d with hσMdef
      have hσMlen : σM.length = σ.length := by
        simp only [hσMdef, List.length_append, List.length_take, List.length_drop, hσ'len]
        omega
      have hσMget?_lt : ∀ j, j < d → σM[j]? = σ[j]? := by
        intro j hjd
        rw [hσMdef, List.getElem?_append_left
              (by simp only [List.length_take]; omega : j < (σ.take d).length),
            List.getElem?_take, if_pos hjd]
      have hσMget?_ge : ∀ j, d ≤ j → σM[j]? = σ'[j]? := by
        intro j hjd
        rw [hσMdef, List.getElem?_append_right
              (by simp only [List.length_take]; omega : (σ.take d).length ≤ j),
            List.getElem?_drop]
        congr 1
        simp only [List.length_take]
        omega
      have hσMget_lt : ∀ j (hjd : j < d) (hj : j < σM.length) (hjσ : j < σ.length),
          σM[j]'hj = σ[j]'hjσ := by
        intro j hjd hj hjσ
        have h := hσMget?_lt j hjd
        rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjσ] at h
        exact Option.some.inj h
      have hσMget_ge : ∀ j (hjd : d ≤ j) (hj : j < σM.length) (hjσ' : j < σ'.length),
          σM[j]'hj = σ'[j]'hjσ' := by
        intro j hjd hj hjσ'
        have h := hσMget?_ge j hjd
        rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjσ'] at h
        exact Option.some.inj h
      have hGM : ∀ s ∈ σM, LRelOf.Good s := by
        intro s hs
        rw [hσMdef] at hs
        rcases List.mem_append.mp hs with hs | hs
        · exact hGin s (List.mem_of_mem_take hs)
        · exact hGout s (List.drop_subset _ _ hs)
      have hstM : ∀ j (hj : j < σM.length), LRelOf.Stable (σM[j]'hj) := by
        intro j hj
        by_cases hjd : j < d
        · rw [hσMget_lt j hjd hj (by omega)]
          exact hstab j hjd (by omega)
        · rw [hσMget_ge j (by omega) hj (by omega)]
          exact hstabout j (by omega)
      have hσMcl : σM.Closed := fun s hs => (hGM s hs).closed
      have WSM : LRelSubs.Kripke σM := fun s hs => (hGM s hs).wf
      have hσMtypes : LRelSubs.types σM = LRelSubs.types σ := by
        apply List.ext_getElem
        · simp only [LRelSubs.types_length, hσMlen]
        · intro i h1 h2
          simp only [LRelSubs.types_length] at h1 h2
          simp only [LRelSubs.types, List.getElem_map]
          by_cases hid : i < d
          · rw [hσMget_lt i hid h1 h2]
          · rw [hσMget_ge i (by omega) h1 (by omega)]
            exact hfrty i (by omega) h2 (by omega)
      have hdrop_types : LRelSubs.types (σM.drop d) = LRelSubs.types (σ.drop d) := by
        show (σM.drop d).map (·.type) = (σ.drop d).map (·.type)
        rw [List.map_drop, List.map_drop]
        exact congrArg (List.drop d) hσMtypes
      have WFM : C0.Wf (σM.length + 1) := by rw [hσMlen]; exact WF
      have WF' : C0.Wf (σ'.length + 1) := by rw [hσ'len]; exact WF
      -- ── the term shape ──────────────────────────────────────────────
      have hdropcl : ∀ E ∈ LRelSubs.types (σ.drop d), E.Closed := by
        intro E hE
        simp only [LRelSubs.types, List.mem_map] at hE
        obtain ⟨u, hu, rfl⟩ := hE
        exact (hGin u (List.drop_subset _ _ hu)).closed
      have hEs1 : (Typ.var 0 :: ((List.range d).map Typ.var
            ++ LRelSubs.types (σ.drop d)).map (Typ.shift 0) : List Typ)
          = (List.range (d+1)).map Typ.var ++ LRelSubs.types (σ.drop d) := by
        rw [List.map_append, map_shift_closed hdropcl]
        rw [show ((List.range d).map Typ.var).map (Typ.shift 0)
              = (List.range' 1 d).map Typ.var from by
            rw [List.range_eq_range', Typ.range'_var_shift]]
        rw [show ((List.range (d+1)).map Typ.var : List Typ)
              = Typ.var 0 :: (List.range' 1 d).map Typ.var from by
            rw [List.range_eq_range', List.range'_succ, List.map_cons]]
        rfl
      simp only [Typ.substAll] at hbody
      rw [hEs1] at hbody
      simp only [Term.fmap] at hbody
      rw [map_shift_closed hCcl] at hbody
      obtain rfl := Term.nlam_lam_inj hbody.symm
      -- ── well-formedness / closedness of the pieces ──────────────────
      have hA'cWf1 : (C0.substAll ((List.range (d+1)).map Typ.var
          ++ LRelSubs.types (σ.drop d))).Wf (Cs_t.length + 1) := by
        refine Typ.substAll_Wf WF ?_
        intro i hi
        by_cases hid : i < d + 1
        · exact ⟨Typ.var i, by rw [Typ.getElem?_rangeVar_append, if_pos hid],
            Typ.Wf.var (by omega)⟩
        · refine ⟨(σ[i - 1]'(by omega)).type, ?_,
            ((hGin _ (List.getElem_mem _)).closed).mono (Nat.zero_le _)⟩
          rw [Typ.getElem?_rangeVar_append, if_neg hid]
          simp only [LRelSubs.types, List.getElem?_map, List.getElem?_drop]
          rw [show d + (i - (d + 1)) = i - 1 from by omega,
              List.getElem?_eq_getElem (show i - 1 < σ.length by omega), Option.map_some]
      have hMtwf : ((C0.substAll ((List.range (d+1)).map Typ.var
          ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)).Wf 1 := by
        refine Typ.substAll_Wf hA'cWf1 ?_
        intro i hi
        rcases i with _ | k
        · exact ⟨Typ.var 0, rfl, Typ.Wf.var (by omega)⟩
        · refine ⟨Cs_t[k]'(by omega), ?_, (hCcl _ (List.getElem_mem _)).mono (Nat.zero_le _)⟩
          simp only [List.getElem?_cons_succ]
          exact List.getElem?_eq_getElem (by omega)
      have hLBLMwf : (C0.substAll (Typ.var 0 :: LRelSubs.types σM)).Wf 1 := by
        refine Typ.substAll_Wf WFM ?_
        intro i hi
        rcases i with _ | k
        · exact ⟨Typ.var 0, rfl, Typ.Wf.var (by omega)⟩
        · refine ⟨(σM[k]'(by omega)).type, ?_,
            ((hGM _ (List.getElem_mem _)).closed).mono (Nat.zero_le _)⟩
          simp only [List.getElem?_cons_succ, LRelSubs.types, List.getElem?_map]
          rw [List.getElem?_eq_getElem (show k < σM.length by omega), Option.map_some]
      have hμMtcl : (μ ((C0.substAll ((List.range (d+1)).map Typ.var
          ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))).Closed := Typ.Wf.mu hMtwf
      have hμLBLMcl : (μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))).Closed :=
        Typ.Wf.mu hLBLMwf
      have hPcl : (μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
          ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
              ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))).Closed :=
        Typ.Wf.prod hμLBLMcl hμMtcl
      have hCc2 : ∀ C ∈ (μ ((C0.substAll ((List.range (d+1)).map Typ.var
          ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t, C.Closed := by
        intro C hC
        headTail hC
        · exact hμMtcl
        · exact hCcl C hC
      have hA'cWfM : (C0.substAll ((List.range (d+1)).map Typ.var
          ++ LRelSubs.types (σ.drop d))).Wf ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
            ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t).length := by
        simpa using hA'cWf1
      -- ── push the outer substitution through the recur body ──────────
      simp only [Term.subs, Term.subs_apps, List.map_cons, Term.fmap_subs hA'cWfM hCc2,
        Term.fmap_fns_subs1 hflen, Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd, reduceDIte,
        List.get_eq_getElem, List.getElem_cons_zero]
      -- ── coherence facts ─────────────────────────────────────────────
      have hmuEtyM : (μ C0).substAll (LRelSubs.types σM)
          = μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM)) := by
        simp only [Typ.substAll]
        rw [map_shift_closed hσMcl.types]
      have hMtmu : (μ (C0.substAll ((List.range (d+1)).map Typ.var
            ++ LRelSubs.types (σ.drop d)))).substAll Cs_t
          = (μ C0).substAll (LRelSubs.types σ') := by
        have h := Typ.fmap_out_coherence (B := μ C0) (Cs_t := Cs_t)
          (Typ.Wf.mu WF) hd hσcl hσ'len hdC hClive hfrty
        rw [show (μ C0).substAll ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))
              = μ (C0.substAll ((List.range (d+1)).map Typ.var ++ LRelSubs.types (σ.drop d)))
            from by simp only [Typ.substAll]; rw [hEs1]] at h
        exact h
      have hMtout : (μ C0).substAll (LRelSubs.types σ')
          = μ ((C0.substAll ((List.range (d+1)).map Typ.var
              ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)) := by
        rw [← hMtmu]
        simp only [Typ.substAll]
        rw [map_shift_closed hCcl]
      have hMtl : (C0.substAll ((List.range (d+1)).map Typ.var
            ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)
          = C0.substAll (Typ.var 0 :: (LRelSubs.types σ').map (Typ.shift 0)) := by
        have h := hMtmu
        simp only [Typ.substAll] at h
        rw [map_shift_closed hCcl] at h
        exact Typ.mu.inj h
      have hsrcmu : (C0.substAll ((List.range (d+1)).map Typ.var
            ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Ss_t)
          = C0.substAll (Typ.var 0 :: LRelSubs.types σ) := by
        have h := Typ.fmap_source_coherence (B := μ C0) (Ss_t := Ss_t)
          (Typ.Wf.mu WF) hd hσcl (by omega) hSlive
        rw [show (μ C0).substAll ((List.range d).map Typ.var ++ LRelSubs.types (σ.drop d))
              = μ (C0.substAll ((List.range (d+1)).map Typ.var ++ LRelSubs.types (σ.drop d)))
            from by simp only [Typ.substAll]; rw [hEs1]] at h
        simp only [Typ.substAll] at h
        rw [map_shift_closed hScl, map_shift_closed hσcl.types] at h
        exact Typ.mu.inj h
      have hsubP : (C0.substAll ((List.range (d+1)).map Typ.var
            ++ LRelSubs.types (σ.drop d))).substAll
              ((μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
                ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Ss_t)
          = (C0.substAll (Typ.var 0 :: LRelSubs.types σM)).sub
              (μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
                ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) := by
        rw [show ((μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
              ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                  ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Ss_t : List Typ)
            = (Typ.var 0 :: Ss_t).map (·.substAll
                [μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
                  ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                      ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))]) from by
            simp only [List.map_cons]
            rw [map_substAll_closed hScl]
            congr 1]
        rw [← Typ.substAll_substAll
              (A := C0.substAll ((List.range (d+1)).map Typ.var ++ LRelSubs.types (σ.drop d)))
              (Cs := Typ.var 0 :: Ss_t)
              (by rw [List.length_cons, hSClen]; exact hA'cWf1),
            hsrcmu, hσMtypes.symm]
        exact Typ.substAll_singleton hLBLMwf _
      have hsubMt : (C0.substAll ((List.range (d+1)).map Typ.var
            ++ LRelSubs.types (σ.drop d))).substAll
              ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                  ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t)
          = ((C0.substAll ((List.range (d+1)).map Typ.var
              ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)).sub
                (μ ((C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) := by
        rw [show ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t : List Typ)
            = (Typ.var 0 :: Cs_t).map (·.substAll
                [μ ((C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))]) from by
            simp only [List.map_cons]
            rw [map_substAll_closed hCcl]
            congr 1]
        rw [← Typ.substAll_substAll
              (A := C0.substAll ((List.range (d+1)).map Typ.var ++ LRelSubs.types (σ.drop d)))
              (Cs := Typ.var 0 :: Cs_t)
              (by rw [List.length_cons]; exact hA'cWf1)]
        exact Typ.substAll_singleton hMtwf _
      -- ── Good/Stable µ-entries (via the rebuild Park) ────────────────
      have hStM : LRelOf.Stable (LRelOf.mu C0 σM) := VRel.mu_fmap_stable ihM WFM hGM hstM
      have hStTgt : LRelOf.Stable (LRelOf.mu C0 σ') :=
        VRel.mu_fmap_stable ihM WF' hGout hstabout
      have hGTgt : LRelOf.Good (LRelOf.mu C0 σ') := by
        rw [LRelOf.mu_eq_cap]
        exact LRelOf.Good.cap (Typ.Wf.mu WF') hGout
      -- ── typing of the step term and the pairing realiser ────────────
      have Ts : ∀ {εY : Env}, ε'.le εY →
          [(C0.substAll (Typ.var 0 :: LRelSubs.types σM)).sub
              (μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
                ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)))] ⊢{εY}
            Term.cons ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))
              (((Term.fmap (C0.substAll ((List.range (d+1)).map Typ.var
                  ++ LRelSubs.types (σ.drop d)))
                  ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                      ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t)).apps
                ((Term.var 0).pr2.lam :: fns.map Subtype.val)).app (Term.var 0))
            ∷ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)) := by
        intro εY SY
        apply HasType.cons hμMtcl
        rw [← hsubMt]
        refine HasType.app' ?_ (HasType.apps (HasType.fmap
            (Ss := (μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
              ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                  ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Ss_t)
            hA'cWfM
            (by simp only [List.length_cons, hSClen]) ?_ hCc2)
          (by simp only [List.length_cons, hSClen])
          (by simp only [List.length_cons, List.length_map, hflen]) ?_)
        · rw [← hsubP]
          exact HasType.var rfl
        · intro S hS
          headTail hS
          · exact hPcl
          · exact hScl S hS
        · intro i hiS hiC hif
          cases i with
          | zero =>
              simp only [List.getElem_cons_zero]
              exact HasType.lam hPcl (HasType.pr2 (HasType.var rfl))
          | succ j =>
              simp only [List.getElem_cons_succ, List.getElem_map]
              have hjS : j < Ss_t.length := by
                simp only [List.length_cons] at hiS; omega
              have hjC : j < Cs_t.length := by
                simp only [List.length_cons] at hiC; omega
              have hjf : j < fns.length := by
                simp only [List.length_cons, List.length_map] at hif; omega
              have hwk := HasType.weaken
                (Γ' := [(C0.substAll (Typ.var 0 :: LRelSubs.types σM)).sub
                  (μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
                    ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                        ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)))])
                ((hfnsT j hjS hjC hjf).le' SY)
              simpa only [List.nil_append] using hwk
      have Tpairfn : ∀ {εY : Env}, ε'.le εY →
          ⊢{εY} Term.lam (Term.pair (Term.var 0)
            (Term.recur (μ ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)))
              (Term.cons ((C0.substAll ((List.range (d+1)).map Typ.var
                  ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))
                (((Term.fmap (C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d)))
                    ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                        ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t)).apps
                  ((Term.var 0).pr2.lam :: fns.map Subtype.val)).app (Term.var 0)))
              (Term.var 0)))
            ∷ μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
              ⟶ (μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
                  ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                      ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) := by
        intro εY SY
        apply HasType.lam hμLBLMcl
        apply HasType.pair
        · exact HasType.var rfl
        · exact HasType.recur hμLBLMcl hμMtcl
            (HasType.weaken (Γ' := [μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))]) (Ts SY))
            (HasType.var rfl)
      -- ── the descendant-closed Kripke Park predicate ─────────────────
      have hmono : LRel.Mono (VRel.muOper C0 σM) := VRel.muOper_mono WFM
      set X : LRel := fun ε₂ v => ∀ ε₃, ε₂.le ε₃ → ∀ (ε₄ : Env) (v₄ : MVal),
        RebStar ((μ C0).substAll (LRelSubs.types σM)) ε₃ v ε₄ v₄ → ε'.le ε₄ →
        Term.recur (μ ((C0.substAll ((List.range (d+1)).map Typ.var
            ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)))
          (Term.cons ((C0.substAll ((List.range (d+1)).map Typ.var
              ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))
            (((Term.fmap (C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d)))
                ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t)).apps
              ((Term.var 0).pr2.lam :: fns.map Subtype.val)).app (Term.var 0)))
          v₄.val ∈ T⟦μ C0⟧σ'#ε₄ with hX
      have hXwf : LRel.Kripke X := by
        intro ε₁ ε₂ v S hv ε₃ S23 ε₄ v₄ hstar Sε₄
        exact hv ε₃ (S.trans S23) ε₄ v₄ hstar Sε₄
      -- ── the Park-meet entry: Good and Stable ────────────────────────
      set eP : LRelOf := ⟨(μ C0).substAll (LRelSubs.types σM),
        fun ε₂ w => LRel.lfp (VRel.muOper C0 σM) ε₂ w ∧ X ε₂ w⟩ with heP
      have hePty : eP.type = (μ C0).substAll (LRelSubs.types σM) := rfl
      have hGeP : LRelOf.Good eP := by
        refine ⟨?_, ?_, ?_⟩
        · exact Typ.substAll_Wf_closed (by simpa using Typ.Wf.mu WFM) hσMcl.types
        · intro v ε₁ ε₂ S hv
          exact ⟨LRel.lfp.kripke _ _ _ S hv.1, hXwf _ _ _ S hv.2⟩
        · intro ε₁ w hw
          have h1 := hw.1
          rw [← VRel.mu_def] at h1
          exact VRel.HasType_open hσMcl (Typ.Wf.mu WFM) h1
      have hSteP : LRelOf.Stable eP := by
        refine ⟨rfl, ?_⟩
        intro Ss' Cs' fns' ε₀ w body'' h1 h2 h3 h4 h5 h6 hw hbody''
        have hwmu : (LRelOf.mu C0 σM).rel ε₀ w := by
          simp only [LRelOf.mu_rel]
          rw [VRel.mu_def]
          exact hw.1
        obtain ⟨w', ε₁, R, V⟩ := hStM.2 h1 h2 h3 h4 h5 h6 hwmu hbody''
        refine ⟨w', ε₁, R, ?_, ?_⟩
        · have hV := V
          simp only [LRelOf.mu_rel] at hV
          rw [VRel.mu_def] at hV
          exact hV
        · have hstep1 : RebStep ((μ C0).substAll (LRelSubs.types σM)) ε₀ w ε₁ w' :=
            ⟨Ss', Cs', fns', body'', h1, h2, h3, h4, h5, h6, hbody'', R⟩
          intro ε₃' S₁₃' ε₄' v₄' hstar' Sε₄'
          exact hw.2 ε₀ (Env.refl ε₀) ε₄' v₄'
            (RebStar.trans (RebStar.weak (RebStar.single hstep1) S₁₃') hstar') Sε₄'
      have WSP : LRelSubs.Kripke (eP :: σM) := by
        intro u hu
        headTail hu
        · exact hGeP.wf
        · exact WSM u hu
      have hGpairPT : LRelOf.Good (LRelOf.pairE eP (LRelOf.mu C0 σ')) :=
        LRelOf.Good.pairE hGeP hGTgt
      have hStpairPT : LRelOf.Stable (LRelOf.pairE eP (LRelOf.mu C0 σ')) :=
        LRelOf.Stable.pairE hGeP hGTgt hSteP hStTgt
      -- ── the key: every fixed-point member satisfies the predicate ───
      have key : ∀ {ε₂ : Env} {v : MVal}, VRel (μ C0) σM ε₂ v → X ε₂ v := by
        intro ε₂ v hv
        rw [VRel.mu_def] at hv
        refine LRel.lfp.strong_induction hmono hXwf ?_ ε₂ v hv
        intro ε₂' a ha
        obtain ⟨a', hcons, Ha'⟩ := ha
        rw [show C0.substAll (Typ.var 0 :: (LRelSubs.types σM).map (Typ.shift 0))
              = C0.substAll (Typ.var 0 :: LRelSubs.types σM) from by
            rw [map_shift_closed hσMcl.types]] at hcons
        subst hcons
        intro ε₃ S23 ε₄ v₄ hstar Sε₄
        -- descend the rebuild chain: every descendant is a fold over the meet
        have descend : ∀ {εa εb : Env} {va vb : MVal},
            RebStar ((μ C0).substAll (LRelSubs.types σM)) εa va εb vb →
            ∀ {u : MVal}, va = MVal.cons (C0.substAll (Typ.var 0 :: LRelSubs.types σM)) u →
            VRel C0 (eP :: σM) εa u →
            ∃ u₄, vb = MVal.cons (C0.substAll (Typ.var 0 :: LRelSubs.types σM)) u₄ ∧
              VRel C0 (eP :: σM) εb u₄ := by
          intro εa εb va vb h
          induction h with
          | refl =>
              intro u hva Hu
              exact ⟨u, hva, Hu⟩
          | weak hst S ihd =>
              intro u hva Hu
              obtain ⟨u₄, rfl, Hu₄⟩ := ihd hva Hu
              exact ⟨u₄, rfl, VRel.kripke WSP Hu₄ S⟩
          | tail hst hstep ihd =>
              intro u hva Hu
              obtain ⟨u₄, rfl, Hu₄⟩ := ihd hva Hu
              exact VRel.mu_fmap_rebuild_land ihM WFM hGM hstM rfl hGeP hSteP Hu₄ hstep
        obtain ⟨u₄, rfl, Hu₄⟩ := descend hstar rfl (VRel.kripke WSP Ha' S23)
        -- ── the fmap₁ step: an `ih` instance over `eP :: σM`, head mapped
        --    into the conjunctive pair entry ⟨meet, target⟩ ─────────────
        obtain ⟨bodyf, hbodyf⟩ := Term.fmap_nlam (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
          [μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
            ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))]
        have hbodyf' : Term.fmap (C0.substAll ((List.range 1).map Typ.var
              ++ LRelSubs.types ((eP :: σM : LRelSubs).drop 1)))
              [μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
                ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))]
            = Term.nlam ([μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
                ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))] : List Typ).length
                (Term.lam bodyf) := by
          rw [show C0.substAll ((List.range 1).map Typ.var
                ++ LRelSubs.types ((eP :: σM : LRelSubs).drop 1))
              = C0.substAll (Typ.var 0 :: LRelSubs.types σM) from by
            simp only [List.range_one, List.map_cons, List.map_nil, List.singleton_append,
              List.drop_succ_cons, List.drop_zero]]
          exact hbodyf
        have hstep_m := ihM (d := 1) (σ := eP :: σM)
          (σ' := LRelOf.pairE eP (LRelOf.mu C0 σ') :: σM)
          (Ss_t := [μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))])
          (Cs_t := [μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
            ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))])
          (fns := [⟨Term.lam (Term.pair (Term.var 0)
            (Term.recur (μ ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)))
              (Term.cons ((C0.substAll ((List.range (d+1)).map Typ.var
                  ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))
                (((Term.fmap (C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d)))
                    ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                        ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t)).apps
                  ((Term.var 0).pr2.lam :: fns.map Subtype.val)).app (Term.var 0)))
              (Term.var 0))), IsMValue.lam⟩])
          (by simpa using WFM) (by simp) (by simp)
          (fun u hu => by
            headTail hu
            · exact hGeP
            · exact hGM u hu)
          (fun u hu => by
            headTail hu
            · exact hGpairPT
            · exact hGM u hu)
          rfl rfl (by simp)
          (fun S hS => by rw [List.mem_singleton] at hS; subst hS; exact hμLBLMcl)
          (fun T hT => by rw [List.mem_singleton] at hT; subst hT; exact hPcl)
          (fun j hjl hjS hjσ => by
            obtain rfl : j = 0 := by omega
            simp only [List.getElem_cons_zero]
            exact hmuEtyM.symm)
          (fun j hjl hjC hjσ' => by
            obtain rfl : j = 0 := by omega
            simp only [List.getElem_cons_zero, LRelOf.pairE_type, LRelOf.mu_type]
            rw [hePty, hmuEtyM, hMtout])
          (fun j hj hjσ hjσ' => by
            cases j with
            | zero => omega
            | succ k => simp only [List.getElem_cons_succ])
          (fun j hjS hjC hjf => by
            obtain rfl : j = 0 := by
              simp only [List.length_singleton] at hjS
              omega
            simpa only [List.getElem_cons_zero] using Tpairfn Sε₄)
          (fun fn hfn σs k => by
            rw [List.mem_singleton] at hfn
            subst hfn
            exact HasType.closed (Tpairfn Sε₄))
          (fun j hjl hjσ => by
            obtain rfl : j = 0 := by omega
            simpa only [List.getElem_cons_zero] using hSteP)
          (fun j hjl hjσ hjσ' hjf {εa} {a} Sa Ra => by
            obtain rfl : j = 0 := by omega
            simp only [List.getElem_cons_zero] at Ra ⊢
            -- the recursive map: the Park conjunct at the refl descendant
            have hrec := Ra.2 εa (Env.refl εa) εa a RebStar.refl (Sε₄.trans Sa)
            obtain ⟨b, εb, Rb, Vb⟩ := hrec.elim
            have hfnscl1 : (fns.map Subtype.val).map (·.subs [a.val] 1)
                = fns.map Subtype.val := by
              rw [List.map_map]
              apply List.map_congr_left
              intro fn hfn
              exact hfcl fn hfn [a.val] 1
            refine ⟨MVal.pair a b, εb, ?_, ?_⟩
            · refine Eval.app (Eval.value IsMValue.lam) (Eval.value a.2) ?_
              rw [show (Term.pair (Term.var 0)
                    (Term.recur (μ ((C0.substAll ((List.range (d+1)).map Typ.var
                        ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)))
                      (Term.cons ((C0.substAll ((List.range (d+1)).map Typ.var
                          ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))
                        (((Term.fmap (C0.substAll ((List.range (d+1)).map Typ.var
                            ++ LRelSubs.types (σ.drop d)))
                            ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                                ++ LRelSubs.types (σ.drop d))).substAll
                                  (Typ.var 0 :: Cs_t))) :: Cs_t)).apps
                          ((Term.var 0).pr2.lam :: fns.map Subtype.val)).app (Term.var 0)))
                      (Term.var 0))).sub a.val
                  = Term.pair a.val
                    (Term.recur (μ ((C0.substAll ((List.range (d+1)).map Typ.var
                        ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)))
                      (Term.cons ((C0.substAll ((List.range (d+1)).map Typ.var
                          ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))
                        (((Term.fmap (C0.substAll ((List.range (d+1)).map Typ.var
                            ++ LRelSubs.types (σ.drop d)))
                            ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                                ++ LRelSubs.types (σ.drop d))).substAll
                                  (Typ.var 0 :: Cs_t))) :: Cs_t)).apps
                          ((Term.var 0).pr2.lam :: fns.map Subtype.val)).app (Term.var 0)))
                      a.val) from by
                simp only [Term.sub, Term.subs, Term.subs_apps, List.map_cons,
                  Term.fmap_subs hA'cWfM hCc2, hfnscl1, Nat.reduceLT, Nat.reduceSub,
                  Nat.reduceAdd, reduceDIte, List.get_eq_getElem, List.getElem_cons_zero,
                  List.length_cons, List.length_nil]]
              exact Eval.pair (Eval.value a.2) Rb
            · simp only [LRelOf.pairE_rel]
              refine ⟨a, b, rfl, ?_, ?_⟩
              · exact hGeP.wf εa εb a Rb.incr Ra
              · simpa only [LRelOf.mu_rel] using Vb)
          (fun j hj hjσ hjσ' => by
            cases j with
            | zero => omega
            | succ k =>
                intro ε₀ w hw
                simpa only [List.getElem_cons_succ] using hw)
          (fun j hjσ' => by
            cases j with
            | zero => simpa only [List.getElem_cons_zero] using hStpairPT
            | succ k =>
                simp only [List.length_cons] at hjσ'
                simpa only [List.getElem_cons_succ] using hstM k (by omega))
          hbodyf' Hu₄
        obtain ⟨w, εw, R2, Hw⟩ := (TRel.fmap_apps_app hbodyf rfl
          (fun fn hfn σs k => by
            rw [List.mem_singleton] at hfn
            subst hfn
            exact HasType.closed (Tpairfn Sε₄))
          (Eval.value u₄.2) hstep_m).elim
        -- ── the layer: an `ih` instance over the pair entry, head mapped
        --    through `pr2` into the target µ-entry, original maps lifted ─
        obtain ⟨bodyL, hbodyL⟩ := Term.fmap_nlam (C0.substAll ((List.range (d+1)).map Typ.var
          ++ LRelSubs.types (σ.drop d)))
          ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
              ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t)
        have hbodyL' : Term.fmap (C0.substAll ((List.range (d+1)).map Typ.var
              ++ LRelSubs.types ((LRelOf.pairE eP (LRelOf.mu C0 σ') :: σM : LRelSubs).drop (d+1))))
              ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                  ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t)
            = Term.nlam ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t).length
                (Term.lam bodyL) := by
          rw [show LRelSubs.types ((LRelOf.pairE eP (LRelOf.mu C0 σ') :: σM : LRelSubs).drop (d+1))
                = LRelSubs.types (σ.drop d) from by
              rw [List.drop_succ_cons]
              exact hdrop_types]
          exact hbodyL
        have hlayer_m := ihM (d := d + 1)
          (σ := LRelOf.pairE eP (LRelOf.mu C0 σ') :: σM)
          (σ' := LRelOf.mu C0 σ' :: σ')
          (Ss_t := (μ (C0.substAll (Typ.var 0 :: LRelSubs.types σM))
            ⨂ μ ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Ss_t)
          (Cs_t := (μ ((C0.substAll ((List.range (d+1)).map Typ.var
              ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t)
          (fns := ⟨(Term.var 0).pr2.lam, IsMValue.lam⟩ :: fns)
          (by simpa using WFM)
          (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons, hσ'len, hσMlen])
          (fun u hu => by
            headTail hu
            · exact hGpairPT
            · exact hGM u hu)
          (fun u hu => by
            headTail hu
            · exact hGTgt
            · exact hGout u hu)
          (by simp only [List.length_cons, hSClen])
          (by simp only [List.length_cons, hflen])
          (by simp only [List.length_cons]; omega)
          (fun S hS => by
            headTail hS
            · exact hPcl
            · exact hScl S hS)
          (fun T hT => by
            headTail hT
            · exact hμMtcl
            · exact hCcl T hT)
          (fun j hjd hjS hjσ => by
            cases j with
            | zero =>
                simp only [List.getElem_cons_zero, LRelOf.pairE_type, LRelOf.mu_type]
                rw [hePty, hmuEtyM, hMtout]
            | succ k =>
                simp only [List.getElem_cons_succ]
                simp only [List.length_cons] at hjS hjσ
                rw [hσMget_lt k (by omega) (by omega) (by omega)]
                exact hSlive k (by omega) (by omega) (by omega))
          (fun j hjd hjC hjσ' => by
            cases j with
            | zero =>
                simp only [List.getElem_cons_zero, LRelOf.mu_type]
                exact hMtout.symm
            | succ k =>
                simp only [List.getElem_cons_succ]
                simp only [List.length_cons] at hjC hjσ'
                exact hClive k (by omega) (by omega) (by omega))
          (fun j hjd hjσ hjσ' => by
            cases j with
            | zero => omega
            | succ k =>
                simp only [List.getElem_cons_succ]
                simp only [List.length_cons] at hjd hjσ hjσ'
                rw [hσMget_ge k (by omega) (by omega) (by omega)])
          (fun j hjS hjC hjf => by
            cases j with
            | zero =>
                simp only [List.getElem_cons_zero]
                exact HasType.lam hPcl (HasType.pr2 (HasType.var rfl))
            | succ k =>
                simp only [List.getElem_cons_succ]
                simp only [List.length_cons] at hjS hjC hjf
                exact (hfnsT k (by omega) (by omega) (by omega)).le' (Sε₄.trans R2.incr))
          (fun fn hfn σs k => by
            headTail hfn
            · rfl
            · exact hfcl fn hfn σs k)
          (fun j hjd hjσ => by
            cases j with
            | zero => simpa only [List.getElem_cons_zero] using hStpairPT
            | succ k =>
                simp only [List.length_cons] at hjd hjσ
                simp only [List.getElem_cons_succ]
                rw [hσMget_lt k (by omega) (by omega) (by omega)]
                exact hstab k (by omega) (by omega))
          (fun j hjd hjσ hjσ' hjf {εp} {p} Sp Rp => by
            cases j with
            | zero =>
                simp only [List.getElem_cons_zero, LRelOf.pairE_rel] at Rp ⊢
                obtain ⟨a1, a2, rfl, Ra1, Ra2⟩ := Rp
                refine ⟨a2, εp, ?_, ?_⟩
                · refine Eval.app (Eval.value IsMValue.lam)
                    (Eval.value (MVal.pair a1 a2).2) ?_
                  show ((Term.var 0).pr2.subs ((MVal.pair a1 a2).val :: []) 0, εp) ⇓ (a2, εp)
                  simp only [Term.subs]
                  exact Eval.pr2 (Eval.value (MVal.pair a1 a2).2)
                · simpa only [List.getElem_cons_zero] using Ra2
            | succ k =>
                simp only [List.getElem_cons_succ] at Rp ⊢
                simp only [List.length_cons] at hjd hjσ hjσ' hjf
                rw [hσMget_lt k (by omega) (by omega) (by omega)] at Rp
                exact hmap k (by omega) (by omega) (by omega) (by omega)
                  ((Sε₄.trans R2.incr).trans Sp) Rp)
          (fun j hjd hjσ hjσ' => by
            cases j with
            | zero => omega
            | succ k =>
                intro ε₀ w' hw'
                simp only [List.getElem_cons_succ] at hw' ⊢
                simp only [List.length_cons] at hjd hjσ hjσ'
                rw [hσMget_ge k (by omega) (by omega) (by omega)] at hw'
                exact hw')
          (fun j hjσ' => by
            cases j with
            | zero => simpa only [List.getElem_cons_zero] using hStTgt
            | succ k =>
                simp only [List.length_cons] at hjσ'
                simpa only [List.getElem_cons_succ] using hstabout k (by omega))
          hbodyL' Hw
        obtain ⟨y, εy, R3', Hy⟩ := (TRel.fmap_apps_app hbodyL
          (by simp only [List.length_cons, hflen])
          (fun fn hfn σs k => by
            headTail hfn
            · rfl
            · exact hfcl fn hfn σs k)
          (Eval.value w.2) hlayer_m).elim
        -- ── assembly: the `recur` evaluation and the fold into σ' ──────
        have hfnscl0 : (fns.map Subtype.val).map (·.subs [w.val] 0) = fns.map Subtype.val := by
          rw [List.map_map]
          apply List.map_congr_left
          intro fn hfn
          exact hfcl fn hfn [w.val] 0
        have R3 : ((Term.cons ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))
                (((Term.fmap (C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d)))
                    ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                        ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t)).apps
                  ((Term.var 0).pr2.lam :: fns.map Subtype.val)).app (Term.var 0))).sub w.val, εw)
            ⇓ (MVal.cons ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t)) y, εy) := by
          rw [show (Term.cons ((C0.substAll ((List.range (d+1)).map Typ.var
                ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))
                (((Term.fmap (C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d)))
                    ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                        ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t)).apps
                  ((Term.var 0).pr2.lam :: fns.map Subtype.val)).app (Term.var 0))).sub w.val
              = Term.cons ((C0.substAll ((List.range (d+1)).map Typ.var
                  ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))
                (((Term.fmap (C0.substAll ((List.range (d+1)).map Typ.var
                    ++ LRelSubs.types (σ.drop d)))
                    ((μ ((C0.substAll ((List.range (d+1)).map Typ.var
                        ++ LRelSubs.types (σ.drop d))).substAll (Typ.var 0 :: Cs_t))) :: Cs_t)).apps
                  ((Term.var 0).pr2.lam :: fns.map Subtype.val)).app w.val) from by
            simp only [Term.sub, Term.subs, Term.subs_apps, List.map_cons,
              Term.fmap_subs hA'cWfM hCc2, hfnscl0, Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd,
              reduceDIte, List.get_eq_getElem, List.getElem_cons_zero, List.length_cons,
              List.length_nil]]
          exact Eval.cons R3'
        refine TRel.intro (Eval.recur (Eval.value (MVal.cons (C0.substAll (Typ.var 0
            :: LRelSubs.types σM)) u₄).2) R2 R3) ?_
        rw [VRel.mu_unfold WF' WSout]
        exact ⟨y, by rw [hMtl], Hy⟩
      -- ── conclude: inject the scrutinee into the mixed environment and
      --    apply the predicate at the reflexive descendant ──────────────
      have hLeM : LRelSubs.Le σ σM := by
        refine ⟨hσMtypes.symm, ?_⟩
        intro k s₁ s₂ hk1 hk2 ε₀ v₀ hv₀
        obtain ⟨hkσ, hs₁⟩ := List.getElem?_eq_some_iff.mp hk1
        by_cases hkd : k < d
        · have h := hσMget?_lt k hkd
          rw [hk2, List.getElem?_eq_getElem hkσ] at h
          obtain rfl := Option.some.inj h
          rw [← hs₁] at hv₀
          exact hv₀
        · have hkσ' : k < σ'.length := by omega
          have h := hσMget?_ge k (by omega)
          rw [hk2, List.getElem?_eq_getElem hkσ'] at h
          obtain rfl := Option.some.inj h
          rw [← hs₁] at hv₀
          exact hsub k (by omega) hkσ hkσ' ε₀ v₀ hv₀
      have VxM : x ∈ V⟦μ C0⟧σM#ε' := VRel.mono_env hLeM (Typ.Wf.mu WF) Vx
      exact key VxM ε' (Env.refl ε') ε' x RebStar.refl (Env.refl ε')

/-- Cap entries over pointwise-Good, pointwise-Stable environments are
stable — the `d := 0` instance of the mapped fmap lemma. -/
lemma VRel.cap_stable {Y : Typ} {σ : LRelSubs} :
    Y.Wf σ.length →
    (∀ s ∈ σ, LRelOf.Good s) →
    (∀ j (hjσ : j < σ.length), LRelOf.Stable (σ[j]'hjσ)) →
    LRelOf.Stable (LRelOf.cap Y σ) := by
  intro hY hG hst
  refine ⟨rfl, ?_⟩
  intro Ss_t Cs_t fns ε₀ w body' hSClen hflen hScl hCcl hfnsT hfcl R hbody
  simp only [LRelOf.cap_rel] at R
  have hbody' : Term.fmap (Y.substAll ((List.range 0).map Typ.var
      ++ LRelSubs.types (σ.drop 0))) Cs_t = Term.nlam Cs_t.length (Term.lam body') := by
    simpa only [List.range_zero, List.map_nil, List.drop_zero, List.nil_append] using hbody
  have hres := VRel.fmap_mapped (C := Y) (d := 0) (σ := σ) (σ' := σ)
    hY (Nat.zero_le _) rfl hG hG hSClen hflen (Nat.zero_le _) hScl hCcl
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j _ hjσ hjσ' => rfl)
    hfnsT hfcl
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j _ hjσ hjσ' ε₁ w' hw => hw)
    hst
    hbody' R
  obtain ⟨w', ε₁, Rw, V⟩ := hres.elim
  exact ⟨w', ε₁, Rw, V⟩

/-- The functorial map `fmap₁` respects the logical relation, over ANY
Good, Stable var-0 entry `e` of the recursive type (canonical instance
`e := LRelOf.mu A' ρ0`; `recur` pushes its Park-meet entry).  The `d = 1`
instance of the mapped fmap lemma `VRel.fmap_mapped`. -/
lemma VRel.fmap₁ {e : LRelOf} :
    A.Wf 1 → 1 ⊢ A' ∷type → ⊢ B ∷type →
    e.type = μ A' → LRelOf.Good e → LRelOf.Stable e →
    MVal.fmap₁ A ((μ A') ⨂ B.sub (μ A')) ∈
      V⟦(Typ.var 0 ⟶ Typ.var 0 ⨂ B) ⟶ A ⟶ A.sub (Typ.var 0 ⨂ B)⟧ (e :: ρ0) # ε := by
  intro hA hA' hB hety hGe hSte
  rw [show B.sub (μ A') = B from Typ.sub_closed hB]
  obtain ⟨body, hbody⟩ := Term.fmap_nlam A [(μ A') ⨂ B]
  have hveq : MVal.fmap₁ A ((μ A') ⨂ B)
      = (⟨Term.nlam 1 (Term.lam body), IsMValue.nlam_lam⟩ : MVal) := by
    apply Subtype.ext
    show Term.fmap A [(μ A') ⨂ B] = Term.nlam 1 (Term.lam body)
    simpa using hbody
  rw [hveq]
  have hGall : ∀ s ∈ (e :: ρ0 : LRelSubs), LRelOf.Good s := by
    intro s hs
    headTail hs
    · exact hGe
    · simp at hs
  have hstall : ∀ j (hjσ : j < (e :: ρ0 : LRelSubs).length),
      LRelOf.Stable ((e :: ρ0 : LRelSubs)[j]'hjσ) := by
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    exact hSte
  have WSe : LRelSubs.Kripke (e :: ρ0) := fun s hs => (hGall s hs).wf
  have hμA'cl : (μ A').Closed := Typ.Wf.mu hA'
  have hρecl : LRelSubs.Closed (e :: ρ0) := fun s hs => (hGall s hs).closed
  have hPwf : (Typ.var 0 ⨂ B).Wf (e :: ρ0 : LRelSubs).length :=
    Typ.Wf.prod (Typ.Wf.var (by simp)) (hB.mono (Nat.zero_le _))
  -- the typing of the fmap value at the collapsed `funcsTo` type
  have hT := VRel.fmap_eval_typing (F := A) (Cs := [Typ.var 0 ⨂ B])
    (ρ := e :: ρ0) (ε := ε)
    (by simpa using hA) (by simp)
    (fun C hC => by
      rw [List.mem_singleton] at hC
      subst hC
      exact hPwf)
    hρecl
  have hCsmap : ([Typ.var 0 ⨂ B] : List Typ).map
      (·.substAll (LRelSubs.types (e :: ρ0))) = [(μ A') ⨂ B] := by
    simp only [List.map_cons, List.map_nil, Typ.substAll, LRelSubs.types_cons, LRelSubs.types_nil,
      List.getD_cons_zero, Typ.substAll_closed hB, hety]
  have hTy : ⊢{ε} Term.nlam 1 (Term.lam body)
      ∷ (Typ.funcsTo [Typ.var 0] [Typ.var 0 ⨂ B] (A ⟶ A.sub (Typ.var 0 ⨂ B))).substAll
          (LRelSubs.types (e :: ρ0)) := by
    have h := hT
    rw [hCsmap, hbody] at h
    rw [show ((e :: ρ0) : LRelSubs).length = 1 from rfl,
        show ((List.range 1).map Typ.var : List Typ) = [Typ.var 0] from by
          simp [List.range_one],
        show A.substAll [Typ.var 0 ⨂ B] = A.sub (Typ.var 0 ⨂ B) from
          Typ.substAll_singleton hA _] at h
    exact h
  refine VRel.nlam_funcsTo_env WSe (Ss := [Typ.var 0]) (Cs := [Typ.var 0 ⨂ B])
    (Sx := A) (Tx := A.sub (Typ.var 0 ⨂ B)) rfl rfl hTy ?_
  intro ε'' fns' x S'' hflen' hg' Vx
  obtain ⟨f, rfl⟩ : ∃ f, fns' = [f] := by
    cases fns' with
    | nil => simp at hflen'
    | cons f rest =>
        cases rest with
        | nil => exact ⟨f, rfl⟩
        | cons g rest' => simp at hflen'
  have hgf := hg' 0 (by simp) (by simp) (by simp)
  simp only [List.getElem_cons_zero] at hgf
  -- the output entry: the (substituted) pair type over `e :: ρ0`
  have hGcap : LRelOf.Good (LRelOf.cap (Typ.var 0 ⨂ B) (e :: ρ0)) :=
    LRelOf.Good.cap hPwf hGall
  have hStcap : LRelOf.Stable (LRelOf.cap (Typ.var 0 ⨂ B) (e :: ρ0)) :=
    VRel.cap_stable hPwf hGall hstall
  have hcapty : (LRelOf.cap (Typ.var 0 ⨂ B) (e :: ρ0)).type = (μ A') ⨂ B := by
    simp only [LRelOf.cap_type, Typ.substAll, LRelSubs.types_cons, LRelSubs.types_nil,
      List.getD_cons_zero, Typ.substAll_closed hB, hety]
  have hTf : ⊢{ε''} f.val ∷ (μ A') ⟶ ((μ A') ⨂ B) := by
    have hgfk := hgf
    vrel at hgfk
    have h1 := hgfk.1
    simpa only [Typ.substAll, LRelSubs.types_cons, LRelSubs.types_nil,
      List.getD_cons_zero, Typ.substAll_closed hB, hety] using h1
  -- the map clause supplied by the input arrow
  have hmapf : ∀ {ε₂ : Env} {a : MVal}, ε''.le ε₂ → e.rel ε₂ a →
      ∃ (w : MVal) (ε₃ : Env), (f.val.app a.val, ε₂) ⇓ (w, ε₃) ∧
        (LRelOf.cap (Typ.var 0 ⨂ B) (e :: ρ0)).rel ε₃ w := by
    intro ε₂ a S₂ Ra
    have hgfk := hgf
    vrel at hgfk
    obtain ⟨Tfk, t, hft, harr⟩ := hgfk
    have Tk := harr ε₂ S₂ a ⟨e, rfl, hGe.hasType Ra, Ra⟩
    simp only [TRel] at Tk
    obtain ⟨w, ε₃, Rta, Vw⟩ := Tk
    have hfval : f.val = Term.lam t := congrArg Subtype.val hft
    refine ⟨w, ε₃, ?_, ?_⟩
    · rw [hfval]
      exact Eval.app (Eval.value IsMValue.lam) (Eval.value a.2) Rta
    · simpa only [LRelOf.cap_rel] using Vw
  -- the mapped-fmap instance
  have hbody' : Term.fmap (A.substAll ((List.range 1).map Typ.var
        ++ LRelSubs.types ((e :: ρ0 : LRelSubs).drop 1))) [(μ A') ⨂ B]
      = Term.nlam ([(μ A') ⨂ B] : List Typ).length (Term.lam body) := by
    rw [show A.substAll ((List.range 1).map Typ.var
          ++ LRelSubs.types ((e :: ρ0 : LRelSubs).drop 1)) = A from by
        simpa using Typ.substAll_rangeVar (A := A) (n := 1)]
    exact hbody
  have hM := VRel.fmap_mapped (C := A) (d := 1) (σ := e :: ρ0)
    (σ' := [LRelOf.cap (Typ.var 0 ⨂ B) (e :: ρ0)])
    (Ss_t := [μ A']) (Cs_t := [(μ A') ⨂ B]) (fns := [f])
    (by simpa using hA) (by simp) (by simp) hGall
    (fun s hs => by rw [List.mem_singleton] at hs; subst hs; exact hGcap)
    rfl rfl (by simp)
    (fun S hS => by rw [List.mem_singleton] at hS; subst hS; exact hμA'cl)
    (fun T hT => by
      rw [List.mem_singleton] at hT
      subst hT
      exact Typ.Wf.prod hμA'cl hB)
    (fun j hjl hjS hjσ => by
      obtain rfl : j = 0 := by omega
      simp only [List.getElem_cons_zero]
      exact hety.symm)
    (fun j hjl hjC hjσ' => by
      obtain rfl : j = 0 := by omega
      simp only [List.getElem_cons_zero]
      exact hcapty.symm)
    (fun j hj hjσ hjσ' => by
      simp only [List.length_singleton] at hjσ'
      exact absurd hjσ' (by omega))
    (fun j hjS hjC hjf => by
      obtain rfl : j = 0 := by
        simp only [List.length_singleton] at hjS
        omega
      simpa only [List.getElem_cons_zero] using hTf)
    (fun fn hfn σs k => by
      rw [List.mem_singleton] at hfn
      subst hfn
      exact HasType.closed hTf)
    (fun j hjl hjσ => by
      obtain rfl : j = 0 := by omega
      simpa only [List.getElem_cons_zero] using hSte)
    (fun j hjl hjσ hjσ' hjf {ε₂} {a} S₂ Ra => by
      obtain rfl : j = 0 := by omega
      simp only [List.getElem_cons_zero] at Ra ⊢
      exact hmapf S₂ Ra)
    (fun j hj hjσ hjσ' => by
      simp only [List.length_singleton] at hjσ'
      exact absurd hjσ' (by omega))
    (fun j hjσ' => by
      obtain rfl : j = 0 := by
        simp only [List.length_singleton] at hjσ'
        omega
      simpa only [List.getElem_cons_zero] using hStcap)
    hbody' Vx
  -- bridge the output back to the substituted form over `e :: ρ0`
  obtain ⟨w, εw, Rw, Vw⟩ := hM.elim
  have Vw2 : w ∈ V⟦A⟧(LRelOf.cap (Typ.var 0 ⨂ B) (e :: ρ0) :: e :: ρ0)#εw := by
    refine (VRel.env_eq hA ?_).mp Vw
    intro j hj
    obtain rfl : j = 0 := by omega
    rfl
  have Vw3 := (VRel.internalize (C := A) (Y := Typ.var 0 ⨂ B) (Δ := []) (ρt := e :: ρ0)
      (fun s hs => by simp at hs) hρecl hPwf
      (show A.Wf (([] : LRelSubs).length + 1 + (e :: ρ0 : LRelSubs).length) from by
        simpa using hA.mono (by omega : 1 ≤ 2))).mpr (by simpa using Vw2)
  refine TRel.intro Rw ?_
  have htyeq : A.substAll ((List.range ([] : LRelSubs).length).map Typ.var
        ++ Typ.shiftN ([] : LRelSubs).length (Typ.var 0 ⨂ B)
          :: (List.range' ([] : LRelSubs).length (e :: ρ0 : LRelSubs).length).map Typ.var)
      = A.sub (Typ.var 0 ⨂ B) := by
    rw [show (([] : LRelSubs).length) = 0 from rfl]
    simp only [List.range_zero, List.map_nil, List.nil_append, Typ.shiftN_zero]
    rw [show ((List.range' 0 (e :: ρ0 : LRelSubs).length).map Typ.var : List Typ)
          = [Typ.var 0] from rfl]
    rw [show A.substAll [Typ.var 0 ⨂ B, Typ.var 0] = A.substAll [Typ.var 0 ⨂ B] from
        Typ.substAll_eq hA (fun j hj => by
          obtain rfl : j = 0 := by omega
          rfl)]
    exact Typ.substAll_singleton hA _
  rw [htyeq] at Vw3
  simpa using Vw3

/-- One rebuild step on a folded value `cons A u` of a closed recursive
type, over an arbitrary Good+Stable var-0 entry `e` (the Park meets of
`recur_key`): the step evaluates to another folded value whose body is
again over `e`.  The `σt := ρ0` instance of `VRel.mu_fmap_rebuild_land`. -/
lemma VRel.mu_rebstep {A} {e : LRelOf} (WFA : 1 ⊢ A ∷type)
    (hety : e.type = μ A) (hGe : LRelOf.Good e) (hSte : LRelOf.Stable e)
    {ε₅ ε₆} {u₅ : MVal} {v₆ : MVal}
    (Hu : VRel A (e :: ρ0) ε₅ u₅)
    (hstep : RebStep (μ A) ε₅ (MVal.cons A u₅) ε₆ v₆) :
    ∃ u₆, v₆ = MVal.cons A u₆ ∧ VRel A (e :: ρ0) ε₆ u₆ := by
  have ihM : VRel.FmapMappedIH A := VRel.fmap_mapped (C := A)
  have hA0 : A.substAll (Typ.var 0 :: LRelSubs.types ρ0) = A :=
    Typ.substAll_var0_cons WFA _
  have hμ0 : (μ A).substAll (LRelSubs.types ρ0) = μ A := by
    simp only [LRelSubs.types_nil, Typ.substAll_nil]
  obtain ⟨u₆, hv, V⟩ := VRel.mu_fmap_rebuild_land (C0 := A) (σt := ρ0) ihM
    (by simpa using WFA)
    (fun s hs => by simp at hs)
    (fun j hj => by simp at hj)
    (by rw [hety, hμ0]) hGe hSte Hu
    (by rw [hμ0, hA0]; exact hstep)
  rw [hA0] at hv
  exact ⟨u₆, hv, V⟩


/-- Kernel of `TRel.recur`: discharging a `recur` whose scrutinee is a
*value* of the recursive type — by `LRel.lfp.strong_induction` with the
descendant-closed Kripke Park predicate
`X ε₂ v := ∀ ε₃ ⊒ ε₂, ∀ (ε₄,v') ∈ RebStar (μA) (ε₃,v), ε ⊑ ε₄ →
recur B s v' ∈ T⟦B⟧ε₄`; the step function's recursive call is justified
by the Park conjunct carried by the var-0 entry `⟨µA, lfp ⊓ X⟩`, whose
Good/Stable evidence feeds the generalized `VRel.fmap₁`, and the
descendant dimension is grounded by `VRel.mu_rebstep`. -/
lemma TRel.recur_key {s A B ε} :
    1 ⊢ A ∷type → ⊢ B ∷type →
    [A.sub (μ A ⨂ B)] ⊢{ε} s ∷ B →
    (∀ {v : MVal} {ε' : Env}, ε.le ε' →
      v ∈ V⟦A.sub (Typ.var 0 ⨂ B)⟧(LRelOf.mu A ρ0 :: ρ0) # ε' →
      s.sub v ∈ T⟦B⟧(LRelOf.mu A ρ0 :: ρ0) # ε') →
    ∀ {ε2 : Env} (v : MVal), ε.le ε2 → v ∈ V⟦μ A⟧ε2 →
      Term.recur B s v.val ∈ T⟦B⟧ε2 := by
  intro WFA WFB Ts IH2
  have hμA : (μ A).Closed := Typ.Wf.mu WFA
  -- the descendant-closed Kripke Park predicate
  set X : LRel := fun ε₂ v => ∀ ε₃, ε₂.le ε₃ → ∀ (ε₄ : Env) (v' : MVal),
    RebStar (μ A) ε₃ v ε₄ v' → ε.le ε₄ →
    Term.recur B s v'.val ∈ T⟦B⟧ε₄ with hX
  have hXwf : LRel.Kripke X := by
    intro ε₁ ε₂ v S hv ε₃ S23 ε₄ v' hstar Sε₄
    exact hv ε₃ (S.trans S23) ε₄ v' hstar Sε₄
  have hmono : LRel.Mono (VRel.muOper A ρ0) :=
    fun h => VRel.muOper_mono (by simpa using WFA) h
  -- the canonical entry is Good and Stable
  have hGmu : LRelOf.Good (LRelOf.mu A ρ0) := by
    rw [LRelOf.mu_eq_cap]
    exact LRelOf.Good.cap (by simpa using hμA) (fun u hu => by simp at hu)
  have hStmu : LRelOf.Stable (LRelOf.mu A ρ0) := by
    rw [LRelOf.mu_eq_cap]
    exact VRel.cap_stable (by simpa using hμA) (fun u hu => by simp at hu)
      (fun j hj => by simp at hj)
  -- the Park-meet entry
  set eP : LRelOf := ⟨(μ A).substAll (LRelSubs.types ρ0),
    fun ε₂ w => LRel.lfp (VRel.muOper A ρ0) ε₂ w ∧ X ε₂ w⟩ with heP
  have hePty : eP.type = μ A := by
    simp only [heP, LRelSubs.types_nil, Typ.substAll_nil]
  have hGeP : LRelOf.Good eP := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hePty]; exact hμA
    · intro v ε₁ ε₂ S hv
      exact ⟨LRel.lfp.kripke _ _ _ S hv.1, hXwf _ _ _ S hv.2⟩
    · intro ε₁ w hw
      have h1 := hw.1
      rw [← VRel.mu_def] at h1
      exact VRel.HasType_open (fun u hu => by simp at hu) (by simpa using hμA) h1
  have hSteP : LRelOf.Stable eP := by
    refine ⟨rfl, ?_⟩
    intro Ss_t Cs_t fns ε₀ w body' h1 h2 h3 h4 h5 h6 hw hbody
    have hwmu : (LRelOf.mu A ρ0).rel ε₀ w := by
      simp only [LRelOf.mu_rel]
      rw [VRel.mu_def]
      exact hw.1
    obtain ⟨w', ε₁, R, V⟩ := hStmu.2 h1 h2 h3 h4 h5 h6 hwmu hbody
    refine ⟨w', ε₁, R, ?_, ?_⟩
    · -- lfp landing
      have := V
      simp only [LRelOf.mu_rel] at this
      rw [VRel.mu_def] at this
      exact this
    · -- X landing: the result is a one-step descendant
      have hXw := hw.2
      have hstep1 : RebStep (μ A) ε₀ w ε₁ w' := by
        refine ⟨Ss_t, Cs_t, fns, body', h1, h2, h3, h4, h5, h6, ?_, R⟩
        rw [← hePty]
        exact hbody
      intro ε₃' S₁₃' ε₄' v₄' hstar' Sε₄'
      refine hXw ε₀ (Env.refl ε₀) ε₄' v₄' ?_ Sε₄'
      exact RebStar.trans (RebStar.weak (RebStar.single hstep1) S₁₃') hstar'
  have WSP : LRelSubs.Kripke (eP :: ρ0) := by
    intro u hu
    headTail hu
    · exact hGeP.wf
    · simp at hu
  -- the key: every µ-value satisfies the Park predicate
  have key : ∀ {ε₂ : Env} {v : MVal}, _root_.VRel (μ A) ρ0 ε₂ v → X ε₂ v := by
    intro ε₂ v hv
    rw [VRel.mu_def] at hv
    refine LRel.lfp.strong_induction hmono hXwf ?_ ε₂ v hv
    intro ε₂' a ha
    obtain ⟨a', hcons, Ha'⟩ := ha
    rw [show A.substAll (Typ.var 0 :: (LRelSubs.types ρ0).map (Typ.shift 0)) = A from
        Typ.substAll_var0_cons WFA _] at hcons
    subst hcons
    -- show X ε₂' (cons A a')
    intro ε₃ S23 ε₄ v₄ hstar Sε₄
    -- descend the rebuild chain: every descendant is a fold over the meet
    have descend : ∀ {εa εb : Env} {va vb : MVal},
        RebStar (μ A) εa va εb vb →
        ∀ {u : MVal}, va = MVal.cons A u → _root_.VRel A (eP :: ρ0) εa u →
        ∃ u₄, vb = MVal.cons A u₄ ∧ _root_.VRel A (eP :: ρ0) εb u₄ := by
      intro εa εb va vb h
      induction h with
      | refl =>
          intro u hva Hu
          exact ⟨u, hva, Hu⟩
      | weak hst S ih =>
          intro u hva Hu
          obtain ⟨u₄, rfl, Hu₄⟩ := ih hva Hu
          exact ⟨u₄, rfl, VRel.kripke WSP Hu₄ S⟩
      | tail hst hstep ih =>
          intro u hva Hu
          obtain ⟨u₄, rfl, Hu₄⟩ := ih hva Hu
          exact VRel.mu_rebstep WFA hePty hGeP hSteP Hu₄ hstep
    obtain ⟨u₄, rfl, Hu₄⟩ := descend hstar rfl (VRel.kripke WSP Ha' S23)
    have Sε₄' : ε.le ε₄ := Sε₄
    -- the step-function realiser over the meet entry
    have Hstepfn : MVal.lam (Term.pair (Term.var 0) (Term.recur B s (Term.var 0)))
        ∈ V⟦Typ.var 0 ⟶ Typ.var 0 ⨂ B⟧(eP :: ρ0)#ε₄ := by
      vrel
      constructor
      · have e1 : (Typ.var 0 ⟶ Typ.var 0 ⨂ B).substAll (LRelSubs.types (eP :: ρ0))
            = (μ A) ⟶ ((μ A) ⨂ B) := by
          simp only [LRelSubs.types_cons, LRelSubs.types_nil, Typ.substAll,
            List.getD_cons_zero, Typ.substAll_closed WFB, hePty]
        rw [e1]
        refine HasType.lam hμA (HasType.pair (HasType.var rfl) ?_)
        refine HasType.recur hμA WFB ?_ (HasType.var rfl)
        have hT := HasType.weaken (Γ' := [μ A]) (Ts.le' Sε₄)
        simpa using hT
      · refine ⟨_, rfl, ?_⟩
        intro ε₅ S₅ a₁ Va₁
        obtain ⟨s₀, hs₀, Ta₁, Ra₁⟩ := Va₁
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hs₀
        subst hs₀
        have hsub1 : (Term.pair (Term.var 0) (Term.recur B s (Term.var 0))).sub a₁.val
            = Term.pair a₁.val (Term.recur B s a₁.val) := by
          simp only [Term.sub, Term.subs]
          rw [HasType.closed' Ts (by simp)]
          simp
        rw [hsub1]
        have Hpair : Term.pair a₁.val (Term.recur B s a₁.val)
            ∈ T⟦Typ.var 0 ⨂ B⟧(eP :: ρ0)#ε₅ := by
          refine TRel.pair WSP ?_ ?_ (Env.refl ε₅)
          · refine TRel'.VRel WSP (?_ : a₁ ∈ V⟦Typ.var 0⟧(eP :: ρ0)#ε₅)
            vrel
            exact ⟨eP, rfl, Ta₁, Ra₁⟩
          · intro ε₆ S₆
            have hrec := Ra₁.2 ε₆ S₆ ε₆ a₁ RebStar.refl ((Sε₄.trans S₅).trans S₆)
            exact hrec.type_closed WFB
        exact Hpair
    -- the fmap₁ step over the meet entry
    have hfm := VRel.fmap₁ (e := eP) (A := A) (A' := A) (B := B) (ε := ε₄)
      WFA WFA WFB hePty hGeP hSteP
    rw [Typ.sub_closed WFB] at hfm
    have hap : ((Term.fmap₁ A (μ A ⨂ B)).app
          (Term.lam (Term.pair (Term.var 0) (Term.recur B s (Term.var 0))))).app u₄.val
        ∈ T'⟦A.sub (Typ.var 0 ⨂ B)⟧(eP :: ρ0)#ε₄ :=
      TRel.app (TRel.app (TRel'.VRel WSP hfm) (TRel'.VRel WSP Hstepfn))
        (TRel'.VRel WSP Hu₄)
    obtain ⟨w, ε₅, R2, Vw⟩ := (hap (Env.refl ε₄)).elim
    -- convert the output to the canonical environment for IH2
    have hLe : LRelSubs.Le (eP :: ρ0) (LRelOf.mu A ρ0 :: ρ0) := by
      refine ⟨rfl, ?_⟩
      intro k s₁ s₂ hk1 hk2 ε₆ v₆ hv₆
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk1 hk2
          subst hk1
          subst hk2
          simp only [LRelOf.mu_rel]
          rw [VRel.mu_def]
          exact hv₆.1
      | succ k => simp at hk1
    have hsubWf : (A.sub (Typ.var 0 ⨂ B)).Wf ((eP :: ρ0 : LRelSubs).length) := by
      have h := Typ.Wf.subAt (show A.Wf (1+1) from WFA.mono (by omega))
        (show (0:Nat) ≤ 1 by omega)
        (show (Typ.var 0 ⨂ B).Wf 1 from
          Typ.Wf.prod (Typ.Wf.var (by omega)) (WFB.mono (Nat.zero_le _)))
      simpa using h
    have Vw' := VRel.mono_env hLe hsubWf Vw
    obtain ⟨u', εu', R3, Vu'⟩ := (IH2 (Sε₄.trans R2.incr) Vw').elim
    exact TRel.intro (Eval.recur (Eval.value (MVal.cons A u₄).2) R2 R3)
      (Vu'.type_closed WFB)
  -- conclude from the key
  intro ε₂ v S0 Vv
  exact key Vv ε₂ (Env.refl ε₂) ε₂ v RebStar.refl S0

/-- Semantic counterpart of the `recur` typing rule. -/
lemma TRel.recur {s t}:
    1 ⊢ A ∷type →
    ⊢ B ∷type →
    [A.sub (μ A ⨂ B)] ⊢{ε} s ∷ B →
    t ∈ T'⟦Typ.var 0⟧(LRelOf.mu A ρ0 :: ρ0) # ε →
    (∀ {v ε'}, ε.le ε' → v ∈ V⟦A.sub (Typ.var 0 ⨂ B)⟧(LRelOf.mu A ρ0 :: ρ0) # ε' →
      s.sub v ∈ T⟦B⟧(LRelOf.mu A ρ0 :: ρ0) # ε') →
    Term.recur B s t ∈ T'⟦B⟧(LRelOf.mu A ρ0 :: ρ0) # ε := by
  intro WFA WFB Ts IH1 IH2 ε1 S0
  obtain ⟨v, ε2, R1, U⟩ := (IH1 S0).elim
  have S1 := R1.incr
  simp only [_root_.VRel, List.getElem?_cons_zero, Option.some.injEq] at U
  obtain ⟨s₀, hs₀, Tv, R⟩ := U
  subst hs₀
  simp only [LRelOf.mu_rel] at R
  have hrec := TRel.recur_key WFA WFB (Ts.le' S0) (fun S V => IH2 (S0.trans S) V)
    v S1 R
  have := TRel.recur_val R1 R hrec
  exact this.type_closed WFB
