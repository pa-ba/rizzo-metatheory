import Rizzo.Env
import Rizzo.Terms

/-
Basic definitions for the logical relation
-/

abbrev LRel : Type := Env → MVal → Prop

namespace LRel

/-- Monotonicity of an operator on value predicates. -/
def Mono (F : LRel → LRel) : Prop := ∀ {X Y : LRel}, X ≤ Y → F X ≤ F Y

/-- Kripke monotonicity: a predicate is stable under runtime-environment
extension. -/
def Kripke (X : LRel) : Prop := ∀ ε ε' (v : MVal), ε.le ε' → X ε v → X ε' v

end LRel

/-- The intersection of all Kripke-monotone `F`-prefixed points; for
monotone, Kripke-preserving `F` this is the least fixed point
(Knaster–Tarski in the lattice of Kripke-monotone predicates). -/
def LRel.lfp (F : LRel → LRel) : LRel :=
  fun ε v => ∀ X : LRel, X.Kripke → F X ≤ X → X ε v

namespace LRel.lfp

variable {F G : LRel → LRel}

/-- `LRel.lfp F` is Kripke-monotone. -/
lemma kripke : (LRel.lfp F).Kripke :=
  fun _ε _ε' _v S h X hWf hX => hWf _ _ _ S (h X hWf hX)

/-- `LRel.lfp F` is below every Kripke-monotone prefixed point (no
monotonicity needed). -/
lemma le_prefixed {X : LRel} : X.Kripke → F X ≤ X → LRel.lfp F ≤ X :=
  fun hWf hX _ _ h => h X hWf hX

/-- `LRel.lfp` is monotone in the operator (no monotonicity needed). -/
lemma mono_oper : (∀ X : LRel, F X ≤ G X) → LRel.lfp F ≤ LRel.lfp G :=
  fun h _ε _v hv X hWf hX => hv X hWf (fun ε' w hF => hX ε' w (h X ε' w hF))

/-- Congruence in the operator (no monotonicity needed). -/
lemma congr_oper : (∀ X : LRel, F X = G X) → LRel.lfp F = LRel.lfp G := by
  intro h
  funext ε v
  exact propext
    ⟨fun hv => mono_oper (fun X ε' w hw => h X ▸ hw) ε v hv,
     fun hv => mono_oper (fun X ε' w hw => (h X).symm ▸ hw) ε v hv⟩

/-- Iff-form of operator congruence (the form the locality lemmas of
the logical relation produce). -/
lemma congr_oper_iff :
    (∀ X : LRel, ∀ ε v, F X ε v ↔ G X ε v) → LRel.lfp F = LRel.lfp G :=
  fun h => congr_oper (fun X => funext fun ε => funext fun v => propext (h X ε v))

/-- Folding: `F (LRel.lfp F) ≤ LRel.lfp F`. -/
lemma prefixed : LRel.Mono F → F (LRel.lfp F) ≤ LRel.lfp F := by
  intro hF ε v h X hWf hX
  exact hX ε v (hF (le_prefixed hWf hX) ε v h)

/-- Unfolding: `LRel.lfp F ≤ F (LRel.lfp F)`, provided the unfolding is
itself Kripke-monotone (it is whenever the µ-body's environment is
well-formed). -/
lemma postfixed :
    LRel.Mono F → (F (LRel.lfp F)).Kripke → LRel.lfp F ≤ F (LRel.lfp F) := by
  intro hF hWf ε v h
  exact h (F (LRel.lfp F)) hWf (hF (prefixed hF))

/-- The fixed-point equation (Knaster–Tarski). -/
lemma unfold :
    LRel.Mono F → (F (LRel.lfp F)).Kripke → LRel.lfp F = F (LRel.lfp F) := by
  intro hF hWf
  funext ε v
  exact propext ⟨fun h => postfixed hF hWf ε v h, fun h => prefixed hF ε v h⟩

/-- Strong induction (Park induction with the fixed point available in
the hypothesis): to show `LRel.lfp F ≤ X` for Kripke-monotone `X` it
suffices to close `X` under `F` on arguments already known to be in the
fixed point. -/
lemma strong_induction {X : LRel} :
    LRel.Mono F → X.Kripke →
    F (fun ε v => LRel.lfp F ε v ∧ X ε v) ≤ X → LRel.lfp F ≤ X := by
  intro hF hXWf h
  have hYWf : LRel.Kripke (fun ε v => LRel.lfp F ε v ∧ X ε v) := by
    intro ε ε' v S hv
    exact ⟨kripke ε ε' v S hv.1, hXWf ε ε' v S hv.2⟩
  have hY : F (fun ε v => LRel.lfp F ε v ∧ X ε v) ≤
      (fun ε v => LRel.lfp F ε v ∧ X ε v) := by
    intro ε v hv
    exact ⟨prefixed hF ε v (hF (fun _ _ hw => hw.1) ε v hv), h ε v hv⟩
  exact fun ε v hv => (le_prefixed hYWf hY ε v hv).2

end LRel.lfp


---------------------------------------------------
-- Semantic environments (`LRelOf` / `LRelSubs`) --
---------------------------------------------------

/-- A logical-relation entry (`LRelOf`): a (syntactic) type together
with the logical relation (`LRel`) interpreting it. -/
structure LRelOf : Type where
  mk ::
  type : Typ
  rel : LRel

/-- A logical-relation substitution interprets the free type variables
  of a type. -/
abbrev LRelSubs := List LRelOf

/-- The underlying syntactic types of a semantic environment. -/
def LRelSubs.types (ρ : LRelSubs) : List Typ := ρ.map (·.type)

/-- The empty semantic environment (for closed types). -/
abbrev ρ0 : LRelSubs := []

@[simp] lemma LRelSubs.types_nil : LRelSubs.types ρ0 = [] := rfl

@[simp] lemma LRelSubs.types_cons {s : LRelOf} {ρ : LRelSubs} :
    LRelSubs.types (s :: ρ) = s.type :: ρ.types := rfl

@[simp] lemma LRelSubs.types_length {ρ : LRelSubs} : ρ.types.length = ρ.length := by
  simp [LRelSubs.types]

lemma LRelSubs.types_append (Δ ρ : LRelSubs) : (Δ ++ ρ).types = Δ.types ++ ρ.types := by
  simp [LRelSubs.types]

/-- Two environments agreeing on their first `k` entries also agree on
  the first `k` entries of their underlying type lists. -/

lemma LRelSubs.types_getElem?_congr {ρ ρ' : LRelSubs} {k : Nat} :
    (∀ j, j < k → ρ[j]? = ρ'[j]?) → ∀ j, j < k → ρ.types[j]? = ρ'.types[j]? :=
  fun h j hj => by simp only [LRelSubs.types, List.getElem?_map, h j hj]

/-- All types interpreted by the environment are closed. -/
def LRelSubs.Closed (ρ : LRelSubs) := ∀ s ∈ ρ, s.type.Closed

@[simp]
lemma LRelSubs.Closed.nil : LRelSubs.Closed ρ0 := by
  intro s h; simp at h

/-- The underlying types of a closed semantic environment are closed. -/
lemma LRelSubs.Closed.types {ρ : LRelSubs} : ρ.Closed → ∀ C ∈ ρ.types, C.Closed := by
  intro hρ C hC
  rcases List.mem_map.mp hC with ⟨s, hs, rfl⟩
  exact hρ s hs

/-- On a closed environment, shifting the underlying types is the identity. -/
lemma LRelSubs.Closed.types_shift {ρ : LRelSubs} :
    ρ.Closed → ρ.types.map (Typ.shift 0) = ρ.types := by
  intro hρ
  have h : ∀ (L : List Typ), (∀ C ∈ L, C.Closed) → L.map (Typ.shift 0) = L := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons C Cs ih =>
        intro hL
        simp only [List.map_cons]
        rw [Typ.shift_closed (hL C (by simp)), ih (fun C' hC' => hL C' (by simp [hC']))]
  exact h _ hρ.types

/-- Pointwise refinement between environments: same types, and each
entry's relation included in the corresponding one. -/
def LRelSubs.Le (ρ ρ' : LRelSubs) : Prop :=
  ρ.types = ρ'.types ∧
  ∀ (k : Nat) (s s' : LRelOf), ρ[k]? = some s → ρ'[k]? = some s' →
    ∀ ε v, s.rel ε v → s'.rel ε v

lemma LRelSubs.Le.refl (ρ : LRelSubs) : LRelSubs.Le ρ ρ :=
  ⟨rfl, fun k s s' h h' ε v hv => by rw [h] at h'; cases h'; exact hv⟩

lemma LRelSubs.Le.length {ρ ρ'} : LRelSubs.Le ρ ρ' → ρ.length = ρ'.length := by
  intro h
  have := congrArg List.length h.1
  simpa using this

lemma LRelSubs.Le.cons {ρ ρ'} {s s' : LRelOf} :
    LRelSubs.Le ρ ρ' → s.type = s'.type →
    (∀ ε v, s.rel ε v → s'.rel ε v) →
    LRelSubs.Le (s :: ρ) (s' :: ρ') := by
  intro h ht hr
  constructor
  · simp [ht, h.1]
  · intro k u u' hu hu' ε v hv
    cases k with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hu hu'
        subst hu; subst hu'
        exact hr ε v hv
    | succ j =>
        simp only [List.getElem?_cons_succ] at hu hu'
        exact h.2 j u u' hu hu' ε v hv

/-- A semantic-substitution entry is *Kripke* when its relation is
monotone in the runtime environment. -/
def LRelOf.Kripke (s : LRelOf) : Prop := s.rel.Kripke

/-- An environment is *Kripke* when all of its entries are. -/
def LRelSubs.Kripke (ρ : LRelSubs) : Prop := ∀ s ∈ ρ, s.Kripke

@[simp,grind .]
lemma LRelSubs.Kripke.nil : ρ0.Kripke := by
  intro s h
  simp at h
