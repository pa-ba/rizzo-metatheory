import Rizzo.Preservation
import Rizzo.Deterministic
import Rizzo.LogicalRelation.Basic

open Term
open MVal
open Typ
open List

--------------------------------------
-- The value logical relation       --
-- denoted p ∈ V⟦F⟧ρ#ε (open types) --
-- and p ∈ V⟦A⟧ε (closed types)     --
-- (Fig. 10)                        --
--------------------------------------

mutual
  @[simp]
  def VRel (A : Typ) (ρ : LRelSubs) (ε : Env) (v : MVal) : Prop :=
    match A with
    | 𝟭 => v = .unit
    | A1 ⨂ A2 => ∃ v1 v2, v = .pair v1 v2
        /\ VRel A1 ρ ε v1 /\ VRel A2 ρ ε v2
    | .sum A1 A2 => (∃ v1, v = .in1 v1 /\ VRel A1 ρ ε v1)
        \/ (∃ v2, v = .in2 v2 /\ VRel A2 ρ ε v2)
    | A1 ⟶ A2 => ⊢{ε} v ∷ (A1 ⟶ A2).substAll ρ.types /\ ∃ t, v = .lam t /\
        ∀ ε', ε.le ε' → ∀ v1, VRel A1 ρ ε' v1 → TRel A2 ρ ε' (t.sub v1)
    | ◯ B => ⊢{ε} v ∷ ◯ (B.substAll ρ.types)
    | □ B => ⊢{ε} v ∷ □ (B.substAll ρ.types)
    | .sig B => ∃ l , v = .loc l /\ ∃ s : Sig, s ∈ ε.now.lookup l /\
        s.type = B.substAll ρ.types /\ VRel B ρ ε s.head
    | .chan B => ⊢{ε} v ∷ .chan (B.substAll ρ.types)
    | .var i => ∃ s, ρ[i]? = some s /\ ⊢{ε} v ∷ s.type /\ s.rel ε v
    | μ B => LRel.lfp (fun X ε'' w => ∃ (v' : MVal),
        w = MVal.cons (B.substAll (Typ.var 0 :: ρ.types.map (Typ.shift 0))) v' /\
        VRel B (⟨(μ B).substAll ρ.types, X⟩ :: ρ) ε'' v') ε v
  termination_by (sizeOf A, 0)

--------------------------------------
-- The term logical relation        --
-- denoted t ∈ T⟦F⟧ρ#ε (open types) --
-- and t ∈ T⟦A⟧ε (closed types)     --
-- (Fig. 10)                        --
--------------------------------------

  def TRel (A : Typ) (ρ : LRelSubs) (ε : Env) (t : Term) : Prop :=
    ∃ v ε', (t, ε) ⇓ (v, ε') /\ VRel A ρ ε' v
  termination_by (sizeOf A, 1)
end

/-- `vrel` unfolds one layer of the logical relation `VRel`
(i.e. `simp only [VRel]`).  `vrel at h ⊢` targets specific hypotheses
and/or the goal. -/
syntax "vrel" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| vrel $[$loc]?) => `(tactic| simp only [_root_.VRel] $[$loc]?)

/-- The canonical environment entry for the recursive variable of `µ B`
over `ρ`. -/
def LRelOf.mu (B : Typ) (ρ : LRelSubs) : LRelOf :=
  ⟨(μ B).substAll ρ.types, VRel (μ B) ρ⟩

@[simp] lemma LRelOf.mu_type {B ρ} :
    (LRelOf.mu B ρ).type = (μ B).substAll ρ.types := rfl

@[simp] lemma LRelOf.mu_rel {B ρ ε w} :
    (LRelOf.mu B ρ).rel ε w ↔ VRel (μ B) ρ ε w := Iff.rfl

/-- The body operator of the µ-case: one `cons` layer over the body
relation, with the abstract predicate pushed for the recursive
variable. -/
def VRel.muOper (B : Typ) (ρ : LRelSubs) (X : LRel) : LRel :=
  fun ε v => ∃ (v' : MVal),
    v = MVal.cons (B.substAll (Typ.var 0 :: ρ.types.map (Typ.shift 0))) v' ∧
    VRel B (⟨(μ B).substAll ρ.types, X⟩ :: ρ) ε v'

/-- The µ-case of the relation, as a least fixed point of the body
operator. -/
lemma VRel.mu_def {B ρ} :
    VRel (μ B) ρ = LRel.lfp (VRel.muOper B ρ) := by
  funext ε v
  vrel
  rfl

----------------------------
-- The full relation      --
----------------------------

/-- Unfolding of the term relation into an evaluation reaching a value
in the value relation. -/
lemma TRel_def {A ρ ε t} :
    TRel A ρ ε t ↔ ∃ v ε', (t, ε) ⇓ (v, ε') /\ VRel A ρ ε' v := by
  rw [TRel]

----------------------------------
-- The context logical relation --
-- denoted γ ∈ C⟦Γ⟧ε            --
-- (Fig. 10)                    --
----------------------------------

inductive CRel : Ctx → Env → Subs → Prop where
  | nil : CRel [] ε []
  | cons : VRel A ρ0 ε ⟨ v, p ⟩  → CRel Γ ε γ → CRel (A :: Γ) ε (v :: γ)

-- Logical-relation notations (the shapes the fundamental property uses).
notation : 80 v : 90 " ∈ " "V⟦" A : 90 "⟧" ρ : 90 "#" ε : 90 => VRel A ρ ε v
notation : 80 v : 90 " ∈ " "V⟦" A : 90 "⟧" ε : 90 => VRel A ρ0 ε v
notation : 80 t : 90 " ∈ " "T⟦" A : 90 "⟧" ρ : 90 "#" ε : 90 => TRel A ρ ε t
notation : 80 t : 90 " ∈ " "T⟦" A : 90 "⟧" ε : 90 => TRel A ρ0 ε t

notation : 80 γ : 90 " ∈ " "C⟦" Γ : 90 "⟧" ε : 90 => CRel Γ ε γ

/-- Extract the components of a term-relation membership proof. -/
lemma TRel.elim : t ∈ T⟦A⟧ρ#ε → ∃ v ε', (t, ε) ⇓ (v, ε') ∧ v ∈ V⟦A⟧ρ#ε' :=
  fun h => TRel_def.mp h

/-- Construct a term-relation membership proof. -/
lemma TRel.intro : (t, ε) ⇓ (v, ε') → v ∈ V⟦A⟧ρ#ε' → t ∈ T⟦A⟧ρ#ε :=
  fun R V => TRel_def.mpr ⟨v, ε', R, V⟩

lemma TRel.VRel  :  ⟨t, p⟩  ∈ V⟦A⟧ρ#ε → t ∈ T⟦A⟧ρ#ε :=
  fun V => TRel.intro (.value p) V

lemma VRel.IsValue_TRel {v : MVal} : v ∈ T⟦A⟧ρ#ε → v ∈ V⟦A⟧ρ#ε  := by
  intros T
  let ⟨t,p⟩ := v
  rcases T.elim with ⟨t', ε', R, V⟩
  apply Eval.IsValue_rfl p at R
  let ⟨R1,R2⟩ := R
  subst R1 R2
  assumption

lemma TRel.VRel'  :  (∃ p , ⟨t, p⟩  ∈ V⟦A⟧ρ# ε) → t ∈ T⟦A⟧ρ#ε := by
  intros E;  cases E
  apply TRel.VRel <;> assumption
